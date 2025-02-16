module Vehicle.Compile.Type.Generalise
  ( generaliseOverUnsolvedConstraints,
    generaliseOverUnsolvedMetaVariables,
  )
where

import Control.Monad (filterM, foldM, forM)
import Control.Monad.Except (MonadError (..))
import Data.Data (Proxy (..))
import Data.Graph (graphFromEdges, topSort)
import Data.List.NonEmpty (NonEmpty (..), (<|))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromMaybe, isNothing, mapMaybe)
import Data.Text qualified as Text
import Vehicle.Compile.Context.Bound
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Type.Constraint.InstanceSolver (runInstanceSolver)
import Vehicle.Compile.Type.Constraint.UnificationSolver (runUnificationSolver)
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Meta
import Vehicle.Compile.Type.Meta.Map qualified as MetaMap
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.Monad.Class
import Vehicle.Data.Code.Value
import Vehicle.Data.DeBruijn (shiftDBIndex)

--------------------------------------------------------------------------------
-- Type-class generalisation

type MonadGeneralise builtin m =
  ( MonadTypeChecker builtin m,
    MonadSupply Int m
  )

generaliseOverUnsolvedConstraints ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  Decl builtin ->
  m (Decl builtin)
generaliseOverUnsolvedConstraints decl = do
  decl1 <- generaliseOverParticularUnsolvedConstraints getActiveInstanceConstraints setInstanceConstraints decl
  generaliseOverParticularUnsolvedConstraints getActiveAuxiliaryInstanceConstraints setAuxiliaryInstanceConstraints decl1

-- Finds any unsolved type class constraints that are blocked on
-- metas that occur in the type of the declaration. It then appends these
-- constraints as instance arguments to the declaration.
generaliseOverParticularUnsolvedConstraints ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  m [WithContext (InstanceConstraint builtin)] ->
  ([WithContext (InstanceConstraint builtin)] -> m ()) ->
  Decl builtin ->
  m (Decl builtin)
generaliseOverParticularUnsolvedConstraints getConstraints setConstraints decl = do
  unsolvedInstanceConstraints <- getConstraints
  case unsolvedInstanceConstraints of
    [] -> return decl
    (c : cs) -> do
      generalisableConstraintIDs <-
        logCompilerPass MaxDetail "finding generalisable constraints" $ do
          findGeneralisableConstraints (c :| cs) decl
      case generalisableConstraintIDs of
        [] -> do
          let ungeneralisableConstraints = fmap (mapObject InstanceConstraint) (c :| cs)
          throwError $ TypingError $ UnsolvedConstraints ungeneralisableConstraints
        _ -> do
          generalisedDecl <- foldM prependConstraint decl (zip [1 ..] generalisableConstraintIDs)
          logUnsolvedUnknowns (Proxy @builtin)
          runInstanceSolver (Proxy @builtin) 0
          runUnificationSolver (Proxy @builtin) False
          generaliseOverParticularUnsolvedConstraints getConstraints setConstraints generalisedDecl

findGeneralisableConstraints ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  NonEmpty (WithContext (InstanceConstraint builtin)) ->
  Decl builtin ->
  m [ConstraintID]
findGeneralisableConstraints allInstanceConstraints decl = do
  unsolvedConstraints <- traverse substMetas =<< getActiveConstraints
  let unsolvedConstraintsAndMetas = (\c -> (c, metasIn $ objectIn c)) <$> NonEmpty.toList allInstanceConstraints

  -- Find any unsolved meta variables that are transitively linked
  -- by constraints of the same type.
  linkedMetas <- getMetasLinkedToMetasIn unsolvedConstraints (typeOf decl)
  metaSubst <- getMetaSubstitution (Proxy @builtin)

  -- The function that determines if we can generalise a constraint or not.
  let isGeneralisable (con@(WithContext constraint _ctx), constraintMetas) = do
        -- Only prepend the constraint if all variables in the constraint
        -- are so linked.
        let allConstraintMetas = MetaSet.insert (instanceSolution constraint) constraintMetas
        let metasAppearInType = not (allConstraintMetas `MetaSet.disjoint` linkedMetas)

        -- Don't generalise constraints whose solution meta has already been solved. These should
        -- get solved when the prior solution is prepended as a generalisable constraint.
        let notAlreadySolved = isNothing (MetaMap.lookup (instanceSolution constraint) metaSubst)
        logDebug MaxDetail $ pretty notAlreadySolved <+> pretty metasAppearInType <+> prettyVerbose con
        return $ metasAppearInType && notAlreadySolved

  generalisable <- filterM isGeneralisable unsolvedConstraintsAndMetas

  -- We need to sort topologically sort the generalisable constraints so that they
  -- are introduced in the right order if there are dependencies between them.
  let getKey constraint = instanceSolution $ objectIn constraint
  let adjacencyList = flip fmap generalisable $ \(c, _) -> do
        let key = getKey c
        let isRelatedKey (c', metas)
              | MetaSet.member key metas = Just $ getKey c'
              | otherwise = Nothing

        let linkedConstraints = mapMaybe isRelatedKey generalisable
        (constraintID $ contextOf c, key, linkedConstraints)

  let (graph, nodeFromVertex, _vertexFromIdent) = graphFromEdges adjacencyList
  let sortedVertices = topSort graph
  let sortedConstraintIDs = reverse $ fmap ((\(c, _, _) -> c) . nodeFromVertex) sortedVertices

  logDebug MaxDetail $ "Sorted order:" <+> pretty sortedConstraintIDs
  return sortedConstraintIDs

prependConstraint ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  Decl builtin ->
  (Int, ConstraintID) ->
  m (Decl builtin)
prependConstraint decl (index, constraintID) = do
  constraintInCtx@(WithContext constraint ctx) <- removeInstanceConstraint (Proxy @builtin) constraintID
  logCompilerPass MaxDetail ("generalisation over" <+> prettyVerbose constraintInCtx) $ do
    let metaSolution = instanceSolution constraint
    let relevance = instanceRelevance constraint
    let p = originalProvenance ctx
    let typeClass = quote p (contextDBLevel ctx) $ goalExpr (instanceGoal constraint)
    substTypeClass <- substMetas typeClass
    let binderForm = BinderDisplayForm (NameAndType ("_t" <> Text.pack (show index))) True
    prependBinderAndSolveMeta metaSolution binderForm (Instance True) relevance substTypeClass decl

--------------------------------------------------------------------------------
-- Unsolved meta generalisation

-- | Finds any unsolved metas that occur in the type of the declaration. For
-- each such meta, it then prepends a new quantified variable to the declaration
-- type and then solves the meta as that new variable.
generaliseOverUnsolvedMetaVariables ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  Decl builtin ->
  m (Decl builtin)
generaliseOverUnsolvedMetaVariables decl =
  logCompilerPass MidDetail "generalisation of unsolved metas in declaration type" $ do
    let declType = typeOf decl

    let unsolvedMetas =
          if not (isTypeSynonym declType)
            then -- Quantify over the metas in the type of the declaration.
              metasIn (typeOf decl)
            else -- In a type synonym so quantify over metas in the body.
            -- Needed for the sub-typing systems (e.g. see issue700 test)
              maybe mempty metasIn (bodyOf decl)

    -- Quantify over any unsolved type-level meta variables
    if MetaSet.null unsolvedMetas
      then return decl
      else do
        result <- foldM quantifyOverMeta decl (MetaSet.toList unsolvedMetas)
        substMetas result

quantifyOverMeta ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  Decl builtin ->
  MetaID ->
  m (Decl builtin)
quantifyOverMeta decl meta = do
  metaType <- substMetas =<< getMetaType meta
  if isMeta metaType
    then
      compilerDeveloperError $
        "Haven't thought about what to do when type of unsolved meta is also"
          <+> "an unsolved meta."
    else do
      metaDoc <- prettyMeta (Proxy @builtin) meta
      logCompilerPass MidDetail ("generalisation over" <+> metaDoc) $ do
        -- Prepend the implicit binders for the new generalised variable.
        binderName <- freshName <$> demand
        let binderDisplayForm = BinderDisplayForm (OnlyName binderName) True
        prependBinderAndSolveMeta meta binderDisplayForm (Implicit True) Relevant metaType decl

isMeta :: Expr builtin -> Bool
isMeta Meta {} = True
isMeta (App Meta {} _) = True
isMeta _ = False

--------------------------------------------------------------------------------
-- Utilities

prependBinderAndSolveMeta ::
  forall builtin m.
  (MonadTypeChecker builtin m) =>
  MetaID ->
  BinderDisplayForm ->
  Visibility ->
  Relevance ->
  Type builtin ->
  Decl builtin ->
  m (Decl builtin)
prependBinderAndSolveMeta meta f v r binderType decl = do
  -- All the metas contained within the type of the binder about to be
  -- appended cannot have any dependencies on variables later on in the expression.
  -- So the replace them with meta-variables with empty contexts.
  (substBinderType, substDecl) <- removeContextsOfMetasIn binderType decl

  -- Construct the new binder and prepend it to both the type and
  -- (if applicable) the body of the declaration.
  let typeBinder = Binder (provenanceOf decl) f v r substBinderType
  let bodyBinderForm = BinderDisplayForm (OnlyName (fromMaybe "_" (nameOf f))) True
  let bodyBinder = Binder (provenanceOf decl) bodyBinderForm v r substBinderType
  prependedDecl <- case substDecl of
    DefAbstract p rt ident t ->
      return $ DefAbstract p rt ident (Pi p typeBinder t)
    DefFunction p ident anns t e ->
      return $ DefFunction p ident anns (Pi p typeBinder t) (Lam p bodyBinder e)

  -- Then we add i) the new binder to the context of the meta-variable being
  -- solved, and ii) a new argument to all uses of the meta-variable so
  -- that meta-subsitution will work later.
  extendBoundContextOfMeta meta typeBinder
  extendBoundContextOfConstraints typeBinder
  updatedDecl <- addNewArgumentToMetaUses meta prependedDecl

  -- We now solve the meta as the newly bound variable
  metaCtx <- getMetaCtx (Proxy @builtin) meta
  let p = provenanceOf prependedDecl
  let solution = BoundVar p (Ix $ length metaCtx - 1)
  solveMeta meta solution metaCtx

  -- Substitute the new meta solution through.
  resultDecl <- substMetas updatedDecl
  setCurrentDecl $ Just resultDecl

  logCompilerPassOutput $ prettyExternal resultDecl
  return resultDecl

removeContextsOfMetasIn ::
  forall builtin m.
  (MonadTypeChecker builtin m) =>
  Type builtin ->
  Decl builtin ->
  m (Type builtin, Decl builtin)
removeContextsOfMetasIn binderType decl =
  logCompilerPass MaxDetail "removing dependencies from dependent metas" $ do
    let metasInBinder = metasIn binderType
    newMetas <- or <$> forM (MetaSet.toList metasInBinder) (removeMetaDependencies (Proxy @builtin))

    if not newMetas
      then return (binderType, decl)
      else do
        substDecl <- substMetas decl
        substBinderType <- substMetas binderType
        logCompilerPassOutput (prettyExternal substDecl)
        return (substBinderType, substDecl)

-- This function attempts to add the new variable representing the appended meta to all the
-- uses of that meta variable. Really we should add variables to all variables everywhere
-- but this function tries to get away with just adding it to the minimum necessary places.
-- This may need to change in future...
addNewArgumentToMetaUses :: forall builtin m. (MonadTypeChecker builtin m) => MetaID -> Decl builtin -> m (Decl builtin)
addNewArgumentToMetaUses meta decl = do
  modifyTypeCheckerState $ \TypeCheckerState {..} -> do
    let metaLv = Ix $ length $ metaCtx $ findMetaInfo metaInfo meta
    let newSubst = fmap (goMetaSolution metaLv) currentSubstitution
    TypeCheckerState
      { currentSubstitution = newSubst,
        ..
      }
  return $ fmap (go (-1)) decl
  where
    goMetaSolution :: Ix -> GluedExpr builtin -> GluedExpr builtin
    goMetaSolution ix expr = case normalised expr of
      VMeta m [] | m == meta -> do
        let p = provenanceOf expr
        let e = normAppList (Meta p meta) [explicit $ BoundVar p ix]
        let ne = VMeta meta [explicit $ VBoundVar 0 []]
        Glued e ne
      _ -> expr

    go :: Lv -> Expr builtin -> Expr builtin
    go d expr = case expr of
      Meta p m
        | m == meta -> App (Meta p m) [newVar p]
        | otherwise -> expr
      App (Meta p m) args
        | m == meta -> App (Meta p m) (newVar p <| goArgs args)
      Universe {} -> expr
      Hole {} -> expr
      Builtin {} -> expr
      FreeVar {} -> expr
      BoundVar {} -> expr
      App fun args -> App (go d fun) (goArgs args)
      Pi p binder result -> Pi p (goBinder binder) (go (d + 1) result)
      Let p bound binder body -> Let p (go d bound) (goBinder binder) (go (d + 1) body)
      Lam p binder body -> Lam p (goBinder binder) (go (d + 1) body)
      where
        newVar p = Arg p Explicit Relevant (BoundVar p $ shiftDBIndex 0 d)
        goBinder = fmap (go d)
        goArgs = fmap (fmap (go d))
