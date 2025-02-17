module Vehicle.Compile.Type.Generalise
  ( generaliseOverUnsolvedConstraints,
    generaliseOverUnsolvedMetaVariables,
  )
where

import Control.Monad (filterM, forM_, unless, when)
import Control.Monad.Except (MonadError (..))
import Data.Data (Proxy (..))
import Data.Foldable (foldlM)
import Data.Graph (graphFromEdges, topSort)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (fromMaybe, isJust, isNothing, mapMaybe)
import Data.Text qualified as Text
import Vehicle.Compile.Context.Bound
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.NBE (normaliseInEnv)
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Type.Constraint.InstanceSolver (runInstanceSolver)
import Vehicle.Compile.Type.Constraint.UnificationSolver (runUnificationSolver)
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Meta
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.Monad.Class
import Vehicle.Data.Code.Value

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
  decl1 <- generaliseOverParticularUnsolvedConstraints getActiveInstanceConstraints decl
  logUnsolvedUnknowns (Proxy @builtin)
  generaliseOverParticularUnsolvedConstraints getActiveAuxiliaryInstanceConstraints decl1

-- Finds any unsolved type class constraints that are blocked on
-- metas that occur in the type of the declaration. It then appends these
-- constraints as instance arguments to the declaration.
generaliseOverParticularUnsolvedConstraints ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  m [WithContext (InstanceConstraint builtin)] ->
  Decl builtin ->
  m (Decl builtin)
generaliseOverParticularUnsolvedConstraints getConstraints decl = do
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
          let p = provenanceOf decl
          binders <- traverse (createBinderForConstraint p) (zip [1 ..] generalisableConstraintIDs)
          generalisedDecl <- logCompilerPass MaxDetail ("generalisation over" <+> pretty generalisableConstraintIDs) $ do
            prependTelescopeAndSolve binders decl
          logUnsolvedUnknowns (Proxy @builtin)
          runInstanceSolver (Proxy @builtin) 0
          runUnificationSolver (Proxy @builtin) False
          return generalisedDecl

findGeneralisableConstraints ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  NonEmpty (WithContext (InstanceConstraint builtin)) ->
  Decl builtin ->
  m [ConstraintID]
findGeneralisableConstraints constraintsToGeneralise decl = do
  instanceConstraints <- getActiveInstanceConstraints
  auxInstanceConstraints <- getActiveAuxiliaryInstanceConstraints
  unsolvedInstanceConstraints <- substMetas (instanceConstraints <> auxInstanceConstraints)
  let unsolvedConstraints = fmap (mapObject InstanceConstraint) unsolvedInstanceConstraints

  -- Find any unsolved meta variables that are transitively linked
  -- by constraints of the same type.
  linkedMetas <- getMetasLinkedToMetasIn unsolvedConstraints (typeOf decl)
  metaCtx <- getMetaVariableCtx @builtin

  -- The function that determines if we can generalise a constraint or not.
  let isGeneralisable (con@(WithContext constraint _ctx), constraintMetas) = do
        -- Only prepend the constraint if all variables in the constraint
        -- are so linked.
        let solutionMeta = instanceSolution constraint
        let allConstraintMetas = MetaSet.insert solutionMeta constraintMetas
        let metasAppearInType = not (allConstraintMetas `MetaSet.disjoint` linkedMetas)

        -- Don't generalise constraints whose solution meta has already been solved. These should
        -- get solved when the prior solution is prepended as a generalisable constraint.
        let notAlreadySolved = isNothing $ metaSolution (findMetaInfo metaCtx solutionMeta)
        logDebug MaxDetail $ pretty notAlreadySolved <+> pretty metasAppearInType <+> prettyVerbose con
        return $ metasAppearInType && notAlreadySolved

  let unsolvedConstraintsAndMetas = (\c -> (c, metasIn $ objectIn c)) <$> NonEmpty.toList constraintsToGeneralise
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
  let sortedConstraintIDs = fmap ((\(c, _, _) -> c) . nodeFromVertex) sortedVertices

  logDebug MaxDetail $ "Sorted order:" <+> pretty sortedConstraintIDs
  return sortedConstraintIDs

createBinderForConstraint ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  Provenance ->
  (Int, ConstraintID) ->
  m (MetaID, Binder builtin)
createBinderForConstraint declProv (index, constraintID) = do
  WithContext constraint ctx <- removeInstanceConstraint (Proxy @builtin) constraintID
  let metaSolution = instanceSolution constraint
  let relevance = instanceRelevance constraint
  let p = originalProvenance ctx
  let lv = contextDBLevel ctx
  let typeClass = quote p lv $ goalExpr (instanceGoal constraint)
  substTypeClass <- substMetasAt lv typeClass
  let binderForm = BinderDisplayForm (NameAndType ("_t" <> Text.pack (show index))) True
  let binder = Binder declProv binderForm (Instance True) relevance substTypeClass
  return (metaSolution, binder)

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
    substDecl <- substMetas decl
    let declType = typeOf substDecl

    let unsolvedMetas =
          MetaSet.toList $
            if not (isTypeSynonym declType)
              then -- Quantify over the metas in the type of the declaration.
                metasIn (typeOf substDecl)
              else -- In a type synonym so quantify over metas in the body.
              -- Needed for the sub-typing systems (e.g. see issue700 test)
                maybe mempty metasIn (bodyOf substDecl)

    -- Quantify over any unsolved type-level meta variables
    if null unsolvedMetas
      then return substDecl
      else do
        let p = provenanceOf substDecl
        metaAndBinderTelescope <- traverse (getBinderForMeta p) unsolvedMetas
        result <- logCompilerPass MidDetail ("generalisation over" <+> pretty unsolvedMetas) $ do
          prependTelescopeAndSolve metaAndBinderTelescope substDecl

        substMetas result

getBinderForMeta :: forall builtin m. (MonadGeneralise builtin m) => Provenance -> MetaID -> m (MetaID, Binder builtin)
getBinderForMeta p meta = do
  metaType <- getSubstMetaType meta
  when (isMeta metaType) $
    compilerDeveloperError
      "When type of unsolved meta is also an unsolved meta need to implement topological sort."

  -- Prepend the implicit binders for the new generalised variable.
  binderName <- freshName <$> demand
  let binderDisplayForm = BinderDisplayForm (OnlyName binderName) True
  let binder = Binder p binderDisplayForm (Implicit True) Relevant metaType
  return (meta, binder)

isMeta :: Expr builtin -> Bool
isMeta Meta {} = True
isMeta (App Meta {} _) = True
isMeta _ = False

--------------------------------------------------------------------------------
-- Utilities

prependTelescopeAndSolve ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  [(MetaID, Binder builtin)] ->
  Decl builtin ->
  m (Decl builtin)
prependTelescopeAndSolve telescope decl = do
  let p = provenanceOf decl

  -- Create a new meta with dependencies on the telescope and solve the previous one in terms of it.
  let instantiateNewMeta result (meta, binder) = do
        logCompilerPass MaxDetail ("solving" <+> pretty meta) $ do
          metaInfo <- getMetaInfo meta
          let solutionCtx = binder : fmap snd result
          newMeta <- solveInTermsOfNewMetaWithDependencies meta metaInfo solutionCtx
          let solution = BoundVar p 0
          solveMeta newMeta solution solutionCtx
          return ((newMeta, binder) : result)

  newTelescope <-
    logCompilerPass MaxDetail ("solving telescope metas" <+> pretty (fmap fst telescope)) $
      foldlM instantiateNewMeta mempty telescope

  -- Then we prepend the binders to the decl making sure we update the meta-variable state appropiately.
  updatedDecl <- addTelescopeForNewVariables newTelescope decl

  -- Substitute the new meta solution through.
  resultDecl <- substMetas updatedDecl
  setCurrentDecl $ Just resultDecl

  logCompilerPassOutput $ prettyExternal resultDecl
  return resultDecl

-- This function attempts to add the new variable representing the appended meta to all the
-- uses of that meta variable. Really we should add variables to all variables everywhere
-- but this function tries to get away with just adding it to the minimum necessary places.
-- This may need to change in future...
addTelescopeForNewVariables ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  [(MetaID, Binder builtin)] ->
  Decl builtin ->
  m (Decl builtin)
addTelescopeForNewVariables metaAndBinderTelescope decl = do
  -- All the metas contained within the type of the binder about to be
  -- appended cannot have any dependencies on variables later on in the expression.
  logCompilerPass MaxDetail "adjusting dependencies for unsolved metas" $ do
    let metasInTelescope = MetaSet.fromList $ fmap fst metaAndBinderTelescope
    let metaBinderContainingMetas = fmap (\(_m, b) -> (b, metasIn b)) metaAndBinderTelescope
    unsolvedMetas <- getUnsolvedMetas (Proxy @builtin)
    let remainingUnsolvedMetas = MetaSet.toList $ MetaSet.difference unsolvedMetas metasInTelescope
    forM_ remainingUnsolvedMetas $
      alterMetaDependencies (reverse metaBinderContainingMetas)

  -- Compute the telescopes
  let typeTelescope = fmap snd metaAndBinderTelescope
  let bodyTelescope = fmap (mapBinderNamingForm (\t -> OnlyName (fromMaybe "_" (nameOf t)))) typeTelescope

  -- Next update the constraints
  instanceConstraints <- getActiveInstanceConstraints
  setInstanceConstraints =<< traverse (updateInstanceConstraint typeTelescope) instanceConstraints

  auxInstanceConstraints <- getActiveAuxiliaryInstanceConstraints
  setAuxiliaryInstanceConstraints =<< traverse (updateInstanceConstraint typeTelescope) auxInstanceConstraints

  -- Then finally update the declaration
  let p = provenanceOf decl
  let alterType t = return $ foldr (Pi p) t (reverse typeTelescope)
  let alterBody e = return $ foldr (Lam p) e (reverse bodyTelescope)

  traverseDeclTypeAndExpr alterType alterBody decl

updateInstanceConstraint ::
  forall builtin m.
  (MonadTypeChecker builtin m) =>
  Telescope builtin ->
  WithContext (InstanceConstraint builtin) ->
  m (WithContext (InstanceConstraint builtin))
updateInstanceConstraint telescope (WithContext Resolve {..} ctx) = do
  -- First update the context
  let newCtx = updateConstraintBoundCtx ctx (telescope <>)
  let InstanceGoal {..} = instanceGoal
  unless (null goalTelescope) $
    developerError "Extending instance constraints with telescopes not yet supported"

  newGoalSpine <- flip traverseSpine goalSpine $ \arg -> do
    let lv = boundCtxLv $ boundContext ctx
    let unnormArg = quote mempty lv arg
    normaliseInEnv (boundContextToEnv $ boundContext newCtx) unnormArg

  solutionMetaInfo <- getMetaInfo @builtin instanceSolution
  let newInstanceSolution = case metaSolution solutionMetaInfo of
        Just (normalised -> VMeta v _) -> v
        _ -> instanceSolution

  let newGoal = InstanceGoal {goalSpine = newGoalSpine, ..}
  let newConstraint = Resolve {instanceSolution = newInstanceSolution, instanceGoal = newGoal, ..}

  return $ WithContext newConstraint newCtx

-- | Alter the dependencies of a meta to either add the new binder or clear the context.
alterMetaDependencies ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  [(Binder builtin, MetaSet)] ->
  MetaID ->
  m ()
alterMetaDependencies telescope meta =
  logCompilerSection MaxDetail ("considering" <+> pretty meta) $ do
    metaInfo@(MetaInfo _ _ ctx solution) <- getMetaInfo @builtin meta
    maybeNewCtx <-
      if isJust solution
        then do
          logDebug MaxDetail "leaving unchanged"
          return Nothing
        else do
          getNewContextForUnsolvedMetaVariable meta ctx mempty telescope

    forM_ maybeNewCtx $ \newCtx -> do
      solveInTermsOfNewMetaWithDependencies meta metaInfo newCtx

getNewContextForUnsolvedMetaVariable ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  MetaID ->
  BoundCtx (Type builtin) ->
  Telescope builtin ->
  [(Binder builtin, MetaSet)] ->
  m (Maybe (BoundCtx (Type builtin)))
getNewContextForUnsolvedMetaVariable meta originalCtx telescope = \case
  (binder, metasInBinder) : cs
    | MetaSet.member meta metasInBinder -> do
        if null originalCtx
          then do
            logDebug MaxDetail "leaving unchanged"
            return Nothing
          else do
            logDebug MaxDetail $ "truncating context to" <+> prettyCtx telescope <+> "as in the type of" <+> prettyVerbose binder
            return $ Just telescope
    | otherwise -> getNewContextForUnsolvedMetaVariable meta originalCtx (binder : telescope) cs
  [] -> do
    logDebug MaxDetail ("changing context from" <+> prettyCtx originalCtx <+> "to" <+> prettyCtx telescope)
    return $ Just telescope
  where
    prettyCtx = prettyVerbose

solveInTermsOfNewMetaWithDependencies ::
  (MonadTypeChecker builtin m) =>
  MetaID ->
  MetaInfo builtin ->
  BoundCtx (Type builtin) ->
  m MetaID
solveInTermsOfNewMetaWithDependencies meta (MetaInfo p t _ _) newCtx = do
  (newMeta, newMetaExpr) <- freshMeta p t newCtx
  solveMeta meta newMetaExpr newCtx
  return newMeta
