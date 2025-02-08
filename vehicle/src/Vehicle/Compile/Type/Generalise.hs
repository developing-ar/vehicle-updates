module Vehicle.Compile.Type.Generalise
  ( generaliseOverUnsolvedConstraints,
    generaliseOverUnsolvedMetaVariables,
  )
where

import Control.Monad (foldM, forM)
import Control.Monad.Except (MonadError (..))
import Data.Data (Proxy (..))
import Data.List.NonEmpty (NonEmpty (..), (<|))
import Data.Maybe (fromMaybe)
import Vehicle.Compile.Context.Bound
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Type.Constraint.UnificationSolver
  ( UnificationResult (..),
  )
import Vehicle.Compile.Type.Constraint.UnificationSolver qualified as UnificationSolver
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Meta
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.Monad.Class (getActiveAuxiliaryInstanceConstraints, setAuxiliaryInstanceConstraints)
import Vehicle.Data.Code.Value (Value (..))
import Vehicle.Data.DeBruijn (shiftDBIndex)

--------------------------------------------------------------------------------
-- Type-class generalisation

type MonadGeneralise builtin m =
  ( MonadTypeChecker builtin m,
    MonadSupply Int m
  )

-- Finds any unsolved type class constraints that are blocked on
-- metas that occur in the type of the declaration. It then appends these
-- constraints as instance arguments to the declaration.
generaliseOverUnsolvedConstraints ::
  forall builtin m.
  (MonadGeneralise builtin m) =>
  Decl builtin ->
  m (Decl builtin)
generaliseOverUnsolvedConstraints decl =
  logCompilerPass MidDetail "generalisation over unsolved type-class constraints" $ do
    unsolvedInstanceConstraints <- getActiveInstanceConstraints
    unsolvedAuxiliaryConstraints <- getActiveAuxiliaryInstanceConstraints

    unsolvedConstraints <- traverse substMetas =<< getActiveConstraints
    generalisableConstraints <- traverse substMetas (unsolvedInstanceConstraints <> unsolvedAuxiliaryConstraints)

    (generalisedDecl, rejectedGeneralisableConstraints) <-
      foldM (generaliseOverConstraint unsolvedConstraints) (decl, []) generalisableConstraints

    case rejectedGeneralisableConstraints of
      (c : cs) -> do
        let ungeneralisableConstraints = fmap (mapObject InstanceConstraint) (c :| cs)
        throwError $ TypingError $ UnsolvedConstraints ungeneralisableConstraints
      [] -> do
        setInstanceConstraints @builtin mempty
        setAuxiliaryInstanceConstraints @builtin mempty
        return generalisedDecl

generaliseOverConstraint ::
  (MonadGeneralise builtin m) =>
  [WithContext (Constraint builtin)] ->
  (Decl builtin, [WithContext (InstanceConstraint builtin)]) ->
  WithContext (InstanceConstraint builtin) ->
  m (Decl builtin, [WithContext (InstanceConstraint builtin)])
generaliseOverConstraint allConstraints (decl, rejected) c@(WithContext tc ctx) = do
  -- Find any unsolved meta variables that are transitively linked
  -- by constraints of the same type.
  linkedMetas <- getMetasLinkedToMetasIn allConstraints (typeOf decl)
  -- Only prepend the constraint if all variables in the constraint
  -- are so linked.
  substTC <- substMetas tc
  constraintMetas <- metasIn substTC
  let prependable = constraintMetas `MetaSet.isSubsetOf` linkedMetas
  if not prependable
    then do
      logDebug MaxDetail $ "Found non-prependable type-class constraint" <+> prettyVerbose c
      return (decl, c : rejected)
    else do
      generalisedDecl <- prependConstraint decl (WithContext substTC ctx)
      return (generalisedDecl, rejected)

prependConstraint ::
  (MonadGeneralise builtin m) =>
  Decl builtin ->
  WithContext (InstanceConstraint builtin) ->
  m (Decl builtin)
prependConstraint decl (WithContext (Resolve _origin meta relevance goal) ctx) = do
  let p = originalProvenance ctx
  let typeClass = quote p (contextDBLevel ctx) $ goalExpr goal
  substTypeClass <- substMetas typeClass
  logCompilerPass MaxDetail ("generalisation over" <+> prettyVerbose substTypeClass) $
    prependBinderAndSolveMeta (boundContextOf ctx) meta (BinderDisplayForm OnlyType True) (Instance True) relevance substTypeClass decl

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

    unsolvedMetas <-
      if not (isTypeSynonym declType)
        then -- Quantify over the metas in the type of the declaration.
          metasIn (typeOf decl)
        else -- In a type synonym so quantify over metas in the body.
        -- Needed for the sub-typing systems (e.g. see issue700 test)
          maybe (return mempty) metasIn (bodyOf decl)

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
  metaCtx <- getMetaCtx (Proxy @builtin) meta
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
        let metaExpr = VMeta meta []
        prependBinderAndSolveMeta metaCtx metaExpr binderDisplayForm (Implicit True) Relevant metaType decl

isMeta :: Expr builtin -> Bool
isMeta Meta {} = True
isMeta (App Meta {} _) = True
isMeta _ = False

--------------------------------------------------------------------------------
-- Utilities

prependBinderAndSolveMeta ::
  forall builtin m.
  (MonadTypeChecker builtin m) =>
  BoundCtx (Type builtin) ->
  Value builtin ->
  BinderDisplayForm ->
  Visibility ->
  Relevance ->
  Type builtin ->
  Decl builtin ->
  m (Decl builtin)
prependBinderAndSolveMeta ctx solutionExpr f v r binderType decl = do
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

  metas <- metasIn solutionExpr

  let extendMeta declaration meta = do
        extendBoundCtxOfMeta meta typeBinder
        return $ addNewArgumentToMetaUses meta declaration

  newDecl <- foldM extendMeta prependedDecl (MetaSet.toList metas)

  let solution = VBoundVar (Lv 0) [] :: (Value builtin)
  let newCtx = typeBinder : ctx
  solvingResult <- UnificationSolver.solve newCtx solutionExpr solution
  case solvingResult of
    Success -> return ()
    _ -> developerError "Unexpectedly unable to solve generalisation unification constraint"

  -- Substitute the new meta solution through.
  resultDecl <- substMetas newDecl

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
    metasInBinder <- metasIn binderType
    newMetas <- or <$> forM (MetaSet.toList metasInBinder) (removeMetaDependencies (Proxy @builtin))

    if not newMetas
      then return (binderType, decl)
      else do
        substDecl <- substMetas decl
        substBinderType <- substMetas binderType
        logCompilerPassOutput (prettyExternal substDecl)
        return (substBinderType, substDecl)

addNewArgumentToMetaUses :: MetaID -> Decl builtin -> Decl builtin
addNewArgumentToMetaUses meta = fmap (go (-1))
  where
    go :: Lv -> Expr builtin -> Expr builtin
    go d expr = case expr of
      Meta p m
        | m == meta -> App (Meta p m) [newVar p]
      App (Meta p m) args
        | m == meta -> App (Meta p m) (newVar p <| goArgs args)
      Universe {} -> expr
      Hole {} -> expr
      Meta {} -> expr
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
