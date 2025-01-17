module Vehicle.Backend.Queries.UserVariableElimination
  ( eliminateUserVariables,
    UserVariableReconstruction,
    UserVariableReconstructionStep (..),
  )
where

-- Needed as Applicative is exported by Prelude in GHC 9.6 and above.
import Control.Applicative (Applicative (..))
import Control.Monad (forM)
import Control.Monad.Except (MonadError (..))
import Control.Monad.Reader (MonadReader (..), asks)
import Control.Monad.State (MonadState (..), evalStateT)
import Control.Monad.Writer (MonadWriter (..), WriterT (..))
import Data.LinkedHashMap qualified as LinkedHashMap
import Data.Map qualified as Map
import Vehicle.Backend.Queries.PostProcessing (convertPartitionsToQueries)
import Vehicle.Backend.Queries.Unblock (UnblockingActions (..))
import Vehicle.Backend.Queries.Unblock qualified as Unblocking
import Vehicle.Backend.Queries.UserVariableElimination.Core
import Vehicle.Backend.Queries.UserVariableElimination.EliminateExists (solveExists)
import Vehicle.Compile.Boolean.LiftIf (unfoldIf)
import Vehicle.Compile.Boolean.LowerNot (lowerNot, notClosure)
import Vehicle.Compile.Context.Name (getNameContext, runFreshNameContextT)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Builtin (EvalSimple, evalAt, evalCompareRatTensor, evalStackTensor)
import Vehicle.Compile.Normalise.NBE
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly, prettyFriendlyEmptyCtx, prettyVerbose)
import Vehicle.Compile.Rational.LinearExpr (LinearityError (..), compileLinearRelation)
import Vehicle.Compile.Resource (NetworkTensorType (..), NetworkType (..))
import Vehicle.Compile.Variable (createUserVar)
import Vehicle.Data.Assertion
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.BooleanExpr
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.LinearExpr
import Vehicle.Data.Code.TypedView
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (RatTensor, Tensor, pattern ZeroDimTensor)
import Vehicle.Verify.Core (NetworkContextInfo (..), QuerySetNegationStatus)
import Vehicle.Verify.QueryFormat (QueryFormat (..), supportsStrictInequalities)
import Vehicle.Verify.Specification
import Prelude hiding (Applicative (..))

--------------------------------------------------------------------------------
-- Algorithm

-- | Compiles the top-level structure of a property until it hits the first quantifier.
-- Assumptions - expression is well-typed in the empty context and of type Bool.
eliminateUserVariables ::
  forall m.
  (MonadPropertyStructure m, MonadSupply QueryID m, MonadStdIO m) =>
  Value Builtin ->
  m (Property QueryMetaData)
eliminateUserVariables expr = case toBoolValue expr of
  ----------------
  -- Base cases --
  ----------------
  VBoolTensorLiteral b -> compileTrivial b
  VQuantifyRatTensor Exists dims binder closure -> compileQuantifiedQuerySet False dims binder closure
  VQuantifyRatTensor Forall dims binder closure -> do
    let negatedClosure = notClosure 0 dims closure
    compileQuantifiedQuerySet True dims binder negatedClosure
  ---------------------
  -- Recursive cases --
  ---------------------
  VAnd (TensorOp2Args _dims e1 e2) -> andTrivial andBoolExpr <$> eliminateUserVariables e1 <*> eliminateUserVariables e2
  VOr (TensorOp2Args _dims e1 e2) -> orTrivial orBoolExpr <$> eliminateUserVariables e1 <*> eliminateUserVariables e2
  VBoolIf args -> eliminateUserVariables =<< unfoldIf args
  -------------------------
  -- Blocked expressions --
  -------------------------
  VReduceAndTensor {} -> eliminateUserVariables =<< unblock expr
  VReduceOrTensor {} -> eliminateUserVariables =<< unblock expr
  VBoolAt {} -> eliminateUserVariables =<< unblock expr
  VBoolStackTensor {} -> eliminateUserVariables =<< unblock expr
  VConstBoolTensor {} -> eliminateUserVariables =<< unblock expr
  VBoolForeach {} -> eliminateUserVariables =<< unblock expr
  VCompareIndex {} -> eliminateUserVariables =<< unblock expr
  VCompareNat {} -> eliminateUserVariables =<< unblock expr
  VNot {} -> eliminateUserVariables =<< lowerNot 0 unblock expr
  -----------------
  -- Mixed cases --
  -----------------
  -- We can only fail to unblock these cases because we can't evaluate networks
  -- applied to constant arguments or because of if statements.
  --
  -- (if (forall x . f x > 0) then x else 0) > 0
  --
  -- When we have the ability to evaluate networks then this case can be turned to a
  -- call to purify.
  VCompareRatTensor {} -> compileUnquantifiedQuerySet expr
  where
    unblock e = runFreshNameContextT (Unblocking.unblockBoolExpr e)

compileTrivial ::
  (MonadPropertyStructure m) =>
  Tensor Bool ->
  m (MaybeTrivial a)
compileTrivial bs = case bs of
  ZeroDimTensor b -> return $ Trivial b
  _ -> developerError "Should not be compiling tensors of booleans"

compileQuantifiedQuerySet ::
  (MonadPropertyStructure m, MonadSupply QueryID m, MonadStdIO m) =>
  Bool ->
  VArg Builtin ->
  VBinder Builtin ->
  Closure Builtin ->
  m (Property QueryMetaData)
compileQuantifiedQuerySet isPropertyNegated dims binder closure = do
  let subsectionDoc = do
        let expr = fromBoolValue $ VQuantifyRatTensor Exists dims binder closure
        "compilation of set of quantified queries:" <+> prettyFriendlyEmptyCtx expr
  logCompilerPass MaxDetail subsectionDoc $ do
    flip evalStateT emptyGlobalCtx $ do
      maybePartitions <- eliminateExists binder closure
      compileQuerySetPartitions isPropertyNegated maybePartitions

-- | We only need this because we can't evaluate networks in the compiler.
compileUnquantifiedQuerySet ::
  (MonadPropertyStructure m, MonadSupply QueryID m, MonadStdIO m) =>
  Value Builtin ->
  m (Property QueryMetaData)
compileUnquantifiedQuerySet value = do
  let subsectionDoc = "compilation of set of unquantified queries:" <+> prettyFriendlyEmptyCtx value
  logCompilerPass MaxDetail subsectionDoc $ do
    flip evalStateT emptyGlobalCtx $ do
      (maybePartitions, equalities) <- runWriterT $ compileBoolExpr value
      networkEqPartitions <- networkEqualitiesToPartition equalities
      let allPartitions = andTrivial andPartitions maybePartitions networkEqPartitions
      compileQuerySetPartitions False allPartitions

compileQuerySetPartitions ::
  (MonadQueryStructure m, MonadSupply QueryID m, MonadStdIO m) =>
  QuerySetNegationStatus ->
  MaybeTrivial Partitions ->
  m (Property QueryMetaData)
compileQuerySetPartitions isPropertyNegated maybePartitions = case maybePartitions of
  Trivial b -> return $ Trivial (b `xor` isPropertyNegated)
  NonTrivial partitions -> do
    queries <- convertPartitionsToQueries partitions
    return $ NonTrivial $ Query $ QuerySet isPropertyNegated queries

-- | Attempts to compile an arbitrary expression of type `Bool` down to a tree
-- of assertions implicitly existentially quantified by a set of network
-- input/output variables.
compileBoolExpr ::
  (MonadQueryStructure m, MonadWriter [Value Builtin] m) =>
  Value Builtin ->
  m (MaybeTrivial Partitions)
compileBoolExpr expr = case toBoolValue expr of
  ----------------
  -- Base cases --
  ----------------
  VBoolTensorLiteral bs -> compileTrivial bs
  VCompareRatTensor (op, args) -> purifyAndCompileAssertion op args
  VQuantifyRatTensor Forall _ _ _ -> throwError catchableUnsupportedAlternatingQuantifiersError
  ---------------------
  -- Recursive cases --
  ---------------------
  VNot (TensorOp1Args _ e) -> do
    lv <- boundCtxLv <$> getGlobalNamedBoundCtx
    compileBoolExpr =<< lowerNot lv Unblocking.unblockBoolExpr e
  VBoolIf args -> compileBoolExpr =<< unfoldIf args
  VAnd (TensorOp2Args _dims x y) -> andTrivial andPartitions <$> compileBoolExpr x <*> compileBoolExpr y
  VOr (TensorOp2Args _dims x y) -> orTrivial orPartitions <$> compileBoolExpr x <*> compileBoolExpr y
  VQuantifyRatTensor Exists _ binder closure -> eliminateExists binder closure
  _ -> compileBoolExpr =<< Unblocking.unblockBoolExpr expr

purifyAndCompileAssertion ::
  (MonadQuantifierBody m) =>
  ComparisonOp ->
  TensorOp2Args (Value Builtin) ->
  m (MaybeTrivial Partitions)
purifyAndCompileAssertion op args = case op of
  Ne -> compileBoolExpr =<< eliminateNotEqualRatTensor args
  _ -> do
    result <- Unblocking.tryPurifyAssertion unblockingActions op args
    case toBoolValue result of
      VCompareRatTensor (op', args') -> do
        logDebug MaxDetail "Pure assertion found"
        compileAssertion (comparisonToAssertion op) (evalCompareRatTensor op') args'
      _ -> do
        logDebug MaxDetail "Impure assertion found"
        compileBoolExpr result

--------------------------------------------------------------------------------
-- Unblocking

type MonadQuantifierBody m =
  ( MonadQueryStructure m,
    MonadWriter [Value Builtin] m
  )

unblockingActions :: (MonadQuantifierBody m) => UnblockingActions m
unblockingActions = UnblockingActions unblockQuantifiedBoundVar unblockNetworkApplication

unblockQuantifiedBoundVar ::
  (MonadQuantifierBody m) =>
  Lv ->
  m (Value Builtin)
unblockQuantifiedBoundVar lv = do
  maybeReduction <- getReducedVariableExprFor lv
  case maybeReduction of
    Just vectorReduction -> return vectorReduction
    Nothing -> return $ VBoundVar lv []

unblockNetworkApplication ::
  (MonadQuantifierBody m) =>
  NetworkApplication ->
  m (Value Builtin)
unblockNetworkApplication networkApp@(networkName, NetworkAppArgs arg) = do
  globalCtx <- get
  networkContext <- asks networkCtx

  networkInfo <- case Map.lookup networkName networkContext of
    Nothing -> compilerDeveloperError $ "Expecting" <+> quotePretty networkName <+> "to be a @network"
    Just info -> return info

  case LinkedHashMap.lookup networkApp (networkApplications globalCtx) of
    Just existingAppInfo ->
      return $ outputVarExpr existingAppInfo
    Nothing -> do
      (inputVarExpr, outputVarExpr, newGlobalCtx) <- addNetworkApplicationToGlobalCtx networkApp networkInfo globalCtx
      let inputDims = dimensions (inputTensor (networkType networkInfo))
      let inputDimsExpr = implicitIrrelevant $ mkDims inputDims
      let inputEquality = fromBoolValue $ VCompareRatTensor (Eq, TensorOp2Args inputDimsExpr inputVarExpr arg)
      put newGlobalCtx
      tell [inputEquality]
      return outputVarExpr

compileAssertion ::
  (MonadQuantifierBody m) =>
  (LinearExpr RatTensor -> LinearExpr RatTensor -> Assertion) ->
  EvalSimple TensorOp2Args Builtin m ->
  TensorOp2Args (Value Builtin) ->
  m (MaybeTrivial Partitions)
compileAssertion mkAssertion evalRel args@(TensorOp2Args _ xs ys) = do
  result <- compileLinearRelation getTensorVariableShape xs ys
  case result of
    Right (e1, e2) -> return $ mkTrivialPartition (mkAssertion e1 e2)
    Left NonLinearity -> throwError catchableUnsupportedNonLinearConstraint
    Left (UnexpectedExpr e) ->
      developerError ("unexpected expression" <+> prettyVerbose e)
    Left (UnreducedExpr e) -> do
      ctx <- getNameContext
      logDebug MaxDetail $ "Eliminating tensor assertion as unreduced expression found:" <+> prettyFriendly (WithContext e ctx)
      compileBoolExpr =<< eliminateTensorAssertion evalRel args

--------------------------------------------------------------------------------
-- Elimination operations

eliminateNotEqualRatTensor ::
  (MonadQueryStructure m) =>
  TensorOp2Args (Value Builtin) ->
  m (Value Builtin)
eliminateNotEqualRatTensor args@(TensorOp2Args dims _ _) = do
  PropertyMetaData {..} <- ask
  if supportsStrictInequalities queryFormat
    then throwError $ UnsupportedInequality (queryFormatID queryFormat) propertyProvenance
    else do
      let leq = fromBoolValue $ VCompareRatTensor (Le, args)
      let geq = fromBoolValue $ VCompareRatTensor (Ge, args)
      return $ fromBoolValue $ VOr (TensorOp2Args dims leq geq)

eliminateTensorAssertion ::
  forall m.
  (MonadQueryStructure m) =>
  EvalSimple TensorOp2Args Builtin m ->
  TensorOp2Args (Value Builtin) ->
  m (Value Builtin)
eliminateTensorAssertion evalFn (TensorOp2Args dims xs ys) =
  case argExpr dims of
    ICons _ d@(INatLiteral n) ds -> do
      let tElem = implicit $ fromTypeValue VRatType
      let dsArg = implicitIrrelevant ds
      let mkAt vs i = evalAt (AtArgs tElem (implicitIrrelevant d) dsArg vs (IIndexLiteral i))
      let stackElements vs = (traverse (mkAt vs) [0 .. (n - 1)] :: m [Value Builtin])
      let stackArgs vs = StackTensorArgs tElem d dsArg <$> stackElements vs
      let stackExpr vs = evalStackTensor =<< stackArgs vs
      relArgs <- TensorOp2Args dims <$> stackExpr xs <*> stackExpr ys
      evalFn relArgs
    _ -> do
      compilerDeveloperError ("unexpected dimensions" <+> prettyVerbose dims)

eliminateExists ::
  (MonadQueryStructure m) =>
  VBinder Builtin ->
  Closure Builtin ->
  m (MaybeTrivial Partitions)
eliminateExists binder (Closure env body) = do
  let varName = getBinderName binder
  let subpassDoc = "compilation of quantified variable" <+> quotePretty varName
  logCompilerPass MidDetail subpassDoc $ do
    -- Get the shape and name of the quantified variable
    namedCtx <- getGlobalNamedBoundCtx
    propertyProv <- asks propertyProvenance
    (userVarName, userVarShapeValue) <- createUserVar propertyProv namedCtx binder
    userVarShape <- case getDims userVarShapeValue of
      Just shape -> return shape
      _ -> throwError $ VariableSizeTensorQuantification propertyProv namedCtx binder userVarShapeValue

    -- Update the global context
    globalCtx <- get
    let (userVar, newGlobalCtx) = addUserVarToGlobalContext userVarName userVarShape globalCtx
    put newGlobalCtx

    -- Normalise the expression
    let newEnv = extendEnvWithDefined (VBoundVar userVar []) binder env
    normExpr <- normaliseInEnv newEnv body

    -- Recursively compile the expression.
    (partitions, networkInputEqualities) <- runWriterT (compileBoolExpr normExpr)

    -- Prepend network equalities to the tree (prepending is important for
    -- performance as the search for constraints will find them first.)
    networkEqPartitions <- networkEqualitiesToPartition networkInputEqualities
    let finalPartitions = andTrivial andPartitions partitions networkEqPartitions

    -- Solve for the user variable.
    solveExists finalPartitions userVar

networkEqualitiesToPartition ::
  (MonadQueryStructure m) =>
  [Value Builtin] ->
  m (MaybeTrivial Partitions)
networkEqualitiesToPartition networkEqualities = do
  logDebugM MaxDetail $ do
    networkEqDocs <- traverse prettyFriendlyInCtx networkEqualities
    return $ line <> "Generated network equalities:" <> line <> indent 2 (vsep networkEqDocs)

  results <- forM networkEqualities $ \equality -> do
    (partitions, newNetworkEqualities) <- runWriterT (compileBoolExpr equality)
    if null newNetworkEqualities
      then return partitions
      else andTrivial andPartitions partitions <$> networkEqualitiesToPartition newNetworkEqualities

  return $ foldr (andTrivial andPartitions) (Trivial True) results

--------------------------------------------------------------------------------
-- Vector operations preservation

-- | Constructs a temporary error with no real fields. This should be recaught
-- and populated higher up the query compilation process.
catchableUnsupportedAlternatingQuantifiersError :: CompileError
catchableUnsupportedAlternatingQuantifiersError =
  UnsupportedAlternatingQuantifiers x x x
  where
    x = developerError "Evaluating temporary quantifier error"

-- | Constructs a temporary error with no real fields. This should be recaught
-- and populated higher up the query compilation process.
catchableUnsupportedNonLinearConstraint :: CompileError
catchableUnsupportedNonLinearConstraint =
  UnsupportedNonLinearConstraint x x x
  where
    x = developerError "Evaluating temporary quantifier error"
