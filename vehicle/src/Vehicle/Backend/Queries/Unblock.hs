module Vehicle.Backend.Queries.Unblock
  ( unblockBoolExpr,
    tryPurifyAssertion,
    UnblockingActions (..),
    unblockRatTensorValue,
  )
where

import Control.Monad (when)
import Vehicle.Backend.Queries.UserVariableElimination.Core
import Vehicle.Compile.Boolean.LiftIf
import Vehicle.Compile.Context.Free (MonadFreeContext, getFreeEnv)
import Vehicle.Compile.Context.Name (MonadNameContext, getNameContext)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Builtin
import Vehicle.Compile.Normalise.NBE (evalApp)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.TypedView
import Vehicle.Data.Code.Value

--------------------------------------------------------------------------------
-- Unblocking
--------------------------------------------------------------------------------

type MonadUnblock m = (MonadCompile m, MonadFreeContext Builtin m, MonadNameContext m)

type MonadPurify m = MonadUnblock m

data UnblockingActions m = UnblockingActions
  { unblockRatTensorBoundVar :: Lv -> m (Value Builtin),
    unblockNetworkApp :: NetworkApplication -> m (Value Builtin)
  }

-- | Lifts all `if`s in the provided expression `e` to the top-level, while
-- preserving the guarantee that the expression is normalised as much as
-- possible.
unblockBoolExpr :: (MonadUnblock m) => Value Builtin -> m (Value Builtin)
unblockBoolExpr expr = do
  ctx <- getNameContext
  let exprDoc = prettyFriendly (WithContext expr ctx)
  logDebug MaxDetail $ line <> "unblocking" <+> squotes exprDoc
  incrCallDepth

  unblockedExpr <- unblockBoolTensorValue expr
  let unblockedExprDoc = prettyFriendly (WithContext unblockedExpr ctx)
  logDebug MaxDetail $ "result:" <+> squotes unblockedExprDoc

  when (layoutAsString exprDoc == layoutAsString unblockedExprDoc) $
    developerError $
      "Failed to unblock expression:" <+> exprDoc

  decrCallDepth
  return unblockedExpr

tryPurifyAssertion ::
  (MonadPurify m) =>
  UnblockingActions m ->
  ComparisonOp ->
  TensorOp2Args (Value Builtin) ->
  m (Value Builtin)
tryPurifyAssertion actions op args = do
  preCtx <- getNameContext
  logDebugM MaxDetail $ do
    let assertion = fromBoolValue $ VCompareRatTensor (op, args)
    let assertionDoc = prettyFriendly (WithContext assertion preCtx)
    return $ line <> "Trying to purify" <+> squotes assertionDoc
  incrCallDepth

  let unblock = unblockRatTensorValue actions
  unblockedExpr <- unblockTensorOp2 unblock (evalCompareRatTensor op) args

  logDebugM MaxDetail $ do
    postCtx <- getNameContext
    let unblockedAssertionDoc = prettyFriendly (WithContext unblockedExpr postCtx)
    return $ "Result" <+> squotes unblockedAssertionDoc

  decrCallDepth
  return unblockedExpr

--------------------------------------------------------------------------------
-- Unblocking types

type UnblockingFunction m = (MonadUnblock m) => Value Builtin -> m (Value Builtin)

unblockBoolTensorValue :: UnblockingFunction m
unblockBoolTensorValue expr = do
  showEntry expr
  showExit =<< case toBoolValue expr of
    -- Already unblocked
    VBoolTensorLiteral {} -> return expr
    VAnd {} -> return expr
    VOr {} -> return expr
    VNot {} -> return expr
    VBoolIf {} -> return expr
    VCompareRatTensor {} -> return expr
    VQuantifyRatTensor {} -> return expr
    -- Recursively unblock
    VReduceAndTensor args -> unblockReduceTensor unblock evalReduceAndTensor args
    VReduceOrTensor args -> unblockReduceTensor unblock evalReduceOrTensor args
    VCompareIndex (op, args) -> unblockIndexOp2 (evalCompareIndex op) args
    VCompareNat (op, args) -> unblockOp2 unblock (evalCompareNat op) args
    VConstBoolTensor args -> unblockConstTensor args
    VBoolStackTensor args -> unblockStackTensor unblock args
    VBoolAt args -> unblockAtTensor unblock args
    VBoolForeach args -> unblockForeachTensor args
  where
    unblock = unblockBoolTensorValue

unblockRatTensorValue :: (MonadPurify m) => UnblockingActions m -> Value Builtin -> m (Value Builtin)
unblockRatTensorValue actions@UnblockingActions {..} expr = do
  showEntry expr
  showExit =<< case toRatTensorValue expr of
    -- Rational operators
    VRatTensorLiteral {} -> return expr
    VIfRatTensor {} -> return expr
    -- Recursively purify
    VNegRatTensor args -> unblockTensorOp1 unblock evalNegRatTensor args
    VAddRatTensor args -> unblockTensorOp2 unblock evalAddRatTensor args
    VSubRatTensor args -> unblockTensorOp2 unblock evalSubRatTensor args
    VMulRatTensor args -> unblockTensorOp2 unblock evalMulRatTensor args
    VDivRatTensor args -> unblockTensorOp2 unblock evalDivRatTensor args
    VMinRatTensor args -> unblockTensorOp2 unblock evalMinRatTensor args
    VMaxRatTensor args -> unblockTensorOp2 unblock evalMaxRatTensor args
    VReduceAddRatTensor args -> unblockReduceTensor unblock evalReduceAddRatTensor args
    VReduceMulRatTensor args -> unblockReduceTensor unblock evalReduceMulRatTensor args
    VReduceMinRatTensor args -> unblockReduceTensor unblock evalReduceMinRatTensor args
    VReduceMaxRatTensor args -> unblockReduceTensor unblock evalReduceMaxRatTensor args
    VRatTensorVar v -> unblockRatTensorBoundVar v
    VNetworkApp n args -> unblockNetworkApp (nameOf n, args)
    VRatConstTensor args -> unblockConstTensor args
    VRatStackTensor args -> unblockStackTensor unblock args
    VRatAt args -> unblockAtTensor unblock args
    VRatForeach args -> unblockForeachTensor args
  where
    unblock = unblockRatTensorValue actions

unblockDimensionsValue :: UnblockingFunction m
unblockDimensionsValue expr = case toDimensionsValue expr of
  VDimsNil {} -> return expr
  VDimsCons {} -> return expr
  VDimsIf {} -> return expr
  VDimsBoundVar {} -> unexpectedExprError currentPass (prettyVerbose expr)

unblockIndexValue :: UnblockingFunction m
unblockIndexValue expr = case toIndexValue expr of
  VIndexLiteral {} -> return expr
  VIndexIf {} -> return expr
  VIndexBoundVar {} -> unexpectedExprError currentPass (prettyVerbose expr)

unblockNatValue :: UnblockingFunction m
unblockNatValue expr = case toNatValue expr of
  VNatLiteral {} -> return expr
  VNatIf {} -> return expr
  VNatAdd args -> unblockOp2 unblockNatValue evalAddNat args
  VNatMul args -> unblockOp2 unblockNatValue evalMulNat args
  VNatBoundVar {} -> unexpectedExprError currentPass (prettyVerbose expr)
  VNatParameter {} -> unexpectedExprError currentPass (prettyVerbose expr)

--------------------------------------------------------------------------------
-- Unblocking individual operations

unblockOp2 ::
  (MonadUnblock m) =>
  UnblockingFunction m ->
  EvalSimple Op2Args Builtin m ->
  Op2Args (Value Builtin) ->
  m (Value Builtin)
unblockOp2 unblock evalFn (Op2Args x y) = do
  x' <- unblock x
  y' <- unblock y
  liftIf x' $ \x'' ->
    liftIf y' $ \y'' -> do
      evalFn $ Op2Args x'' y''

unblockIndexOp2 ::
  (MonadUnblock m) =>
  EvalSimple IndexComparisonArgs Builtin m ->
  IndexComparisonArgs (Value Builtin) ->
  m (Value Builtin)
unblockIndexOp2 evalFn (IndexCompArgs n1 n2 x y) = do
  x' <- unblockIndexValue x
  y' <- unblockIndexValue y
  liftIf x' $ \x'' ->
    liftIf y' $ \y'' -> do
      evalFn $ IndexCompArgs n1 n2 x'' y''

unblockTensorOp1 ::
  (MonadUnblock m) =>
  UnblockingFunction m ->
  EvalSimple TensorOp1Args Builtin m ->
  TensorOp1Args (Value Builtin) ->
  m (Value Builtin)
unblockTensorOp1 unblock evalFn (TensorOp1Args ds xs) = do
  xs' <- unblock xs
  liftIf xs' $ \xs'' -> do
    evalFn (TensorOp1Args ds xs'')

unblockTensorOp2 ::
  (MonadUnblock m) =>
  UnblockingFunction m ->
  EvalSimple TensorOp2Args Builtin m ->
  TensorOp2Args (Value Builtin) ->
  m (Value Builtin)
unblockTensorOp2 unblock evalFn (TensorOp2Args ds xs ys) = do
  xs' <- unblock xs
  ys' <- unblock ys
  liftIf xs' $ \xs'' ->
    liftIf ys' $ \ys'' -> do
      evalFn $ TensorOp2Args ds xs'' ys''

unblockReduceTensor ::
  (MonadUnblock m) =>
  UnblockingFunction m ->
  EvalSimple TensorReductionArgs Builtin m ->
  TensorReductionArgs (Value Builtin) ->
  m (Value Builtin)
unblockReduceTensor unblock evalFn (TensorOp2Args ds e xs) = do
  xs' <- unblock xs
  liftIf xs' $ \xs'' ->
    evalFn $ TensorOp2Args ds e xs''

unblockConstTensor ::
  (MonadUnblock m) =>
  ConstTensorArgs (Value Builtin) ->
  m (Value Builtin)
unblockConstTensor (ConstTensorArgs tElem value dims) = do
  dims' <- unblockDimensionsValue dims
  liftIf dims' $ \dims'' -> do
    evalConstTensor $ ConstTensorArgs tElem value dims''

unblockStackTensor ::
  (MonadUnblock m) =>
  UnblockingFunction m ->
  StackTensorArgs (Value Builtin) ->
  m (Value Builtin)
unblockStackTensor unblock (StackTensorArgs tElem d ds xss) = do
  d' <- unblockNatValue d
  xss' <- traverse unblock xss
  liftIf d' $ \d'' ->
    liftIfValues xss' $ \xss'' ->
      evalStackTensor $ StackTensorArgs tElem d'' ds xss''

unblockAtTensor ::
  (MonadUnblock m) =>
  UnblockingFunction m ->
  AtArgs (Value Builtin) ->
  m (Value Builtin)
unblockAtTensor unblock (AtArgs tElem d ds xs i) = do
  xs' <- unblock xs
  i' <- unblockIndexValue i
  liftIf xs' $ \xs'' ->
    liftIf i' $ \i'' -> do
      evalAt $ AtArgs tElem d ds xs'' i''

unblockForeachTensor ::
  (MonadUnblock m) =>
  ForeachArgs (Value Builtin) ->
  m (Value Builtin)
unblockForeachTensor (ForeachArgs tElem d ds fn) = do
  d' <- unblockNatValue d
  liftIf d' $ \d'' -> do
    freeEnv <- getFreeEnv
    evalForeach (evalApp freeEnv) $ ForeachArgs tElem d'' ds fn

--------------------------------------------------------------------------------
-- Unblocking operations

currentPass :: CompilerPass
currentPass = "unblocking"

showEntry :: forall m. (MonadUnblock m) => Value Builtin -> m ()
showEntry e = do
  ctx <- getNameContext
  -- logDebug MaxDetail $ "unblock-entry" <+> prettyVerbose e
  logDebug MaxDetail $ "unblock-entry" <+> prettyFriendly (WithContext e ctx)
  incrCallDepth

showExit :: forall m. (MonadUnblock m) => Value Builtin -> m (Value Builtin)
showExit e = do
  ctx <- getNameContext
  decrCallDepth
  -- logDebug MaxDetail $ "unblock-exit " <+> prettyVerbose e
  logDebug MaxDetail $ "unblock-exit " <+> prettyFriendly (WithContext e ctx)
  return e
