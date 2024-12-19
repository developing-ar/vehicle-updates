module Vehicle.Backend.Queries.Unblock
  ( unblockBoolExpr,
    tryPurifyAssertion,
    UnblockingActions (..),
  )
where

import Vehicle.Backend.Queries.UserVariableElimination.Core
import Vehicle.Compile.Boolean.LiftIf
import Vehicle.Compile.Context.Free (MonadFreeContext, getFreeEnv)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Builtin hiding (evalOp2)
import Vehicle.Compile.Normalise.NBE (evalApp)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly, prettyVerbose)
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.TypedView
import Vehicle.Data.Code.Value

--------------------------------------------------------------------------------
-- Unblocking
--------------------------------------------------------------------------------

type MonadUnblock m = (MonadCompile m, MonadFreeContext Builtin m)

type MonadPurify m = MonadQueryStructure m

data UnblockingActions m = UnblockingActions
  { unblockRatTensorBoundVar ::
      Lv ->
      m (Value Builtin),
    unblockNetworkApp ::
      UnblockingFunction m ->
      Identifier ->
      Spine Builtin ->
      m (Value Builtin)
  }

-- | Lifts all `if`s in the provided expression `e` to the top-level, while
-- preserving the guarantee that the expression is normalised as much as
-- possible.
unblockBoolExpr :: (MonadUnblock m) => NamedBoundCtx -> Value Builtin -> m (Value Builtin)
unblockBoolExpr ctx expr = do
  let exprDoc = prettyFriendly (WithContext expr ctx)
  logDebug MaxDetail $ line <> "Unblocking" <+> squotes exprDoc
  incrCallDepth

  unblockedExpr <- unblockBoolTensorValue expr
  let unblockedExprDoc = prettyFriendly (WithContext unblockedExpr ctx)
  logDebug MaxDetail $ "Unblocked to" <+> squotes unblockedExprDoc
  decrCallDepth
  return unblockedExpr

tryPurifyAssertion ::
  (MonadPurify m) =>
  UnblockingActions m ->
  Value Builtin ->
  m (Value Builtin)
tryPurifyAssertion actions assertion = do
  logDebugM MaxDetail $ do
    preCtx <- getGlobalNamedBoundCtx
    let assertionDoc = prettyFriendly (WithContext assertion preCtx)
    return $ line <> "Trying to purify" <+> squotes assertionDoc
  incrCallDepth

  let unblock = unblockRatTensorValue actions
  unblockedExpr <- case toBoolValue assertion of
    VEqualsRatTensor Eq dims x y -> unblockOp2 (Equals EqRatTensor Eq) (evalEqualityRatTensor Eq) unblock unblock [dims] x y
    VOrderRatTensor op dims x y -> unblockOp2 (Order OrderRatTensor op) (evalOrderRatTensor op) unblock unblock [dims] x y
    _ -> unexpectedExprError "purifying assertion" (prettyVerbose assertion)

  logDebugM MaxDetail $ do
    postCtx <- getGlobalNamedBoundCtx
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
    VOrderRatTensor {} -> return expr
    VEqualsRatTensor {} -> return expr
    VQuantifyRatTensor {} -> return expr
    -- Recursively unblock
    VReduceAndTensor dims xs -> unblockOp1 ReduceAndTensor evalReduceAndTensor unblock [dims] xs
    VReduceOrTensor dims xs -> unblockOp1 ReduceOrTensor evalReduceOrTensor unblock [dims] xs
    VOrderIndex op n1 n2 x y -> unblockIndexOp2 (Order OrderIndex op) (evalOrderIndex op) n1 n2 x y
    VEqualsIndex op n1 n2 x y -> unblockIndexOp2 (Equals EqIndex op) (evalEqualsIndex op) n1 n2 x y
    VOrderNat op x y -> unblockNatOp2 (Order OrderNat op) (evalOrderNat op) x y
    VEqualsNat op x y -> unblockNatOp2 (Equals EqNat op) (evalEqualsNat op) x y
    VConstBoolTensor v dims -> unblockConstTensor IBoolType v dims
    VBoolStackTensor d ds xss -> unblockStackTensor unblock IBoolType d ds xss
    VBoolAt d ds xs s -> unblockAtTensor unblock IBoolType d ds xs s
    VBoolForeach d ds f -> unblockForeachTensor IBoolType d ds f
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
    VNegRatTensor dims x -> unblockOp1 (Neg NegRatTensor) evalNegRatTensor unblock [dims] x
    VAddRatTensor dims x y -> unblockOp2 (Add AddRatTensor) evalAddRatTensor unblock unblock [dims] x y
    VSubRatTensor dims x y -> unblockOp2 (Sub SubRatTensor) evalSubRatTensor unblock unblock [dims] x y
    VMulRatTensor dims x y -> unblockOp2 (Mul MulRatTensor) evalMulRatTensor unblock unblock [dims] x y
    VDivRatTensor dims x y -> unblockOp2 (Div DivRatTensor) evalDivRatTensor unblock unblock [dims] x y
    VMinRatTensor dims x y -> unblockOp2 (Min MinRatTensor) evalMinRatTensor unblock unblock [dims] x y
    VMaxRatTensor dims x y -> unblockOp2 (Max MaxRatTensor) evalMaxRatTensor unblock unblock [dims] x y
    VReduceAddRatTensor dims xs -> unblockOp1 ReduceAddRatTensor evalReduceAddRatTensor unblock [dims] xs
    VReduceMulRatTensor dims xs -> unblockOp1 ReduceMulRatTensor evalReduceMulRatTensor unblock [dims] xs
    VReduceMinRatTensor dims xs -> unblockOp1 ReduceMinRatTensor evalReduceMinRatTensor unblock [dims] xs
    VReduceMaxRatTensor dims xs -> unblockOp1 ReduceMaxRatTensor evalReduceMaxRatTensor unblock [dims] xs
    VRatTensorVar v -> unblockRatTensorBoundVar v
    VNetworkApp n spine -> unblockNetworkApp unblock n spine
    VRatConstTensor v dims -> unblockConstTensor IRatType v dims
    VRatStackTensor n ds xss -> unblockStackTensor unblock IRatType n ds xss
    VRatAt d ds xs i -> unblockAtTensor unblock IRatType d ds xs i
    VRatForeach d ds fn -> unblockForeachTensor IRatType d ds fn
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
  VNatAdd x y -> unblockNatOp2 (Add AddNat) evalAddNat x y
  VNatMul x y -> unblockNatOp2 (Mul MulNat) evalMulNat x y
  VNatBoundVar {} -> unexpectedExprError currentPass (prettyVerbose expr)
  VNatParameter {} -> unexpectedExprError currentPass (prettyVerbose expr)

--------------------------------------------------------------------------------
-- Unblocking individual operations

unblockOp1 ::
  (MonadUnblock m) =>
  BuiltinFunction ->
  EvalSimpleBuiltin (Value Builtin) ->
  UnblockingFunction m ->
  [VArg Builtin] ->
  Value Builtin ->
  m (Value Builtin)
unblockOp1 fn evalFn unblock1 implicitArgs x = do
  x' <- unblock1 x
  liftIf x' $ \x'' -> do
    let args = implicitArgs <> [explicit x'']
    return $ evalFn (VBuiltin (BuiltinFunction fn) args) args

unblockOp2 ::
  (MonadUnblock m) =>
  BuiltinFunction ->
  EvalSimpleBuiltin (Value Builtin) ->
  UnblockingFunction m ->
  UnblockingFunction m ->
  [VArg Builtin] ->
  Value Builtin ->
  Value Builtin ->
  m (Value Builtin)
unblockOp2 fn evalFn unblock1 unblock2 implicitArgs x y = do
  x' <- unblock1 x
  y' <- unblock2 y
  liftIf x' $ \x'' ->
    liftIf y' $ \y'' -> do
      let args = implicitArgs <> [explicit x'', explicit y'']
      return $ evalFn (VBuiltin (BuiltinFunction fn) args) args

unblockNatOp2 ::
  (MonadUnblock m) =>
  BuiltinFunction ->
  EvalSimpleBuiltin (Value Builtin) ->
  Value Builtin ->
  Value Builtin ->
  m (Value Builtin)
unblockNatOp2 fn evalFn =
  unblockOp2 fn evalFn unblockNatValue unblockNatValue []

unblockIndexOp2 ::
  (MonadUnblock m) =>
  BuiltinFunction ->
  EvalSimpleBuiltin (Value Builtin) ->
  VArg Builtin ->
  VArg Builtin ->
  Value Builtin ->
  Value Builtin ->
  m (Value Builtin)
unblockIndexOp2 fn evalFn n1 n2 =
  unblockOp2 fn evalFn unblockIndexValue unblockIndexValue [n1, n2]

unblockConstTensor ::
  (MonadUnblock m) =>
  VType Builtin ->
  Value Builtin ->
  Value Builtin ->
  m (Value Builtin)
unblockConstTensor tElem value dims = do
  dims' <- unblockDimensionsValue dims
  liftIf dims' $ \dims'' -> do
    let args = [implicit tElem, explicit value, explicit dims'']
    return $ evalConstTensor (VBuiltin (BuiltinFunction ConstTensor) args) args

unblockStackTensor ::
  (MonadUnblock m) =>
  UnblockingFunction m ->
  VType Builtin ->
  VArg Builtin ->
  VArg Builtin ->
  Spine Builtin ->
  m (Value Builtin)
unblockStackTensor unblock tElem d ds xss = do
  d' <- traverse unblockNatValue d
  xss' <- traverseSpine unblock xss
  liftIfArg d' $ \d'' ->
    liftIfSpine xss' $ \xss'' -> do
      let args = [d'', ds, implicit tElem] <> xss''
      return $ evalStackTensor (VBuiltin (BuiltinFunction StackTensor) args) args

unblockAtTensor ::
  (MonadUnblock m) =>
  UnblockingFunction m ->
  VType Builtin ->
  VArg Builtin ->
  VArg Builtin ->
  Value Builtin ->
  Value Builtin ->
  m (Value Builtin)
unblockAtTensor unblock tElem d ds =
  unblockOp2 At evalAt unblock unblockIndexValue [implicit tElem, d, ds]

unblockForeachTensor ::
  (MonadUnblock m) =>
  VType Builtin ->
  VArg Builtin ->
  VArg Builtin ->
  Value Builtin ->
  m (Value Builtin)
unblockForeachTensor tElem d ds fn = do
  d' <- unblockNatValue (argExpr d)
  liftIf d' $ \d'' -> do
    let args = [implicit tElem, implicit d'', ds, explicit fn]
    freeEnv <- getFreeEnv
    evalForeach (evalApp freeEnv) (VBuiltin (BuiltinFunction Foreach) args) args

--------------------------------------------------------------------------------
-- Unblocking operations

currentPass :: CompilerPass
currentPass = "unblocking"

showEntry :: forall m. (MonadUnblock m) => Value Builtin -> m ()
showEntry e = do
  -- ctx <- getNamedBoundCtx (Proxy @(Type Builtin))
  logDebug MaxDetail $ "unblock-entry" <+> prettyVerbose e
  incrCallDepth

showExit :: forall m. (MonadUnblock m) => Value Builtin -> m (Value Builtin)
showExit e = do
  decrCallDepth
  -- ctx <- getNamedBoundCtx (Proxy @(Type Builtin))
  logDebug MaxDetail $ "unblock-exit " <+> prettyVerbose e --  (WithContext e ctx)
  return e
