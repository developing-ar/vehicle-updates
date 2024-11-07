module Vehicle.Compile.Rational.LinearExpr
  ( LinearityError (..),
    compileTensorLinearRelation,
  )
where

-- Needed as Applicative is exported by Prelude in GHC 9.6 and above.
import Control.Applicative (Applicative (..))
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT)
import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.LinearExpr (LinearExpr, addExprs, constantExpr, isConstant, scaleExpr, singletonVarExpr)
import Vehicle.Data.Code.TypedView
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (RationalTensor, TensorShape, zeroTensor, pattern ZeroDimTensor)
import Prelude hiding (Applicative (..))

type MonadCompileLinearExpr m =
  ( MonadLogger m,
    MonadError LinearityError m
  )

data LinearityError
  = NonLinearity
  | UnexpectedExpr (Value Builtin)
  | UnreducedExpr (Value Builtin)

--------------------------------------------------------------------------------
-- Tensor expression

compileTensorLinearRelation ::
  (MonadLogger m) =>
  (Lv -> ExceptT LinearityError m TensorShape) ->
  Value Builtin ->
  Value Builtin ->
  m (Either LinearityError (LinearExpr RationalTensor, LinearExpr RationalTensor))
compileTensorLinearRelation lookupVar x y = do
  runExceptT $ do
    x' <- compile lookupVar x
    y' <- compile lookupVar y
    return (x', y')

compile ::
  forall m.
  (MonadCompileLinearExpr m) =>
  (Lv -> m TensorShape) ->
  Value Builtin ->
  m (LinearExpr RationalTensor)
compile lookupVar expr = case toRatTensorValue expr of
  ----------------
  -- Base cases --
  ----------------
  VRatTensorLiteral t -> do
    return $ constantExpr t
  VRatTensorVar lv -> do
    shape <- lookupVar lv
    return $ singletonVarExpr (zeroTensor shape) lv
  ---------------------
  -- Inductive cases --
  ---------------------
  VNegRatTensor _ e -> scaleExpr (-1) <$> compile lookupVar e
  VAddRatTensor _ e1 e2 -> addExprs 1 1 <$> compile lookupVar e1 <*> compile lookupVar e2
  VSubRatTensor _ e1 e2 -> addExprs 1 (-1) <$> compile lookupVar e1 <*> compile lookupVar e2
  VMulRatTensor _ e1 e2 -> do
    e1' <- compile lookupVar e1
    e2' <- compile lookupVar e2
    case (isConstant e1', isConstant e2') of
      (Just (ZeroDimTensor c1), _) -> return $ scaleExpr c1 e2'
      (_, Just (ZeroDimTensor c2)) -> return $ scaleExpr c2 e1'
      _ -> throwError NonLinearity
  VDivRatTensor _ e1 e2 -> do
    e1' <- compile lookupVar e1
    e2' <- compile lookupVar e2
    case isConstant e2' of
      (Just (ZeroDimTensor c2)) -> return $ scaleExpr (1 / c2) e1'
      _ -> throwError NonLinearity
  ---------------------
  -- Unreduced cases --
  ---------------------
  -- The expression is being blocked
  VRatConstTensor {} -> unreduced
  VRatStackTensor {} -> unreduced
  VRatAt {} -> unreduced
  VNetworkApp {} -> unreduced
  VRatForeach {} -> unreduced
  VIfRatTensor {} -> unreduced
  -----------------------
  -- Unsupported cases --
  -----------------------
  VMinRatTensor {} -> unexpected
  VMaxRatTensor {} -> unexpected
  VReduceAddRatTensor {} -> unexpected
  VReduceMulRatTensor {} -> unexpected
  VReduceMinRatTensor {} -> unexpected
  VReduceMaxRatTensor {} -> unexpected
  where
    unexpected = throwError $ UnexpectedExpr expr
    unreduced = throwError $ UnreducedExpr expr
