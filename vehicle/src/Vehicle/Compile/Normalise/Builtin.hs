{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
module Vehicle.Compile.Normalise.Builtin where

import Control.Applicative ((<|>))
import Data.Maybe (fromMaybe)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print.Builtin
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Linearity (LinearityBuiltin (..))
import Vehicle.Data.Builtin.Loss (LossBuiltin (..))
import Vehicle.Data.Builtin.Loss qualified as L
import Vehicle.Data.Builtin.Polarity (PolarityBuiltin (..))
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (Tensor, at, foldTensor, stack, unstack, zipWithTensor, pattern ConstantTensor, pattern ZeroDimTensor)

-- Okay so the important thing to remember about this module is that we have
-- a variety of different typing schemes for builtins (standard, polarity,
-- linearity etc.). Normalisation needs to work for all of these, and
-- therefore we can't guarantee what the implicit and instance arguments are
-- going to be for a given builtin. However, explicit arguments are always
-- the same in every type system.

-- Therefore this can be viewed as a type of runtime irrelevance, where only
-- the explicit arguments are runtime relevant. This notion isn't made
-- explicit in the code below. Maybe there's a nice way of doing so?

-----------------------------------------------------------------------------
-- Main method

type Eval builtin m =
  (MonadLogger m) =>
  Expr builtin ->
  m (Value builtin)

-----------------------------------------------------------------------------
-- Builtin evaluation

-- | A method for evaluating an application.
-- Although there is only one implementation of this type, it needs to be
-- passed around as an argument to avoid dependency cycles between
-- this module and the module in which the general NBE algorithm lives in.
type EvalApp builtin m = Value builtin -> [VArg builtin] -> m (Value builtin)

--------------------------------------------------------------------------------
-- Evaluation

type BlockingArguments builtin = [Value builtin]

-- | A method for evaluating builtins that takes in an argument allowing the
-- recursive evaluation of applications. that takes in an argument allowing
-- the subsequent further evaluation of applications.
-- Such recursive evaluation is necessary when evaluating higher order
-- functions such as fold, map etc.
type EvalBuiltin args builtin m =
  (MonadLogger m) =>
  EvalApp builtin m ->
  args (Value builtin) ->
  m (Maybe (Value builtin))

type EvalSimple args builtin =
  args (Value builtin) ->
  Value builtin

type EvalSimplePartial args builtin =
  args (Value builtin) ->
  Maybe (Value builtin)

evalSimple ::
  (IsArgs args) =>
  builtin ->
  EvalSimplePartial args builtin ->
  args (Value builtin) ->
  Value builtin
evalSimple b eval args = case eval args of
  Just result -> result
  Nothing -> VBuiltin b (mkExpr accessSpine args)

evalNonSimple ::
  (MonadLogger m, IsArgs args) =>
  EvalApp builtin m ->
  Accessor builtin () ->
  EvalBuiltin args builtin m ->
  args (Value builtin) ->
  m (Value builtin)
evalNonSimple evalApp accessBuiltin eval args = do
  maybeResult <- eval evalApp args
  return $ case maybeResult of
    Just result -> result
    Nothing -> VBuiltin (mkExpr accessBuiltin ()) (mkExpr accessSpine args)

evalTensorOp1 ::
  forall builtin a.
  (HasTensorExpr Value builtin) =>
  Accessor builtin () ->
  Accessor (Value builtin) (Tensor a) ->
  (a -> a) ->
  TensorOp1Args (Value builtin) ->
  Value builtin
evalTensorOp1 accessBuiltinOp accessLit op = evalSimple (mkExpr accessBuiltinOp ()) eval
  where
    eval :: EvalSimplePartial TensorOp1Args builtin
    eval = \case
      TensorOp1Args _ds (getExpr accessLit -> Just t) ->
        Just $ mkExpr accessLit $ fmap op t
      TensorOp1Args (argExpr -> ICons _ d _) (getExpr accessConstTensor -> Just args) ->
        Just $ mkExpr accessConstTensor $ mapConstTensorValue (evalFull d) args
      TensorOp1Args (argExpr -> ICons _ d _) (getExpr accessStackTensor -> Just args) ->
        Just $ mkExpr accessStackTensor $ mapStackTensorElements (evalFull d) args
      _ -> Nothing

    evalFull :: Value builtin -> Value builtin -> Value builtin
    evalFull d x = evalSimple (mkExpr accessBuiltinOp ()) eval (TensorOp1Args (implicitIrrelevant d) x)

evalTensorOp2 ::
  forall builtin a.
  (HasTensorExpr Value builtin, Eq a) =>
  Accessor builtin () ->
  Accessor (Value builtin) (Tensor a) ->
  (a -> a -> a) ->
  Maybe a ->
  Maybe a ->
  TensorOp2Args (Value builtin) ->
  Value builtin
evalTensorOp2 accessBuiltin accessLit =
  evalHeteroTensorOp2 (mkExpr accessBuiltin ()) accessLit accessLit

evalHeteroTensorOp2 ::
  forall builtin a b.
  (HasTensorExpr Value builtin, Eq a, Eq b) =>
  builtin ->
  Accessor (Value builtin) (Tensor a) ->
  Accessor (Value builtin) (Tensor b) ->
  (a -> a -> b) ->
  Maybe a ->
  Maybe a ->
  TensorOp2Args (Value builtin) ->
  Value builtin
evalHeteroTensorOp2 b inputLit outputLit op leftUnit rightUnit = evalSimple b eval
  where
    eval :: EvalSimplePartial TensorOp2Args builtin
    eval = \case
      TensorOp2Args _ds (getExpr inputLit -> Just xs) (getExpr inputLit -> Just ys) ->
        Just $ mkExpr outputLit $ zipWithTensor op xs ys
      TensorOp2Args (argExpr -> ICons _ _ ds) (getExpr accessConstTensor -> Just xs) (getExpr accessConstTensor -> Just ys) ->
        Just $
          mkExpr accessConstTensor $
            xs
              { constValue = evalFull ds (constValue xs) (constValue ys)
              }
      -- Unlike const tensors, we need to eval stack tensors as after being combined with constants, short-circuiting of
      -- operations may allow for further reduction.
      TensorOp2Args (argExpr -> ICons _ _ ds) (getExpr inputLit -> Just xs) (getExpr accessStackTensor -> Just ys) ->
        Just $
          evalStackTensorWithPrimitives [Wrapper outputLit] $
            ys
              { stackElements = zipWith (evalFull ds) (unstackExpr xs) (stackElements ys)
              }
      TensorOp2Args (argExpr -> ICons _ _ ds) (getExpr accessStackTensor -> Just xs) (getExpr inputLit -> Just ys) ->
        Just $
          evalStackTensorWithPrimitives [Wrapper outputLit] $
            xs
              { stackElements = zipWith (evalFull ds) (stackElements xs) (unstackExpr ys)
              }
      TensorOp2Args (argExpr -> ICons _ _ ds) (getExpr accessStackTensor -> Just xs) (getExpr accessStackTensor -> Just ys) ->
        Just $
          evalStackTensorWithPrimitives [Wrapper outputLit] $
            xs
              { stackElements = zipWith (evalFull ds) (stackElements xs) (stackElements ys)
              }
      TensorOp2Args _ds (getExpr accessConstTensor -> Just xs) ys -> case (leftUnit, getExpr inputLit (constValue xs)) of
        (Just lunit, Just (ZeroDimTensor v)) | v == lunit -> Just ys
        _ -> Nothing
      TensorOp2Args _ds xs (getExpr accessConstTensor -> Just ys) -> case (rightUnit, getExpr inputLit (constValue ys)) of
        (Just runit, Just (ZeroDimTensor v)) | v == runit -> Just xs
        _ -> Nothing
      _ -> Nothing

    evalFull :: Value builtin -> Value builtin -> Value builtin -> Value builtin
    evalFull d x y = evalSimple b eval (TensorOp2Args (implicitIrrelevant d) x y)

    unstackExpr :: Tensor a -> [Value builtin]
    unstackExpr xs = mkExpr inputLit <$> unstack xs

evalReduceTensor ::
  forall builtin a.
  (HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  Accessor builtin () ->
  Accessor (Value builtin) (Tensor a) ->
  (TensorOp2Args (Value builtin) -> Value builtin) ->
  (a -> a -> a) ->
  TensorReductionArgs (Value builtin) ->
  Value builtin
evalReduceTensor accessReductionOp accessLit evalOp2 op2 =
  evalSimple (mkExpr accessReductionOp ()) eval
  where
    eval :: EvalSimplePartial TensorReductionArgs builtin
    eval = \case
      TensorOp2Args _ (getExpr accessLit -> Just e) (getExpr accessLit -> Just xs) ->
        Just $ mkExpr accessLit $ foldTensor op2 e xs
      TensorOp2Args (argExpr -> ICons _ _ ds) e (getExpr accessStackTensor -> Just xs) ->
        Just $ foldr (foldFn e (implicitIrrelevant ds)) e (stackElements xs)
      _ -> Nothing

    evalFull :: VArg builtin -> Value builtin -> Value builtin -> Value builtin
    evalFull ds e xs = evalSimple (mkExpr accessReductionOp ()) eval (TensorOp2Args ds e xs)

    evalBop :: VArg builtin -> Value builtin -> Value builtin -> Value builtin
    evalBop ds xs ys = evalOp2 (TensorOp2Args ds xs ys)

    foldFn e ds x y = evalBop ds (evalFull ds e x) y

-----------------------------------------------------------------------------
-- Individual builtin evaluation
-----------------------------------------------------------------------------
-- Bool

evalNot :: (HasBoolExpr Value builtin) => TensorOp1Args (Value builtin) -> Value builtin
evalNot = evalTensorOp1 accessNotBuiltin accessBoolTensorLiteral not

evalAnd :: (HasBoolExpr Value builtin) => TensorOp2Args (Value builtin) -> Value builtin
evalAnd = evalTensorOp2 accessAndBuiltin accessBoolTensorLiteral (&&) (Just True) (Just True)

evalOr :: (HasBoolExpr Value builtin) => TensorOp2Args (Value builtin) -> Value builtin
evalOr = evalTensorOp2 accessOrBuiltin accessBoolTensorLiteral (||) (Just False) (Just False)

evalImplies :: (HasBoolExpr Value builtin) => TensorOp2Args (Value builtin) -> Value builtin
evalImplies (TensorOp2Args ds xs ys) = evalOr (TensorOp2Args ds (evalNot (TensorOp1Args ds xs)) ys)

evalReduceAndTensor :: (HasBoolExpr Value builtin) => TensorReductionArgs (Value builtin) -> Value builtin
evalReduceAndTensor = evalReduceTensor accessReduceAndBuiltin accessBoolTensorLiteral evalAnd (&&)

evalReduceOrTensor :: (HasBoolExpr Value builtin) => TensorReductionArgs (Value builtin) -> Value builtin
evalReduceOrTensor = evalReduceTensor accessReduceOrBuiltin accessBoolTensorLiteral evalOr (||)

evalIf :: (HasBoolExpr Value builtin) => IfArgs (Value builtin) -> Value builtin
evalIf args@(IfArgs _t c e1 e2) = case c of
  IBoolLiteral True -> e1
  IBoolLiteral False -> e2
  _ -> mkExpr accessIf args

-----------------------------------------------------------------------------
-- Index

evalOrderIndex ::
  (HasBoolExpr Value builtin, BuiltinHasIndexLiterals builtin) =>
  OrderOp ->
  IndexComparisonArgs (Value builtin) ->
  Value builtin
evalOrderIndex op = \case
  IndexCompArgs _ _ (IIndexLiteral x) (IIndexLiteral y) -> IBoolLiteral (orderOp op x y)
  args -> mkExpr accessOrderIndex (op, args)

evalEqualsIndex ::
  (HasBoolExpr Value builtin, BuiltinHasIndexLiterals builtin) =>
  EqualityOp ->
  IndexComparisonArgs (Value builtin) ->
  Value builtin
evalEqualsIndex op = \case
  IndexCompArgs _ _ (IIndexLiteral x) (IIndexLiteral y) -> IBoolLiteral (equalityOp op x y)
  args -> mkExpr accessEqIndex (op, args)

-----------------------------------------------------------------------------
-- Nat

evalAddNat :: (BuiltinHasNatLiterals builtin) => Op2Args (Value builtin) -> Value builtin
evalAddNat = \case
  Op2Args (INatLiteral x) (INatLiteral y) -> INatLiteral (x + y)
  args -> mkExpr accessAddNat args

evalMulNat :: (BuiltinHasNatLiterals builtin) => Op2Args (Value builtin) -> Value builtin
evalMulNat = \case
  Op2Args (INatLiteral x) (INatLiteral y) -> INatLiteral (x * y)
  args -> mkExpr accessMulNat args

evalOrderNat ::
  (HasBoolExpr Value builtin, BuiltinHasNatLiterals builtin) =>
  OrderOp ->
  Op2Args (Value builtin) ->
  Value builtin
evalOrderNat op = \case
  Op2Args (INatLiteral x) (INatLiteral y) -> IBoolLiteral (orderOp op x y)
  args -> mkExpr accessOrderNat (op, args)

evalEqualsNat ::
  (HasBoolExpr Value builtin, BuiltinHasNatLiterals builtin) =>
  EqualityOp ->
  Op2Args (Value builtin) ->
  Value builtin
evalEqualsNat op = \case
  Op2Args (INatLiteral x) (INatLiteral y) -> IBoolLiteral (equalityOp op x y)
  args -> mkExpr accessEqNat (op, args)

evalFromNatToNat :: (BuiltinHasNatLiterals builtin) => FromNatArgs (Value builtin) -> Value builtin
evalFromNatToNat (FromNatArgs v _) = v

evalFromNatToIndex ::
  (BuiltinHasIndexLiterals builtin, BuiltinHasNatLiterals builtin, BuiltinHasCasts builtin) =>
  FromNatArgs (Value builtin) ->
  Value builtin
evalFromNatToIndex = \case
  FromNatArgs (INatLiteral v) _ -> IIndexLiteral v
  args -> mkExpr accessFromNatToIndex args

-----------------------------------------------------------------------------
-- Rat

evalFromNatToRat ::
  (HasRatExpr Value builtin, BuiltinHasNatLiterals builtin, BuiltinHasCasts builtin) =>
  FromNatArgs (Value builtin) ->
  Value builtin
evalFromNatToRat = \case
  FromNatArgs (INatLiteral n) _ -> IRatLiteral $ fromIntegral n
  args -> mkExpr accessFromNatToRat args

evalFromRatToRat :: Op1Args (Value builtin) -> Value builtin
evalFromRatToRat (Op1Args x) = x

evalVectorToList ::
  (BuiltinHasNatLiterals builtin, BuiltinHasListLiterals builtin, BuiltinHasCasts builtin) =>
  VectorToListArgs (Value builtin) ->
  Value builtin
evalVectorToList args@(VectorToListArgs t d xs) = case argExpr d of
  INatLiteral n | n == length xs -> mkListExpr (argExpr t) xs
  _ -> mkExpr accessFromVectorToList args

-----------------------------------------------------------------------------
-- List

evalMapList ::
  forall builtin m.
  (MonadLogger m, BuiltinHasListLiterals builtin) =>
  EvalApp builtin m ->
  MapListArgs (Value builtin) ->
  m (Value builtin)
evalMapList evalApp (MapListArgs a b f xs) = eval xs
  where
    eval :: Value builtin -> m (Value builtin)
    eval = \case
      INil _ -> return $ INil b
      ICons _ v vs -> do
        v' <- evalApp f [explicit v]
        vs' <- evalMapList evalApp (recArgs vs)
        return $ ICons b v' vs'
      vs -> return $ mkExpr accessMapList (recArgs vs)

    recArgs :: Value builtin -> MapListArgs (Value builtin)
    recArgs = MapListArgs a b f

evalFoldList ::
  forall m builtin.
  (MonadLogger m, BuiltinHasListLiterals builtin) =>
  EvalApp builtin m ->
  FoldListArgs (Value builtin) ->
  m (Value builtin)
evalFoldList evalApp (FoldListArgs a b f e xs) = eval xs
  where
    eval :: Value builtin -> m (Value builtin)
    eval = \case
      INil _ -> return e
      ICons _ v vs -> do
        r <- evalFoldList evalApp (recArgs vs)
        evalApp f [explicit v, explicit r]
      vs -> return $ mkExpr accessFoldList (recArgs vs)

    recArgs :: Value builtin -> FoldListArgs (Value builtin)
    recArgs = FoldListArgs a b f e

-----------------------------------------------------------------------------
-- Rational tensors

evalNegRatTensor :: (HasRatExpr Value builtin) => TensorOp1Args (Value builtin) -> Value builtin
evalNegRatTensor = evalTensorOp1 accessNegRatTensorBuiltin accessRatTensorLiteral (\x -> -x)

evalAddRatTensor :: (HasRatExpr Value builtin) => TensorOp2Args (Value builtin) -> Value builtin
evalAddRatTensor = evalTensorOp2 accessAddRatTensorBuiltin accessRatTensorLiteral (+) (Just 0) (Just 0)

evalMulRatTensor :: (HasRatExpr Value builtin) => TensorOp2Args (Value builtin) -> Value builtin
evalMulRatTensor = evalTensorOp2 accessMulRatTensorBuiltin accessRatTensorLiteral (*) (Just 1) (Just 1)

evalSubRatTensor :: (HasRatExpr Value builtin) => TensorOp2Args (Value builtin) -> Value builtin
evalSubRatTensor = evalTensorOp2 accessSubRatTensorBuiltin accessRatTensorLiteral (-) Nothing (Just 0)

evalDivRatTensor :: (HasRatExpr Value builtin) => TensorOp2Args (Value builtin) -> Value builtin
evalDivRatTensor = evalTensorOp2 accessDivRatTensorBuiltin accessRatTensorLiteral (/) Nothing (Just 1)

evalMinRatTensor :: (HasRatExpr Value builtin) => TensorOp2Args (Value builtin) -> Value builtin
evalMinRatTensor = evalTensorOp2 accessMinRatTensorBuiltin accessRatTensorLiteral min Nothing Nothing

evalMaxRatTensor :: (HasRatExpr Value builtin) => TensorOp2Args (Value builtin) -> Value builtin
evalMaxRatTensor = evalTensorOp2 accessMaxRatTensorBuiltin accessRatTensorLiteral max Nothing Nothing

evalPowRat ::
  (HasRatExpr Value builtin, BuiltinHasNatLiterals builtin) =>
  TensorOp2Args (Value builtin) ->
  Value builtin
evalPowRat = \case
  TensorOp2Args _ (IRatTensor xs) (INatLiteral n) -> IRatTensor (fmap (^^ n) xs)
  args -> mkExpr accessPowRatTensor args

evalReduceAddRatTensor :: (HasRatExpr Value builtin) => TensorReductionArgs (Value builtin) -> Value builtin
evalReduceAddRatTensor = evalReduceTensor accessReduceAddRatBuiltin accessRatTensorLiteral evalAddRatTensor (+)

evalReduceMulRatTensor :: (HasRatExpr Value builtin) => TensorReductionArgs (Value builtin) -> Value builtin
evalReduceMulRatTensor = evalReduceTensor accessReduceMulRatBuiltin accessRatTensorLiteral evalMulRatTensor (*)

evalReduceMinRatTensor :: (HasRatExpr Value builtin) => TensorReductionArgs (Value builtin) -> Value builtin
evalReduceMinRatTensor = evalReduceTensor accessReduceMinRatBuiltin accessRatTensorLiteral evalMinRatTensor min

evalReduceMaxRatTensor :: (HasRatExpr Value builtin) => TensorReductionArgs (Value builtin) -> Value builtin
evalReduceMaxRatTensor = evalReduceTensor accessReduceMaxRatBuiltin accessRatTensorLiteral evalMaxRatTensor max

evalEqualsRatTensor ::
  (HasBoolExpr Value builtin, HasRatExpr Value builtin, PrintableBuiltin builtin) =>
  EqualityOp ->
  TensorOp2Args (Value builtin) ->
  Value builtin
evalEqualsRatTensor op =
  evalHeteroTensorOp2
    (mkExpr accessEqRatTensorBuiltin op)
    accessRatTensorLiteral
    accessBoolTensorLiteral
    (equalityOp op)
    Nothing
    Nothing

evalOrderRatTensor ::
  (HasBoolExpr Value builtin, HasRatExpr Value builtin, PrintableBuiltin builtin) =>
  OrderOp ->
  TensorOp2Args (Value builtin) ->
  Value builtin
evalOrderRatTensor op =
  evalHeteroTensorOp2
    (mkExpr accessOrderRatTensorBuiltin op)
    accessRatTensorLiteral
    accessBoolTensorLiteral
    (orderOp op)
    Nothing
    Nothing

-----------------------------------------------------------------------------
-- Generic tensor operations

data TensorLiteralAccessor builtin
  = forall a. (Eq a) => Wrapper (Accessor (Value builtin) (Tensor a))

type TensorOp1EvalData builtin =
  ( TensorOp1Accessor (Value builtin),
    TensorOp1Args (Value builtin) -> Value builtin
  )

type TensorOp2EvalData builtin =
  ( TensorOp2Accessor (Value builtin),
    TensorOp2Args (Value builtin) -> Value builtin
  )

class HasPrimitives builtin where
  tensorLiterals :: [TensorLiteralAccessor builtin]
  tensorOp1s :: [TensorOp1EvalData builtin]
  tensorOp2s :: [TensorOp2EvalData builtin]

instance HasPrimitives Builtin where
  tensorLiterals =
    [ Wrapper accessBoolTensorLiteral,
      Wrapper accessNatTensorLiteral,
      Wrapper accessRatTensorLiteral,
      Wrapper accessIndexTensorLiteral
    ]

  tensorOp1s =
    [ (accessNegRatTensor, evalNegRatTensor),
      (accessNotTensor, evalNot)
    ]

  tensorOp2s :: [TensorOp2EvalData Builtin]
  tensorOp2s =
    [ (accessAddRatTensor, evalAddRatTensor),
      (accessMulRatTensor, evalMulRatTensor),
      (accessSubRatTensor, evalSubRatTensor),
      (accessDivRatTensor, evalDivRatTensor),
      (accessMinRatTensor, evalMinRatTensor),
      (accessMaxRatTensor, evalMaxRatTensor),
      (accessAndTensor, evalAnd),
      (accessOrTensor, evalOr)
    ]

instance HasPrimitives LossBuiltin where
  tensorLiterals =
    [ Wrapper accessNatTensorLiteral,
      Wrapper accessRatTensorLiteral,
      Wrapper accessIndexTensorLiteral
    ]

  tensorOp1s =
    [ (accessNegRatTensor, evalNegRatTensor)
    ]

  tensorOp2s =
    [ (accessAddRatTensor, evalAddRatTensor),
      (accessMulRatTensor, evalMulRatTensor),
      (accessSubRatTensor, evalSubRatTensor),
      (accessDivRatTensor, evalDivRatTensor),
      (accessMinRatTensor, evalMinRatTensor),
      (accessMaxRatTensor, evalMaxRatTensor)
    ]

evalAt ::
  forall builtin.
  (HasPrimitives builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorExpr Value builtin) =>
  AtArgs (Value builtin) ->
  Value builtin
evalAt args@(AtArgs t d ds tensor index) = do
  fromMaybe (mkExpr accessAtTensor args) $
    goOp1 tensorOp1s
      <|> goOp2 tensorOp2s
      <|> case index of
        IIndexLiteral i ->
          goLiterals i tensorLiterals
            <|> case tensor of
              (getExpr accessStackTensor -> Just stackArgs) -> Just $ stackElements stackArgs !! i
              (getExpr accessConstTensor -> Just constArgs) -> Just $ mkExpr accessConstTensor $ constArgs {constDims = argExpr ds}
              _ -> Nothing
        _ -> Nothing
  where
    recEvalAt :: Value builtin -> Value builtin
    recEvalAt ys = evalAt (AtArgs t d ds ys index)

    goOp1 :: [TensorOp1EvalData builtin] -> Maybe (Value builtin)
    goOp1 = \case
      (accessOp1, evalOp1) : remainingOp1s -> case getExpr accessOp1 tensor of
        Just (TensorOp1Args _ xs) -> Just $ evalOp1 $ TensorOp1Args ds $ recEvalAt xs
        _ -> goOp1 remainingOp1s
      [] -> Nothing

    goOp2 :: [TensorOp2EvalData builtin] -> Maybe (Value builtin)
    goOp2 = \case
      (accessOp2, evalOp2) : remainingOps2 -> case getExpr accessOp2 tensor of
        Just (TensorOp2Args _ xs ys) -> Just $ evalOp2 $ TensorOp2Args ds (recEvalAt xs) (recEvalAt ys)
        _ -> goOp2 remainingOps2
      _ -> Nothing

    goLiterals :: Int -> [TensorLiteralAccessor builtin] -> Maybe (Value builtin)
    goLiterals i literals = case literals of
      Wrapper Access {..} : remainingLiterals -> case getExpr tensor of
        Just xs -> Just $ mkExpr (xs `at` i)
        Nothing -> goLiterals i remainingLiterals
      _ -> Nothing

evalStackTensor ::
  (HasPrimitives builtin, BuiltinHasNatLiterals builtin, HasTensorExpr Value builtin) =>
  StackTensorArgs (Value builtin) ->
  Value builtin
evalStackTensor = evalStackTensorWithPrimitives tensorLiterals

evalStackTensorWithPrimitives ::
  (BuiltinHasNatLiterals builtin, HasTensorExpr Value builtin) =>
  [TensorLiteralAccessor builtin] ->
  StackTensorArgs (Value builtin) ->
  Value builtin
evalStackTensorWithPrimitives tensorLits args@(StackTensorArgs _t d ds xs) = fromMaybe (mkExpr accessStackTensor args) $
  -- If we know that all the tensors being stacked are concrete tensors, then
  -- we must know the dimensions as well.
  case (d, getDims (argExpr ds)) of
    (INatLiteral n, Just ns) | length xs == n -> go ns xs tensorLits
    _ -> Nothing
  where
    go :: [Int] -> [Value builtin] -> [TensorLiteralAccessor builtin] -> Maybe (Value builtin)
    go elemDims elements = \case
      Wrapper Access {..} : prims -> case traverse getExpr elements of
        Just xss -> Just $ mkExpr $ stack elemDims xss
        Nothing -> go elemDims elements prims
      [] -> Nothing

evalConstTensor ::
  forall builtin.
  (HasPrimitives builtin, BuiltinHasNatLiterals builtin, HasTensorExpr Value builtin) =>
  ConstTensorArgs (Value builtin) ->
  Value builtin
evalConstTensor args@(ConstTensorArgs _t xs ds) =
  -- Pattern matching on ds here is technically a bug as blocking will not
  -- function correctly. However, to fix it we would need to go via `StackTensor`
  -- and in particular make `StackTensor` take the size argument as an expression.
  -- Our type-system can't handle that easily yet.
  case (`go` tensorLiterals) =<< getDims ds of
    Just result -> result
    _ -> mkExpr accessConstTensor args
  where
    go :: [Int] -> [TensorLiteralAccessor builtin] -> Maybe (Value builtin)
    go dims = \case
      [] -> Nothing
      Wrapper Access {..} : prims -> case getExpr xs of
        Just t -> case t of
          ZeroDimTensor v -> Just $ mkExpr $ ConstantTensor dims v
          _ -> developerError "Non-zero dimensional tensor argument for ConstTensor"
        Nothing -> go dims prims

evalForeach ::
  (MonadLogger m, HasPrimitives builtin, HasTensorExpr Value builtin, BuiltinHasNatLiterals builtin, BuiltinHasIndexLiterals builtin, BuiltinHasForeach builtin) =>
  EvalApp builtin m ->
  ForeachArgs (Value builtin) ->
  m (Value builtin)
evalForeach evalApp args@(ForeachArgs t d ds f) = case d of
  INatLiteral n -> do
    xs <- traverse (\i -> evalApp f [explicit (IIndexLiteral i)]) [0 .. (n - 1 :: Int)]
    return $ evalStackTensor (StackTensorArgs t d ds xs)
  _ -> return $ mkExpr accessForeachTensor args

evalIterate ::
  (MonadLogger m, BuiltinHasNatLiterals builtin, BuiltinHasIterate builtin) =>
  EvalApp builtin m ->
  IterateArgs (Value builtin) ->
  m (Value builtin)
evalIterate evalApp args@(IterateArgs t f n e) = case n of
  INatLiteral 0 -> return e
  INatLiteral v -> do
    recResult <- evalIterate evalApp (IterateArgs t f (INatLiteral (v - 1)) e)
    evalApp f [explicit recResult, explicit e]
  _ -> return $ mkExpr accessIterate args

-----------------------------------------------------------------------------
-- Blocking arguments

data BlockingArgs
  = Unknown
  | Known [Int]

noBlockingArgs :: BlockingArgs
noBlockingArgs = Known []

blockingArgsNot :: BlockingArgs
blockingArgsNot = Known [1]

blockingArgsAnd :: BlockingArgs
blockingArgsAnd = Known [1, 2]

blockingArgsOr :: BlockingArgs
blockingArgsOr = Known [1, 2]

blockingArgsNeg :: NegDomain -> BlockingArgs
blockingArgsNeg = \case
  NegRatTensor -> Known [1]

blockingArgsAdd :: AddDomain -> BlockingArgs
blockingArgsAdd = \case
  AddNat -> Known [0, 1]
  AddRatTensor -> Known [1, 2]

blockingArgsMul :: MulDomain -> BlockingArgs
blockingArgsMul = \case
  MulNat -> Known [0, 1]
  MulRatTensor -> Known [1, 2]

blockingArgsSub :: SubDomain -> BlockingArgs
blockingArgsSub = \case
  SubRatTensor -> Known [1, 2]

blockingArgsDiv :: DivDomain -> BlockingArgs
blockingArgsDiv = \case
  DivRatTensor -> Known [1, 2]

blockingArgsMin :: MinDomain -> BlockingArgs
blockingArgsMin = \case
  MinRatTensor -> Known [1, 2]

blockingArgsMax :: MaxDomain -> BlockingArgs
blockingArgsMax = \case
  MaxRatTensor -> Known [1, 2]

blockingArgsEquals :: EqualityDomain -> BlockingArgs
blockingArgsEquals = \case
  EqIndex -> Known [2, 3]
  EqNat -> Known [0, 1]
  EqRatTensor -> Known [1, 2]

blockingArgsOrder :: OrderDomain -> BlockingArgs
blockingArgsOrder = \case
  OrderIndex -> Known [2, 3]
  OrderNat -> Known [0, 1]
  OrderRatTensor -> Known [1, 2]

functionBlockingArgs :: BuiltinFunction -> BlockingArgs
functionBlockingArgs = \case
  QuantifyRatTensor {} -> noBlockingArgs
  Not -> blockingArgsNot
  And -> blockingArgsAnd
  Or -> blockingArgsOr
  Neg dom -> blockingArgsNeg dom
  Add dom -> blockingArgsAdd dom
  Sub dom -> blockingArgsSub dom
  Mul dom -> blockingArgsMul dom
  Div dom -> blockingArgsDiv dom
  Min dom -> blockingArgsMin dom
  Max dom -> blockingArgsMax dom
  PowRat -> Known [0, 1]
  Equals dom _op -> blockingArgsEquals dom
  Order dom _op -> blockingArgsOrder dom
  FromNat FromNatToIndex -> Known [1]
  FromNat FromNatToNat -> Known [0]
  FromNat FromNatToRat -> Known [0]
  FromRat FromRatToRat -> noBlockingArgs
  If -> Known [1]
  At -> Known [3, 4]
  FoldList -> Known [4]
  MapList -> Known [3]
  Implies -> noBlockingArgs
  ConstTensor -> Known [0, 1]
  ReduceAddRatTensor -> Known [1]
  ReduceMulRatTensor -> Known [1]
  ReduceMinRatTensor -> Known [1]
  ReduceMaxRatTensor -> Known [1]
  ReduceOrTensor -> Known [1]
  ReduceAndTensor -> Known [1]
  Foreach -> Known [1]
  Iterate -> Known [2]
  StackTensor -> Unknown
  FromVectorToList -> Known [0]

-----------------------------------------------------------------------------
-- Type-class
-----------------------------------------------------------------------------

data EvalScheme builtin m
  = forall args. (IsArgs args) => Simple (args (Value builtin) -> Value builtin)
  | forall args. (IsArgs args) => NonSimple (EvalApp builtin m -> args (Value builtin) -> m (Value builtin))
  | None

-- | A type-class for builtins that can be normalised compositionally.
class (PrintableBuiltin builtin) => NormalisableBuiltin builtin where
  -- This function takes in the original expression (containing both relevant
  -- and irrelevant arguments), the builtin that is in the head position
  -- and the list of computationally relevant arguments.
  evalScheme :: (MonadLogger m) => builtin -> EvalScheme builtin m
  blockingArgs :: builtin -> BlockingArgs

evaluateBuiltin ::
  (MonadLogger m, NormalisableBuiltin builtin) =>
  EvalApp builtin m ->
  builtin ->
  Spine builtin ->
  m (Value builtin)
evaluateBuiltin evalApp b spine = case evalScheme b of
  Simple eval -> return $ maybe (VBuiltin b spine) eval (getExpr accessSpine spine)
  NonSimple eval -> maybe (return $ VBuiltin b spine) (eval evalApp) (getExpr accessSpine spine)
  None -> return $ VBuiltin b spine

instance NormalisableBuiltin Builtin where
  evalScheme = \case
    BuiltinFunction f -> case f of
      Equals EqNat op -> Simple (evalEqualsNat op)
      Equals EqIndex op -> Simple (evalEqualsIndex op)
      Equals EqRatTensor op -> Simple (evalEqualsRatTensor op)
      Order OrderNat op -> Simple (evalOrderNat op)
      Order OrderIndex op -> Simple (evalOrderNat op)
      Order OrderRatTensor op -> Simple (evalOrderRatTensor op)
      Not -> Simple evalNot
      And -> Simple evalAnd
      Or -> Simple evalOr
      Add AddNat -> Simple evalAddNat
      Mul MulNat -> Simple evalMulNat
      Neg NegRatTensor -> Simple evalNegRatTensor
      Add AddRatTensor -> Simple evalAddRatTensor
      Sub SubRatTensor -> Simple evalSubRatTensor
      Mul MulRatTensor -> Simple evalMulRatTensor
      Div DivRatTensor -> Simple evalDivRatTensor
      Min MinRatTensor -> Simple evalMinRatTensor
      Max MaxRatTensor -> Simple evalMaxRatTensor
      PowRat -> Simple evalPowRat
      ReduceAddRatTensor -> Simple evalReduceAddRatTensor
      ReduceMulRatTensor -> Simple evalReduceMulRatTensor
      ReduceMinRatTensor -> Simple evalReduceMinRatTensor
      ReduceMaxRatTensor -> Simple evalReduceMaxRatTensor
      ReduceAndTensor -> Simple evalReduceAndTensor
      ReduceOrTensor -> Simple evalReduceOrTensor
      FromNat FromNatToNat -> Simple evalFromNatToNat
      FromNat FromNatToIndex -> Simple evalFromNatToIndex
      FromNat FromNatToRat -> Simple evalFromNatToRat
      FromRat FromRatToRat -> Simple evalFromRatToRat
      FromVectorToList -> Simple evalVectorToList
      If -> Simple evalIf
      Implies -> Simple evalImplies
      At -> Simple evalAt
      StackTensor -> Simple evalStackTensor
      ConstTensor -> Simple evalConstTensor
      FoldList -> NonSimple evalFoldList
      MapList -> NonSimple evalMapList
      Foreach -> NonSimple evalForeach
      Iterate -> NonSimple evalIterate
      QuantifyRatTensor {} -> None
    _ -> None

  blockingArgs = \case
    BuiltinFunction f -> functionBlockingArgs f
    _ -> noBlockingArgs

instance NormalisableBuiltin LossBuiltin where
  evalScheme = \case
    LossBuiltinFunction f -> case f of
      L.Add AddNat -> Simple evalAddNat
      L.Mul MulNat -> Simple evalMulNat
      L.Neg NegRatTensor -> Simple evalNegRatTensor
      L.Add AddRatTensor -> Simple evalAddRatTensor
      L.Sub SubRatTensor -> Simple evalSubRatTensor
      L.Mul MulRatTensor -> Simple evalMulRatTensor
      L.Div DivRatTensor -> Simple evalDivRatTensor
      L.Min MinRatTensor -> Simple evalMinRatTensor
      L.Max MaxRatTensor -> Simple evalMaxRatTensor
      L.PowRat -> Simple evalPowRat
      L.ReduceAddRatTensor -> Simple evalReduceAddRatTensor
      L.ReduceMulRatTensor -> Simple evalReduceMulRatTensor
      L.ReduceMinRatTensor -> Simple evalReduceMinRatTensor
      L.ReduceMaxRatTensor -> Simple evalReduceMaxRatTensor
      L.At -> Simple evalAt
      L.StackTensor -> Simple evalStackTensor
      L.ConstTensor -> Simple evalConstTensor
      L.FoldList -> NonSimple evalFoldList
      L.MapList -> NonSimple evalMapList
      L.SearchRatTensor {} -> None
    _ -> None

  blockingArgs = developerError "Blocking arguments not yet implemented for LossBuiltin"

instance NormalisableBuiltin LinearityBuiltin where
  evalScheme b = notImplemented b
    where
      notImplemented = normNotImplemented "Linearity"

  blockingArgs = \case
    LinearityFunction f -> functionBlockingArgs f
    _ -> noBlockingArgs

instance NormalisableBuiltin PolarityBuiltin where
  evalScheme b = notImplemented b
    where
      notImplemented = normNotImplemented "Polarity"

  blockingArgs = \case
    PolarityFunction f -> functionBlockingArgs f
    _ -> noBlockingArgs

normNotImplemented :: (Pretty fn) => Doc () -> fn -> a
normNotImplemented typeSystem b =
  developerError $ "Normalisation of " <+> pretty b <+> "at the type-level not yet supported for" <+> typeSystem <+> "system"
