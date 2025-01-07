module Vehicle.Compile.Normalise.Builtin where

import Data.Maybe (maybeToList)
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
import Vehicle.Data.Tensor (Tensor, at, foldTensor, stack, zipWithTensor, pattern ConstantTensor, pattern ZeroDimTensor)

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

findInstanceArg :: (MonadLogger m, Show op) => op -> [GenericArg a] -> m (a, [GenericArg a])
findInstanceArg op = \case
  (InstanceArg _ _ inst : xs) -> return (inst, xs)
  (_ : xs) -> findInstanceArg op xs
  [] -> developerError $ "Malformed type class operation:" <+> pretty (show op)

filterOutIrrelevantArgs :: Spine builtin -> Spine builtin
filterOutIrrelevantArgs = filter isRelevant

-----------------------------------------------------------------------------
-- Builtin evaluation

-- | A method for evaluating an application.
-- Although there is only one implementation of this type, it needs to be
-- passed around as an argument to avoid dependency cycles between
-- this module and the module in which the general NBE algorithm lives in.
type EvalApp builtin m = Value builtin -> [VArg builtin] -> m (Value builtin)

--------------------------------------------------------------------------------
-- Evaluation

-- | A method for evaluating builtins that takes in an argument allowing the
-- recursive evaluation of applications. that takes in an argument allowing
-- the subsequent further evaluation of applications.
-- Such recursive evaluation is necessary when evaluating higher order
-- functions such as fold, map etc.
type EvalBuiltin builtin m =
  (MonadLogger m) =>
  EvalApp builtin m ->
  Value builtin ->
  Spine builtin ->
  m (Value builtin)

type EvalSimpleBuiltin builtin =
  Value builtin ->
  Spine builtin ->
  Value builtin

data Action1 builtin = forall a b.
  Action1
  { getter1 :: Destruct (Value builtin) a,
    setter1 :: Construct (Value builtin) b,
    app1 :: a -> b
  }

action1 :: Accessor expr a -> Accessor expr b -> (a -> b) -> Action1 expr
action1 get set = Action1 (getExpr get) (mkExpr set)

literalAction1 :: Accessor expr (Tensor a) -> (a -> a) -> Action1 expr
literalAction1 accessTensor f = action1 accessTensor accessTensor (fmap f)

constantAction1 :: (HasTensorPseudoConstructors expr) => (GenericArg expr -> expr -> expr) -> Action1 expr
constantAction1 f =
  action1
    accessConstTensor
    accessConstTensor
    (\(t, v, ds) -> (t, f (implicit ds) v, ds))

stackAction1 :: (HasTensorPseudoConstructors expr) => (GenericArg expr -> expr -> expr) -> Action1 expr
stackAction1 f =
  action1
    accessStackTensor
    accessStackTensor
    (\(t, d, ds, xs) -> (t, d, ds, explicit <$> fmap (f ds . argExpr) xs))

data Action2 builtin = forall a b c.
  Action2
  { getter21 :: Destruct (Value builtin) a,
    getter22 :: Destruct (Value builtin) b,
    setter2 :: Construct (Value builtin) c,
    app2 :: a -> b -> c
  }

action2 :: Accessor expr a -> Accessor expr b -> Accessor expr c -> (a -> b -> c) -> Action2 expr
action2 get1 get2 set = Action2 (getExpr get1) (getExpr get2) (mkExpr set)

literalAction2 :: Accessor expr (Tensor a) -> (a -> a -> a) -> Action2 expr
literalAction2 accessTensor f =
  action2
    accessTensor
    accessTensor
    accessTensor
    (zipWithTensor f)

constantAction2 :: (HasTensorPseudoConstructors expr) => (GenericArg expr -> expr -> expr -> expr) -> Action2 expr
constantAction2 f =
  action2
    accessConstTensor
    accessConstTensor
    accessConstTensor
    (\(t1, v1, ds1) (_t2, v2, _ds2) -> (t1, f (implicit ds1) v1 v2, ds1))

stackAction2 :: (HasTensorPseudoConstructors expr) => (GenericArg expr -> expr -> expr -> expr) -> Action2 expr
stackAction2 f =
  action2
    accessStackTensor
    accessStackTensor
    accessStackTensor
    (\(t1, d1, ds1, xs) (_t2, _d2, _ds2, ys) -> (t1, d1, ds1, explicit <$> zipWith (f ds1) (fmap argExpr xs) (fmap argExpr ys)))

leftUnitAction :: (HasTensorPseudoConstructors expr, Eq a) => Accessor expr (Tensor a) -> a -> Action2 expr
leftUnitAction accessTensor u = Action2 (constantMatching u (singleElement accessTensor)) Just id (\() e -> e)

rightUnitAction :: (HasTensorPseudoConstructors expr, Eq a) => Accessor expr (Tensor a) -> a -> Action2 expr
rightUnitAction accessTensor u = Action2 Just (constantMatching u (singleElement accessTensor)) id (\e () -> e)

evalOp1 ::
  forall builtin.
  [Action1 builtin] ->
  EvalSimpleBuiltin builtin
evalOp1 actions originalExpr args =
  case args of
    [argExpr -> x] -> go x actions
    _ -> originalExpr
  where
    go :: Value builtin -> [Action1 builtin] -> Value builtin
    go e = \case
      [] -> originalExpr
      Action1 {..} : as -> case getter1 e of
        Just x -> setter1 (app1 x)
        _ -> go e as

evalOp2 ::
  forall builtin.
  [Action2 builtin] ->
  EvalSimpleBuiltin builtin
evalOp2 actions originalExpr args =
  case args of
    [argExpr -> x, argExpr -> y] -> go x y actions
    _ -> originalExpr
  where
    go :: Value builtin -> Value builtin -> [Action2 builtin] -> Value builtin
    go e1 e2 = \case
      [] -> originalExpr
      Action2 {..} : as -> case (getter21 e1, getter22 e2) of
        (Just x, Just y) -> setter2 (app2 x y)
        _ -> go e1 e2 as

evalReduceTensor ::
  (HasTensorPseudoConstructors expr) =>
  TensorReductionAccessor expr ->
  Accessor expr (Tensor a) ->
  TensorOp2Accessor expr ->
  (a -> a -> a) ->
  EvalSimpleBuiltin builtin
evalReduceTensor accessReductionOp tensor accessBinaryOp tensorLiteralOp =
  evalOp2
    [ action2 tensor tensor tensor (foldTensor tensorLiteralOp),
      -- , Action2 Just (getExpr accessConstTensor) id $
      --     \e (t, v, ds) -> foldr (\x y -> mkExpr accessBinaryOp (_, x, y)) e _
      Action2 Just (getExpr accessStackTensor) id $
        \e (_d, ds, _t, xs) -> foldr (\x y -> mkExpr accessBinaryOp (ds, recEval ds e (argExpr x), y)) e xs
    ]
  where
    recEval ds e x = do
      let originalExpr = mkExpr accessReductionOp (ds, e, x)
      evalReduceTensor accessReductionOp tensor accessBinaryOp tensorLiteralOp originalExpr [ds, explicit e, explicit x]

-----------------------------------------------------------------------------
-- Individual builtin evaluation
-----------------------------------------------------------------------------
-- Bool

evalNotBoolTensor :: (HasBoolLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalNotBoolTensor =
  evalOp1
    [ action1 accessBoolTensorLiteral accessBoolTensorLiteral (fmap not),
      action1 accessConstTensor accessConstTensor (\(t, v, ds) -> (t, evalNot (implicit ds) v, ds)),
      action1 accessStackTensor accessStackTensor (\(t, d, ds, xs) -> (t, d, ds, fmap (fmap (evalNot ds)) xs))
    ]
  where
    evalNot ds x = evalNotBoolTensor (mkExpr accessNotTensor (ds, x)) [explicit x]

evalAndBoolTensor :: (HasBoolLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalAndBoolTensor =
  evalOp2
    [ literalAction2 accessBoolTensorLiteral (&&),
      constantAction2 evalAnd,
      stackAction2 evalAnd,
      leftUnitAction accessBoolTensorLiteral True,
      rightUnitAction accessBoolTensorLiteral True
    ]
  where
    evalAnd ds x y = evalAndBoolTensor (mkExpr accessAndTensor (ds, x, y)) [explicit x, explicit y]

evalOrBoolTensor :: (HasBoolLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalOrBoolTensor =
  evalOp2
    [ literalAction2 accessBoolTensorLiteral (||),
      constantAction2 evalOr,
      stackAction2 evalOr,
      leftUnitAction accessBoolTensorLiteral False,
      rightUnitAction accessBoolTensorLiteral False
    ]
  where
    evalOr ds x y = evalOrBoolTensor (mkExpr accessOrTensor (ds, x, y)) [explicit x, explicit y]

evalImplies :: (HasBoolLits expr) => EvalSimpleBuiltin builtin
evalImplies =
  evalOp2
    [ literalAction2 accessBoolTensorLiteral (\u v -> not u && v)
    ]

evalIf :: (HasBoolLits expr) => EvalSimpleBuiltin builtin
evalIf originalExpr = \case
  [argExpr -> IBoolLiteral True, e1, _e2] -> argExpr e1
  [argExpr -> IBoolLiteral False, _e1, e2] -> argExpr e2
  _ -> originalExpr

-----------------------------------------------------------------------------
-- Index

evalOrderIndex :: (HasBoolLits expr, BuiltinHasIndexLiterals builtin) => OrderOp -> EvalSimpleBuiltin builtin
evalOrderIndex op originalExpr = \case
  [_, _, argExpr -> IIndexLiteral x, argExpr -> IIndexLiteral y] -> IBoolLiteral (orderOp op x y)
  _ -> originalExpr

evalEqualsIndex :: (HasBoolLits expr, BuiltinHasIndexLiterals builtin) => EqualityOp -> EvalSimpleBuiltin builtin
evalEqualsIndex op originalExpr = \case
  [_, _, argExpr -> IIndexLiteral x, argExpr -> IIndexLiteral y] -> IBoolLiteral (equalityOp op x y)
  _ -> originalExpr

-----------------------------------------------------------------------------
-- Nat

evalAddNat :: (BuiltinHasNatLiterals builtin) => EvalSimpleBuiltin builtin
evalAddNat =
  evalOp2
    [ action2 accessNatLiteral accessNatLiteral accessNatLiteral (+)
    ]

evalMulNat :: (BuiltinHasNatLiterals builtin) => EvalSimpleBuiltin builtin
evalMulNat =
  evalOp2
    [ action2 accessNatLiteral accessNatLiteral accessNatLiteral (*)
    ]

evalOrderNat :: (HasBoolLits expr, BuiltinHasNatLiterals builtin) => OrderOp -> EvalSimpleBuiltin builtin
evalOrderNat op =
  evalOp2
    [ action2 accessNatLiteral accessNatLiteral (singleElement accessBoolTensorLiteral) (orderOp op)
    ]

evalEqualsNat :: (HasBoolLits expr, BuiltinHasNatLiterals builtin) => EqualityOp -> EvalSimpleBuiltin builtin
evalEqualsNat op =
  evalOp2
    [ action2 accessNatLiteral accessNatLiteral (singleElement accessBoolTensorLiteral) (equalityOp op)
    ]

evalFromNatToIndex :: (BuiltinHasIndexLiterals builtin, BuiltinHasNatLiterals builtin) => EvalSimpleBuiltin builtin
evalFromNatToIndex =
  evalOp1
    [ action1 accessNatLiteral accessIndexLiteral id
    ]

-----------------------------------------------------------------------------
-- Rat

evalFromNatToRat :: (HasRatLits expr, BuiltinHasNatLiterals builtin) => EvalSimpleBuiltin builtin
evalFromNatToRat =
  evalOp1
    [ action1 accessNatLiteral (singleElement accessRatTensorLiteral) fromIntegral
    ]

evalFromRatToRat :: EvalSimpleBuiltin builtin
evalFromRatToRat originalExpr = \case
  [argExpr -> x] -> x
  _ -> originalExpr

evalVectorToList :: (BuiltinHasNatLiterals builtin, BuiltinHasListLiterals builtin) => EvalSimpleBuiltin builtin
evalVectorToList originalExpr = \case
  (argExpr -> INatLiteral d) : (argExpr -> t) : xs
    | d /= length xs -> originalExpr
    | otherwise -> mkListExpr t (fmap argExpr xs)
  _ -> originalExpr

-----------------------------------------------------------------------------
-- List

evalMapList :: (BuiltinHasListLiterals builtin) => (Spine builtin -> expr) -> EvalBuiltin expr m
evalMapList mkMapList evalApp originalExpr = \case
  [_a, b, _f, argExpr -> INil _] -> return $ INil b
  [a, b, f, argExpr -> ICons _ x xs] -> do
    fx <- evalApp (argExpr f) [x]
    let defaultMap = mkMapList [a, b, f, xs]
    fxs <- evalMapList mkMapList evalApp defaultMap [a, b, f, xs]
    return $ ICons b (explicit fx) (explicit fxs)
  _ -> return originalExpr

evalFoldList :: EvalBuiltin (Value Builtin) m
evalFoldList evalApp originalExpr args =
  case args of
    [_a, _b, _f, e, argExpr -> INil _] -> return $ argExpr e
    [a, b, f, e, argExpr -> ICons _ x xs] -> do
      let defaultFold = VBuiltin (BuiltinFunction FoldList) [a, b, f, e, xs]
      r <- evalFoldList evalApp defaultFold [a, b, f, e, xs]
      evalApp (argExpr f) [x, explicit r]
    _ -> return originalExpr

-----------------------------------------------------------------------------
-- Rational tensors

evalRatTensorOp1 ::
  (HasRatLits expr, HasTensorPseudoConstructors expr) =>
  (Rational -> Rational) ->
  (TensorOp1Accessor expr, EvalSimpleBuiltin builtin) ->
  EvalSimpleBuiltin builtin
evalRatTensorOp1 ratOp (accessOp, ratExprOp) = do
  let evalExpr ds x = ratExprOp (mkExpr accessOp (ds, x)) [ds, explicit x]
  let literalAction = literalAction1 accessRatTensorLiteral ratOp
  let constAction = constantAction1 evalExpr
  let stackAction = stackAction1 evalExpr
  evalOp1 [literalAction, constAction, stackAction]

evalRatTensorOp2 ::
  (HasRatLits expr, HasTensorPseudoConstructors expr) =>
  (Rational -> Rational -> Rational) ->
  (TensorOp2Accessor expr, EvalSimpleBuiltin builtin) ->
  Maybe Rational ->
  Maybe Rational ->
  EvalSimpleBuiltin builtin
evalRatTensorOp2 ratOp (accessOp, ratExprOp) leftUnit rightUnit = do
  let evalExpr ds x y = ratExprOp (mkExpr accessOp (ds, x, y)) [ds, explicit x, explicit y]
  let literalAction = literalAction2 accessRatTensorLiteral ratOp
  let constAction = constantAction2 evalExpr
  let stackAction = stackAction2 evalExpr
  let lUnitAction = fmap (leftUnitAction accessRatTensorLiteral) leftUnit
  let rUnitAction = fmap (rightUnitAction accessRatTensorLiteral) rightUnit
  evalOp2 ([literalAction, constAction, stackAction] <> maybeToList lUnitAction <> maybeToList rUnitAction)

evalNegRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalNegRatTensor = evalRatTensorOp1 (\x -> -x) (accessNegRatTensor, evalNegRatTensor)

evalAddRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalAddRatTensor = evalRatTensorOp2 (+) (accessAddRatTensor, evalAddRatTensor) (Just 0) (Just 0)

evalMulRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalMulRatTensor = evalRatTensorOp2 (*) (accessMulRatTensor, evalMulRatTensor) (Just 1) (Just 1)

evalSubRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalSubRatTensor = evalRatTensorOp2 (-) (accessSubRatTensor, evalSubRatTensor) Nothing (Just 0)

evalDivRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalDivRatTensor = evalRatTensorOp2 (/) (accessDivRatTensor, evalDivRatTensor) Nothing (Just 1)

evalMinRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalMinRatTensor = evalRatTensorOp2 min (accessMinRatTensor, evalMinRatTensor) Nothing Nothing

evalMaxRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalMaxRatTensor = evalRatTensorOp2 max (accessMaxRatTensor, evalMaxRatTensor) Nothing Nothing

evalPowRat :: (BuiltinHasNatLiterals builtin, HasRatLits expr) => EvalSimpleBuiltin builtin
evalPowRat =
  evalOp2
    [ action2 accessRatTensorLiteral accessNatLiteral accessRatTensorLiteral (\t n -> fmap (^^ n) t)
    ]

evalReduceAddRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalReduceAddRatTensor = evalReduceTensor accessReduceAddRat accessRatTensorLiteral accessAddRatTensor (+)

evalReduceMulRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalReduceMulRatTensor = evalReduceTensor accessReduceMulRat accessRatTensorLiteral accessMulRatTensor (*)

evalReduceMinRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalReduceMinRatTensor = evalReduceTensor accessReduceMinRat accessRatTensorLiteral accessMinRatTensor min

evalReduceMaxRatTensor :: (HasRatLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalReduceMaxRatTensor = evalReduceTensor accessReduceMaxRat accessRatTensorLiteral accessMaxRatTensor max

evalEqualityRatTensor :: (HasBoolLits expr, HasRatLits expr) => EqualityOp -> EvalSimpleBuiltin builtin
evalEqualityRatTensor op =
  evalOp2
    [ action2 accessRatTensorLiteral accessRatTensorLiteral accessBoolTensorLiteral (zipWithTensor (equalityOp op))
    ]

evalOrderRatTensor :: (HasBoolLits expr, HasRatLits expr) => OrderOp -> EvalSimpleBuiltin builtin
evalOrderRatTensor op =
  evalOp2
    [ action2 accessRatTensorLiteral accessRatTensorLiteral accessBoolTensorLiteral (zipWithTensor (orderOp op))
    ]

evalReduceAndTensor :: (HasBoolLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalReduceAndTensor = evalReduceTensor accessReduceAnd accessBoolTensorLiteral accessAndTensor (&&)

evalReduceOrTensor :: (HasBoolLits expr, HasTensorPseudoConstructors expr) => EvalSimpleBuiltin builtin
evalReduceOrTensor = evalReduceTensor accessReduceOr accessBoolTensorLiteral accessOrTensor (||)

-----------------------------------------------------------------------------
-- Generic tensor operations

data TensorLiteralAccessor builtin = forall a. (Eq a) => Wrapper (Accessor (Value builtin) (Tensor a))

class HasPrimitives builtin where
  tensorLiterals :: [TensorLiteralAccessor builtin]
  tensorOp1s :: [(TensorOp1Accessor expr, EvalSimpleBuiltin builtin)]
  tensorOp2s :: [(TensorOp2Accessor expr, EvalSimpleBuiltin builtin)]

instance HasPrimitives Builtin where
  tensorLiterals =
    [ Wrapper accessBoolTensorLiteral,
      Wrapper accessNatTensorLiteral,
      Wrapper accessRatTensorLiteral,
      Wrapper accessIndexTensorLiteral
    ]

  tensorOp1s =
    [ (accessNegRatTensor, evalNegRatTensor),
      (accessNotTensor, evalNotBoolTensor)
    ]

  tensorOp2s =
    [ (accessAddRatTensor, evalAddRatTensor),
      (accessMulRatTensor, evalMulRatTensor),
      (accessSubRatTensor, evalSubRatTensor),
      (accessDivRatTensor, evalDivRatTensor),
      (accessMinRatTensor, evalMinRatTensor),
      (accessMaxRatTensor, evalMaxRatTensor),
      (accessAndTensor, evalAndBoolTensor),
      (accessOrTensor, evalOrBoolTensor)
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
  (HasPrimitives builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorPseudoConstructors expr) =>
  EvalSimpleBuiltin builtin
evalAt originalExpr args = case args of
  [tElem, _, argExpr -> t, argExpr -> i] -> goAbstract tElem t i tensorOp1s tensorOp2s
  _ -> originalExpr
  where
    goAbstract ::
      GenericArg expr ->
      expr ->
      expr ->
      [(TensorOp1Accessor expr, EvalSimpleBuiltin builtin)] ->
      [(TensorOp2Accessor expr, EvalSimpleBuiltin builtin)] ->
      expr
    goAbstract tElem tensor index op1s op2s =
      case op1s of
        (Access {..}, evalTOp1) : remainingOp1s -> case getExpr tensor of
          Just (argExpr -> ICons _ _ ds, xs) -> do
            let makeAt x i = explicit $ evaluateAt tElem ds x i
            evalTOp1 (mkExpr (ds, _)) [makeAt xs index]
          _ -> goAbstract tElem tensor index remainingOp1s op2s
        [] -> case op2s of
          (Access {..}, evalTOp2) : remainingOps2 -> case getExpr tensor of
            Just (ds, xs, ys) -> do
              let makeAt x i = explicit $ evaluateAt tElem ds x i
              evalTOp2 _ [makeAt xs index, makeAt ys index]
            Nothing -> goAbstract tElem tensor index op1s remainingOps2
          _ -> case index of
            IIndexLiteral i -> goConcrete tensor i tensorLiterals
            _ -> originalExpr

    goConcrete :: expr -> Int -> [TensorLiteralAccessor expr] -> expr
    goConcrete tensor i literals = case literals of
      Wrapper Access {..} : prims -> case getExpr tensor of
        Just t -> mkExpr (t `at` i)
        Nothing -> goConcrete tensor i prims
      _ -> case tensor of
        IStackTensor _ _ _ xs -> argExpr $ xs !! i
        IConstTensor t v (ICons _ _ ds) -> IConstTensor t v (argExpr ds)
        _ -> originalExpr

evaluateAt ::
  (HasPrimitives builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorPseudoConstructors expr) =>
  GenericArg expr ->
  GenericArg expr ->
  expr ->
  expr ->
  expr
evaluateAt tElem ds x i = evalAt (mkExpr accessAtTensor (tElem, ds, x, i)) [tElem, ds, explicit x, explicit i]

evalStackTensor :: (HasPrimitives builtin, BuiltinHasNatLiterals builtin, BuiltinHasListLiterals builtin) => EvalSimpleBuiltin builtin
evalStackTensor originalExpr = \case
  (argExpr -> INatLiteral n) : ds : _t : args
    | length args /= n -> originalExpr
    | otherwise -> do
        let exprs = fmap argExpr args
        -- If we know that all the tensors being stacked are concrete tensors, then
        -- we must know the dimensions as well.
        let dims = case getDims (argExpr ds) of
              Nothing -> developerError "Non-concrete dimensions for concrete tensor literals"
              Just r -> r
        go originalExpr dims exprs tensorLiterals
  _ -> originalExpr
  where
    go :: expr -> [Int] -> [expr] -> [TensorLiteralAccessor expr] -> expr
    go original elemDims args = \case
      Wrapper Access {..} : prims -> case traverse getExpr args of
        Just xss -> mkExpr $ stack elemDims xss
        Nothing -> go original elemDims args prims
      [] -> original

evalConstTensor :: (HasPrimitives builtin, BuiltinHasNatLiterals builtin, BuiltinHasListLiterals builtin) => EvalSimpleBuiltin builtin
evalConstTensor originalExpr = \case
  -- Pattern matching on ds here is technically a bug as blocking will not
  -- function correctly. However, to fix it we would need to go via `StackTensor`
  -- and in particular make `StackTensor` take the size argument as an expression.
  -- Our type-system can't handle that easily yet.
  [_tElem, argExpr -> tensorExpr, getDims . argExpr -> Just dims] -> go originalExpr tensorExpr dims tensorLiterals
  _ -> originalExpr
  where
    go :: expr -> expr -> [Int] -> [TensorLiteralAccessor expr] -> expr
    go original tensorExpr dims = \case
      [] -> original
      Wrapper Access {..} : prims -> case getExpr tensorExpr of
        Just t -> case t of
          ZeroDimTensor v -> mkExpr $ ConstantTensor dims v
          _ -> developerError "Non-zero dimensional tensor argument for ConstTensor"
        Nothing -> go original tensorExpr dims prims

evalForeach :: EvalBuiltin Builtin m
evalForeach evalApp originalExpr = \case
  [tElem, d@(argExpr -> INatLiteral n), ds, argExpr -> f] -> do
    xs <- traverse (\i -> evalApp f [explicit (IIndexLiteral i)]) [0 .. (n - 1 :: Int)]
    let args = d : ds : tElem : fmap explicit xs
    let newExpr = VBuiltin (BuiltinFunction StackTensor) args
    return $ evalStackTensor newExpr args
  _ -> return originalExpr

evalIterate :: (BuiltinHasNatLiterals builtin) => (Spine builtin -> Value builtin) -> EvalBuiltin builtin m
evalIterate mkIterate evalApp originalExpr = \case
  (t : f : (argExpr -> INatLiteral n) : e : _) -> case n of
    0 -> return $ argExpr e
    _ -> evalApp (argExpr f) [explicit (mkIterate [t, f, explicit (INatLiteral (n - 1))]), e]
  _ -> return originalExpr

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

-- | A type-class for builtins that can be normalised compositionally.
class (PrintableBuiltin builtin) => NormalisableBuiltin builtin where
  -- This function takes in the original expression (containing both relevant
  -- and irrelevant arguments), the builtin that is in the head position
  -- and the list of computationally relevant arguments.
  evalBuiltinApp ::
    (MonadLogger m) =>
    EvalApp (Value builtin) m ->
    FreeEnv builtin ->
    Value builtin ->
    builtin ->
    Spine builtin ->
    m (Value builtin)

  blockingArgs ::
    builtin ->
    BlockingArgs

-----------------------------------------------------------------------------
-- Eval domains

evalEquals :: (HasBoolLits expr, BuiltinHasIndexLiterals builtin, BuiltinHasNatLiterals builtin, HasRatLits expr) => EqualityDomain -> EqualityOp -> EvalSimpleBuiltin builtin
evalEquals = \case
  EqIndex -> evalEqualsIndex
  EqNat -> evalEqualsNat
  EqRatTensor -> evalEqualityRatTensor

evalOrder :: (HasBoolLits expr, BuiltinHasIndexLiterals builtin, BuiltinHasNatLiterals builtin, HasRatLits expr) => OrderDomain -> OrderOp -> EvalSimpleBuiltin builtin
evalOrder = \case
  OrderIndex -> evalOrderIndex
  OrderNat -> evalOrderNat
  OrderRatTensor -> evalOrderRatTensor

evalNeg :: (HasRatLits expr, HasTensorPseudoConstructors expr) => NegDomain -> EvalSimpleBuiltin builtin
evalNeg = \case
  NegRatTensor -> evalNegRatTensor

evalAdd :: (HasRatLits expr, BuiltinHasNatLiterals builtin, HasTensorPseudoConstructors expr) => AddDomain -> EvalSimpleBuiltin builtin
evalAdd = \case
  AddNat -> evalAddNat
  AddRatTensor -> evalAddRatTensor

evalSub :: (HasRatLits expr, HasTensorPseudoConstructors expr) => SubDomain -> EvalSimpleBuiltin builtin
evalSub = \case
  SubRatTensor -> evalSubRatTensor

evalMul :: (HasRatLits expr, BuiltinHasNatLiterals builtin, HasTensorPseudoConstructors expr) => MulDomain -> EvalSimpleBuiltin builtin
evalMul = \case
  MulNat -> evalMulNat
  MulRatTensor -> evalMulRatTensor

evalDiv :: (HasRatLits expr, HasTensorPseudoConstructors expr) => DivDomain -> EvalSimpleBuiltin builtin
evalDiv = \case
  DivRatTensor -> evalDivRatTensor

evalMin :: (HasRatLits expr, HasTensorPseudoConstructors expr) => MinDomain -> EvalSimpleBuiltin builtin
evalMin = \case
  MinRatTensor -> evalMinRatTensor

evalMax :: (HasRatLits expr, HasTensorPseudoConstructors expr) => MaxDomain -> EvalSimpleBuiltin builtin
evalMax = \case
  MaxRatTensor -> evalMaxRatTensor

evalBuiltinFunction :: BuiltinFunction -> EvalBuiltin (Value Builtin) m
evalBuiltinFunction b evalApp originalValue args = case b of
  QuantifyRatTensor {} -> return originalValue
  Equals dom op -> return $ evalEquals dom op originalValue args
  Order dom op -> return $ evalOrder dom op originalValue args
  Not -> return $ evalNotBoolTensor originalValue args
  And -> return $ evalAndBoolTensor originalValue args
  Or -> return $ evalOrBoolTensor originalValue args
  Neg dom -> return $ evalNeg dom originalValue args
  Add dom -> return $ evalAdd dom originalValue args
  Sub dom -> return $ evalSub dom originalValue args
  Mul dom -> return $ evalMul dom originalValue args
  Div dom -> return $ evalDiv dom originalValue args
  Min dom -> return $ evalMin dom originalValue args
  Max dom -> return $ evalMax dom originalValue args
  PowRat -> return $ evalPowRat originalValue args
  ReduceAddRatTensor -> return $ evalReduceAddRatTensor originalValue args
  ReduceMulRatTensor -> return $ evalReduceMulRatTensor originalValue args
  ReduceMinRatTensor -> return $ evalReduceMinRatTensor originalValue args
  ReduceMaxRatTensor -> return $ evalReduceMaxRatTensor originalValue args
  ReduceAndTensor -> return $ evalReduceAndTensor originalValue args
  ReduceOrTensor -> return $ evalReduceOrTensor originalValue args
  FromNat FromNatToIndex -> return $ evalFromNatToIndex originalValue args
  FromNat FromNatToRat -> return $ evalFromNatToRat originalValue args
  FromRat FromRatToRat -> return $ evalFromRatToRat originalValue args
  FromVectorToList -> return $ evalVectorToList originalValue args
  If -> return $ evalIf originalValue args
  FoldList -> evalFoldList evalApp originalValue args
  MapList -> evalMapList (VBuiltin $ BuiltinFunction MapList) evalApp originalValue args
  Implies -> return $ evalImplies originalValue args
  At -> return $ evalAt originalValue args
  StackTensor -> return $ evalStackTensor originalValue args
  ConstTensor -> return $ evalConstTensor originalValue args
  Foreach -> evalForeach evalApp originalValue args
  Iterate -> evalIterate (VBuiltin (BuiltinFunction Iterate)) evalApp originalValue args

instance NormalisableBuiltin Builtin where
  evalBuiltinApp evalApp _freeEnv originalExpr b normArgs =
    case getBuiltinFunction b of
      Nothing -> return originalExpr
      Just f -> evalBuiltinFunction f evalApp originalExpr normArgs

  blockingArgs = \case
    BuiltinFunction f -> functionBlockingArgs f
    _ -> noBlockingArgs

-----------------------------------------------------------------------------
-- Linearity

instance NormalisableBuiltin LinearityBuiltin where
  evalBuiltinApp _evalApp _freeEnv _originalValue b _args = notImplemented b
    where
      {-
      case b of
        SliceTensor -> notImplemented b
        FoldVector -> notImplemented b
        ZipWithVector -> notImplemented b
        MapList -> notImplemented b
        MapVector -> notImplemented b
        Indices -> notImplemented b
        Implies -> notImplemented b
        FoldList -> evalLinearityFoldList evalApp originalValue args
        _ -> evalBuiltinFunction b evalApp originalValue args
        -}

      notImplemented = normNotImplemented "Linearity"

  blockingArgs = \case
    LinearityFunction f -> functionBlockingArgs f
    _ -> noBlockingArgs

-- Need foldList at the type-level to evaluate the Tensor definition
evalLinearityFoldList :: EvalBuiltin (Value LinearityBuiltin) m
evalLinearityFoldList evalApp originalExpr args =
  case args of
    [_a, _b, _c, _f, e, argExpr -> VBuiltin (LinearityConstructor Nil) []] -> return $ argExpr e
    [a, b, c, f, e, argExpr -> VBuiltin (LinearityConstructor Cons) [_, _, _, _, x, xs]] -> do
      let defaultFold = VBuiltin (LinearityFunction FoldList) [a, b, c, f, e, xs]
      r <- evalLinearityFoldList evalApp defaultFold [a, b, c, f, e, xs]
      evalApp (argExpr f) [x, explicit r]
    _ -> return originalExpr

-----------------------------------------------------------------------------
-- Polarity

instance NormalisableBuiltin PolarityBuiltin where
  evalBuiltinApp _evalApp _freeEnv _originalValue b _args = notImplemented b
    where
      {-
        case b of
        SliceTensor -> notImplemented b
        FoldVector -> notImplemented b
        ZipWithVector -> notImplemented b
        MapList -> notImplemented b
        MapVector -> notImplemented b
        Indices -> notImplemented b
        Implies -> notImplemented b
        FoldList -> evalPolarityFoldList evalApp originalValue args
        _ -> evalBuiltinFunction b evalApp originalValue args
        -}

      notImplemented = normNotImplemented "Polarity"

  blockingArgs = \case
    PolarityFunction f -> functionBlockingArgs f
    _ -> noBlockingArgs

-- Need foldList at the type-level to evaluate the Tensor definition
evalPolarityFoldList :: EvalBuiltin (Value PolarityBuiltin) m
evalPolarityFoldList evalApp originalExpr args =
  case args of
    [_a, _b, _c, _f, e, argExpr -> VBuiltin (PolarityConstructor Nil) []] -> return $ argExpr e
    [a, b, c, f, e, argExpr -> VBuiltin (PolarityConstructor Cons) [_, _, _, _, x, xs]] -> do
      let defaultFold = VBuiltin (PolarityFunction FoldList) [a, b, c, f, e, xs]
      r <- evalPolarityFoldList evalApp defaultFold [a, b, c, f, e, xs]
      evalApp (argExpr f) [x, explicit r]
    _ -> return originalExpr

normNotImplemented :: (Pretty fn) => Doc () -> fn -> a
normNotImplemented typeSystem b = developerError $ "Normalisation of " <+> pretty b <+> "at the type-level not yet supported for" <+> typeSystem <+> "system"

-----------------------------------------------------------------------------
-- Loss

instance NormalisableBuiltin LossBuiltin where
  evalBuiltinApp _evalApp _freeEnv originalValue b args = case b of
    LossBuiltinConstructor {} -> return originalValue
    LossBuiltinType {} -> return originalValue
    LossBuiltinFunction f -> case f of
      L.Neg dom -> return $ evalNeg dom originalValue args
      L.Add dom -> return $ evalAdd dom originalValue args
      L.Sub dom -> return $ evalSub dom originalValue args
      L.Mul dom -> return $ evalMul dom originalValue args
      L.Div dom -> return $ evalDiv dom originalValue args
      L.Min dom -> return $ evalMin dom originalValue args
      L.Max dom -> return $ evalMax dom originalValue args
      L.PowRat -> return $ evalPowRat originalValue args
      L.ReduceAddRatTensor -> return $ evalReduceAddRatTensor originalValue args
      L.ReduceMulRatTensor -> return $ evalReduceMulRatTensor originalValue args
      L.ReduceMinRatTensor -> return $ evalReduceMinRatTensor originalValue args
      L.ReduceMaxRatTensor -> return $ evalReduceMaxRatTensor originalValue args
      L.At -> return $ evalAt originalValue args
      L.StackTensor -> return $ evalStackTensor originalValue args
      L.ConstTensor -> return $ evalConstTensor originalValue args
      L.SearchRatTensor {} -> return originalValue

  blockingArgs = developerError "Blocking arguments not yet implemented for LossBuiltin"
