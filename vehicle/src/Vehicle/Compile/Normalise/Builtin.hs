module Vehicle.Compile.Normalise.Builtin where

import Data.Maybe (isJust, maybeToList)
import Debug.Trace
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyVerbose)
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

findInstanceArg :: (MonadLogger m, Show op) => op -> [GenericArg a] -> m (a, [GenericArg a])
findInstanceArg op = \case
  (InstanceArg _ _ inst : xs) -> return (inst, xs)
  (_ : xs) -> findInstanceArg op xs
  [] -> developerError $ "Malformed type class operation:" <+> pretty (show op)

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
type EvalBuiltin args builtin m =
  (MonadLogger m) =>
  EvalApp builtin m ->
  args (Value builtin) ->
  m (Maybe (Value builtin))

type EvalSimpleBuiltin args builtin =
  args (Value builtin) ->
  Maybe (Value builtin)

class HasSimple builtin where
  evaluationPrimitives ::
    Builtin ->
    ( Accessor (Spine builtin) (args (Value builtin)),
      EvalSimpleBuiltin args builtin
    )

evaluateSimply :: (HasSimple builtin) => builtin -> [GenericArg builtin] -> Value builtin
evaluateSimply b args = do
  let (access, eval) = evaluationPrimitives b
  case eval access of
    Just result -> result result
    Nothing -> mkExpr access args

data Action1 builtin
  = forall a b.
  Action1
  { getter1 :: Destruct (Value builtin) a,
    setter1 :: Construct (Value builtin) b,
    app1 :: a -> b
  }

action1 :: Accessor (Value builtin) a -> Accessor (Value builtin) b -> (a -> b) -> Action1 builtin
action1 get set = Action1 (getExpr get) (mkExpr set)

literalAction1 :: Accessor (Value builtin) (Tensor a) -> (a -> a) -> Action1 builtin
literalAction1 accessTensor f = action1 accessTensor accessTensor (fmap f)

constantAction1 ::
  (HasTensorExpr Value builtin) =>
  (VArg builtin -> Value builtin -> Value builtin) ->
  Action1 builtin
constantAction1 f =
  action1
    accessConstTensor
    accessConstTensor
    (\(t, v, ds) -> (t, f (implicit ds) v, ds))

stackAction1 ::
  (HasTensorExpr Value builtin) =>
  (VArg builtin -> Value builtin -> Value builtin) ->
  Action1 builtin
stackAction1 f =
  action1
    accessStackTensor
    accessStackTensor
    (\(t, d, ds, xs) -> (t, d, ds, explicit <$> fmap (f ds . argExpr) xs))

{-
evalTensorOp1 ::
  forall builtin.
  [Action1 builtin] ->
  Accessor _ (TensorOp1Args builtin) ->
  Maybe (Value builtin)
evalTensorOp1 actions args = \case
  [] -> originalExpr
  Action1 {..} : as -> case getter1 e of
    Just x -> setter1 (app1 x)
    _ -> go e as
-}
evalTensorOp1 ::
  (HasRatExpr Value builtin, HasTensorExpr Value builtin) =>
  builtin ->
  (Rational -> Rational) ->
  EvalSimpleBuiltin TensorOp1Args builtin
evalTensorOp1 b ratOp (accessOp, ratExprOp) = do
  -- let evalExpr ds x = ratExprOp (mkExpr accessOp (ds, x)) [ds, explicit x]
  let literalAction = literalAction1 accessRatTensorLiteral ratOp
  let constAction = constantAction1 evalExpr
  let stackAction = stackAction1 evalExpr
  evalOp1 [literalAction, constAction, stackAction]

data Action2 builtin
  = forall a b c.
  Action2
  { getter21 :: Destruct (Value builtin) a,
    getter22 :: Destruct (Value builtin) b,
    setter2 :: Construct (Value builtin) c,
    app2 :: a -> b -> c
  }

action2 ::
  Accessor (Value builtin) a ->
  Accessor (Value builtin) b ->
  Accessor (Value builtin) c ->
  (a -> b -> c) ->
  Action2 builtin
action2 get1 get2 set = Action2 (getExpr get1) (getExpr get2) (mkExpr set)

literalAction2 :: Accessor (Value builtin) (Tensor a) -> (a -> a -> a) -> Action2 builtin
literalAction2 accessTensor f =
  action2
    accessTensor
    accessTensor
    accessTensor
    (zipWithTensor f)

constantMatching :: (HasTensorExpr Value builtin, Eq a, PrintableBuiltin builtin) => a -> Accessor (Value builtin) a -> Destruct (Value builtin) ()
constantMatching value access e = case getExpr accessConstTensor e of
  Just (_, b, _) -> case getExpr access b of
    Just v | v == value -> Just ()
    _ -> Nothing
  _ -> Nothing

singleElement :: (PrintableBuiltin builtin) => Accessor (Value builtin) (Tensor a) -> Accessor (Value builtin) a
singleElement accessTensor =
  Access
    { getExpr = \case
        (getExpr accessTensor -> Just (ZeroDimTensor v)) -> Just v
        _e -> Nothing,
      mkExpr = mkExpr accessTensor . ZeroDimTensor
    }

evalOp2 ::
  forall builtin.
  (PrintableBuiltin builtin) =>
  [Action2 builtin] ->
  EvalSimpleBuiltin _ builtin
evalOp2 actions originalExpr args =
  case filter isRelevant args of
    [argExpr -> x, argExpr -> y] -> do
      go x y actions
    _ -> originalExpr
  where
    go :: Value builtin -> Value builtin -> [Action2 builtin] -> Value builtin
    go e1 e2 = \case
      [] -> originalExpr
      Action2 {..} : as -> case (getter21 e1, getter22 e2) of
        (Just x, Just y) -> setter2 (app2 x y)
        _ -> go e1 e2 as

evalReduceTensor ::
  (HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  TensorReductionAccessor (Value builtin) ->
  Accessor (Value builtin) (Tensor a) ->
  BuiltinFunction ->
  (a -> a -> a) ->
  EvalSimpleBuiltin TensorOp2Args builtin
evalReduceTensor accessReductionOp tensor binaryOp tensorLiteralOp = do
  let (accessBinaryOp, evalBinaryOp) = _ binaryOp
  evalOp2
    [ action2 tensor tensor tensor (foldTensor tensorLiteralOp),
      -- , Action2 Just (getExpr accessConstTensor) id $
      --     \e (t, v, ds) -> foldr (\x y -> mkExpr accessBinaryOp (_, x, y)) e _
      Action2 Just (getExpr accessStackTensor) id $
        \e (_d, ds, _t, xs) -> foldr (foldFn e ds) e xs
    ]
  where
    recEval ds e x = do
      let originalExpr = mkExpr accessReductionOp (ds, e, x)
      evalReduceTensor accessReductionOp tensor binaryOp tensorLiteralOp originalExpr [ds, explicit e, explicit x]

    foldFn e ds x y = do
      let recResult = recEval ds e (argExpr x)
      evalBinaryOp (mkExpr accessBinaryOp (ds, recResult, y)) [ds, explicit recResult, explicit y]

evalTensorOp2 ::
  (HasTensorExpr Value builtin, PrintableBuiltin builtin, Eq a) =>
  builtin ->
  (Accessor (Value builtin) (Tensor a), a -> a -> a) ->
  Maybe a ->
  Maybe a ->
  EvalSimpleBuiltin _ builtin
evalTensorOp2 op (accessLit, literalOp) leftUnit rightUnit = do
  let evalExpr ds x y = ratExprOp (mkExpr accessOp (ds, x, y)) [ds, explicit x, explicit y]

  let litLitAction =
        action2 accessLit accessLit accessLit $
          zipWithTensor literalOp
  let litStackAction = Action2 (getExpr accessLit) (getExpr accessStackTensor) _ $
        \v (t, d, ds, xs) -> (t, d, ds, zipWith (evalExpr ds) (mkExpr accessLit <$> unstack v) (fmap argExpr xs))

  let constConstAction = action2 accessConstTensor accessConstTensor accessConstTensor $
        \(t1, v1, ds1) (_t2, v2, _ds2) -> (t1, evalExpr (implicit ds1) v1 v2, ds1)

  let stackLitAction = Action2 (getExpr accessStackTensor) (getExpr accessLit) _ $
        \(t, d, ds, xs) v -> (t, d, ds, zipWith (evalExpr ds) (fmap argExpr xs) (mkExpr accessLit <$> unstack v))
  let stackStackAction = action2 accessStackTensor accessStackTensor accessStackTensor $
        \(t1, d1, ds1, xs) (_t2, _d2, _ds2, ys) ->
          (t1, d1, ds1, explicit <$> zipWith (evalExpr ds1) (fmap argExpr xs) (fmap argExpr ys))

  let lUnitAction = flip fmap leftUnit $
        \u -> Action2 (constantMatching u (singleElement accessLit)) Just id (\() e -> e)
  let rUnitAction = flip fmap rightUnit $
        \u -> Action2 Just (constantMatching u (singleElement accessLit)) id (\e () -> e)

  evalOp2
    ( [ litLitAction,
        litStackAction,
        constConstAction,
        stackLitAction,
        stackStackAction
      ]
        <> maybeToList lUnitAction
        <> maybeToList rUnitAction
    )

-----------------------------------------------------------------------------
-- Individual builtin evaluation
-----------------------------------------------------------------------------
-- Bool

evalNotBoolTensor :: (HasBoolExpr Value builtin, HasTensorExpr Value builtin) => EvalSimpleBuiltin TensorOp1Args builtin
evalNotBoolTensor = evalTensorOp1 _ _ not

evalAndBoolTensor ::
  (HasBoolExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  EvalSimpleBuiltin TensorOp2Args builtin
evalAndBoolTensor = evalTensorOp2 And (accessBoolTensorLiteral, (&&)) (Just True) (Just True)

evalOrBoolTensor ::
  (HasBoolExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  EvalSimpleBuiltin TensorOp2Args builtin
evalOrBoolTensor = evalTensorOp2 Or (accessBoolTensorLiteral, (||)) (Just False) (Just False)

evalImplies :: (HasBoolExpr Value builtin, PrintableBuiltin builtin) => EvalSimpleBuiltin TensorOp2Args builtin
evalImplies = evalTensorOp2 Implies (accessBoolTensorLiteral, \u v -> not u && v) Nothing Nothing

evalIf :: (HasBoolExpr Value builtin) => EvalSimpleBuiltin IfArgs builtin
evalIf (IfArgs t c e1 e2) = case c of
  IBoolLiteral True -> Just argExpr e1
  IBoolLiteral False -> Just argExpr e2
  _ -> Nothing

-----------------------------------------------------------------------------
-- Index

evalOrderIndex :: (HasBoolExpr Value builtin, BuiltinHasIndexLiterals builtin) => OrderOp -> EvalSimpleBuiltin IndexComparisonArgs builtin
evalOrderIndex op originalExpr = \case
  [_, _, argExpr -> IIndexLiteral x, argExpr -> IIndexLiteral y] -> IBoolLiteral (orderOp op x y)
  _ -> originalExpr

evalEqualsIndex :: (HasBoolExpr Value builtin, BuiltinHasIndexLiterals builtin) => EqualityOp -> EvalSimpleBuiltin IndexComparisonArgs builtin
evalEqualsIndex op originalExpr = \case
  [_, _, argExpr -> IIndexLiteral x, argExpr -> IIndexLiteral y] -> IBoolLiteral (equalityOp op x y)
  _ -> originalExpr

-----------------------------------------------------------------------------
-- Nat

evalAddNat ::
  (BuiltinHasNatLiterals builtin, PrintableBuiltin builtin) => EvalSimpleBuiltin Op2Args builtin
evalAddNat =
  evalOp2
    [ action2 accessNatLiteral accessNatLiteral accessNatLiteral (+)
    ]

evalMulNat ::
  (BuiltinHasNatLiterals builtin, PrintableBuiltin builtin) => EvalSimpleBuiltin Op2Args builtin
evalMulNat =
  evalOp2
    [ action2 accessNatLiteral accessNatLiteral accessNatLiteral (*)
    ]

evalOrderNat ::
  (HasBoolExpr Value builtin, BuiltinHasNatLiterals builtin, PrintableBuiltin builtin) =>
  OrderOp ->
  EvalSimpleBuiltin Op2Args builtin
evalOrderNat op =
  evalOp2
    [ action2 accessNatLiteral accessNatLiteral (singleElement accessBoolTensorLiteral) (orderOp op)
    ]

evalEqualsNat ::
  (HasBoolExpr Value builtin, BuiltinHasNatLiterals builtin, PrintableBuiltin builtin) =>
  EqualityOp ->
  EvalSimpleBuiltin Op2Args builtin
evalEqualsNat op =
  evalOp2
    [ action2 accessNatLiteral accessNatLiteral (singleElement accessBoolTensorLiteral) (equalityOp op)
    ]

evalFromNatToNat ::
  (HasNatExpr Value builtin, BuiltinHasNatLiterals builtin) => EvalSimpleBuiltin _ builtin
evalFromNatToNat =
  evalOp1
    [ action1 accessNatLiteral accessNatLiteral id
    ]

evalFromNatToIndex ::
  (BuiltinHasIndexLiterals builtin, BuiltinHasNatLiterals builtin) => EvalSimpleBuiltin _ builtin
evalFromNatToIndex =
  evalOp1
    [ action1 accessNatLiteral accessIndexLiteral id
    ]

-----------------------------------------------------------------------------
-- Rat

evalFromNatToRat ::
  (HasRatExpr Value builtin, BuiltinHasNatLiterals builtin, PrintableBuiltin builtin) =>
  EvalSimpleBuiltin _ builtin
evalFromNatToRat =
  evalOp1
    [ action1 accessNatLiteral (singleElement accessRatTensorLiteral) fromIntegral
    ]

evalFromRatToRat :: EvalSimpleBuiltin _ builtin
evalFromRatToRat originalExpr = \case
  [argExpr -> x] -> x
  _ -> originalExpr

evalVectorToList ::
  (BuiltinHasNatLiterals builtin, BuiltinHasListLiterals builtin) =>
  EvalSimpleBuiltin _ builtin
evalVectorToList originalExpr = \case
  (argExpr -> INatLiteral d) : (argExpr -> t) : xs
    | d /= length xs -> originalExpr
    | otherwise -> mkListExpr t (fmap argExpr xs)
  _ -> originalExpr

-----------------------------------------------------------------------------
-- List

evalMapList ::
  (BuiltinHasListLiterals builtin) =>
  (Spine builtin -> Value builtin) ->
  EvalBuiltin _ builtin m
evalMapList mkMapList evalApp originalExpr = \case
  [_a, b, _f, argExpr -> INil _] -> return $ INil b
  [a, b, f, argExpr -> ICons _ x xs] -> do
    fx <- evalApp (argExpr f) [explicit x]
    let defaultMap = mkMapList [a, b, f, explicit xs]
    fxs <- evalMapList mkMapList evalApp defaultMap [a, b, f, explicit xs]
    return $ ICons b fx fxs
  _ -> return originalExpr

evalFoldList :: EvalBuiltin _ Builtin m
evalFoldList evalApp originalExpr args =
  case args of
    [_a, _b, _f, e, argExpr -> INil _] -> return $ argExpr e
    [a, b, f, e, argExpr -> ICons _ x xs] -> do
      let defaultFold = VBuiltin (BuiltinFunction FoldList) [a, b, f, e, explicit xs]
      r <- evalFoldList evalApp defaultFold [a, b, f, e, explicit xs]
      evalApp (argExpr f) [explicit x, explicit r]
    _ -> return originalExpr

-----------------------------------------------------------------------------
-- Rational tensors

evalNegRatTensor ::
  (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  EvalSimpleBuiltin TensorOp1Args builtin
evalNegRatTensor = evalRatTensorOp1 (\x -> -x) (accessNegRatTensor, evalNegRatTensor)

evalAddRatTensor ::
  (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  EvalSimpleBuiltin TensorOp2Args builtin
evalAddRatTensor = evalTensorOp2 (accessRatTensorLiteral, (+)) (accessAddRatTensor, evalAddRatTensor) (Just 0) (Just 0)

evalMulRatTensor ::
  (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) => EvalSimpleBuiltin TensorOp2Args builtin
evalMulRatTensor = evalTensorOp2 (accessRatTensorLiteral, (*)) (accessMulRatTensor, evalMulRatTensor) (Just 1) (Just 1)

evalSubRatTensor :: (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) => EvalSimpleBuiltin TensorOp2Args builtin
evalSubRatTensor = evalTensorOp2 (accessRatTensorLiteral, (-)) (accessSubRatTensor, evalSubRatTensor) Nothing (Just 0)

evalDivRatTensor :: (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) => EvalSimpleBuiltin TensorOp2Args builtin
evalDivRatTensor = evalTensorOp2 (accessRatTensorLiteral, (/)) (accessDivRatTensor, evalDivRatTensor) Nothing (Just 1)

evalMinRatTensor :: (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) => EvalSimpleBuiltin TensorOp2Args builtin
evalMinRatTensor = evalTensorOp2 (accessRatTensorLiteral, min) (accessMinRatTensor, evalMinRatTensor) Nothing Nothing

evalMaxRatTensor :: (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) => EvalSimpleBuiltin TensorOp2Args builtin
evalMaxRatTensor = evalTensorOp2 (accessRatTensorLiteral, max) (accessMaxRatTensor, evalMaxRatTensor) Nothing Nothing

evalPowRat :: (BuiltinHasNatLiterals builtin, HasRatExpr Value builtin, PrintableBuiltin builtin) => EvalSimpleBuiltin _ builtin
evalPowRat =
  evalOp2
    [ action2 accessRatTensorLiteral accessNatLiteral accessRatTensorLiteral (\t n -> fmap (^^ n) t)
    ]

evalReduceAddRatTensor ::
  (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  EvalSimpleBuiltin TensorReductionArgs builtin
evalReduceAddRatTensor = evalReduceTensor accessReduceAddRat accessRatTensorLiteral (accessAddRatTensor, evalAddRatTensor) (+)

evalReduceMulRatTensor ::
  (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  EvalSimpleBuiltin TensorReductionArgs builtin
evalReduceMulRatTensor = evalReduceTensor accessReduceMulRat accessRatTensorLiteral (accessMulRatTensor, evalMulRatTensor) (*)

evalReduceMinRatTensor ::
  (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  EvalSimpleBuiltin TensorReductionArgs builtin
evalReduceMinRatTensor = evalReduceTensor accessReduceMinRat accessRatTensorLiteral (accessMinRatTensor, evalMinRatTensor) min

evalReduceMaxRatTensor ::
  (HasRatExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  EvalSimpleBuiltin TensorReductionArgs builtin
evalReduceMaxRatTensor = evalReduceTensor accessReduceMaxRat accessRatTensorLiteral (accessMaxRatTensor, evalMaxRatTensor) max

evalEqualityRatTensor ::
  (HasBoolExpr Value builtin, HasRatExpr Value builtin, PrintableBuiltin builtin) =>
  EqualityOp ->
  EvalSimpleBuiltin TensorReductionArgs builtin
evalEqualityRatTensor op =
  evalOp2
    [ action2 accessRatTensorLiteral accessRatTensorLiteral accessBoolTensorLiteral (zipWithTensor (equalityOp op)),
      _
    ]

evalOrderRatTensor ::
  (HasBoolExpr Value builtin, HasRatExpr Value builtin, PrintableBuiltin builtin) =>
  OrderOp ->
  EvalSimpleBuiltin TensorOp2Args builtin
evalOrderRatTensor op =
  evalOp2
    [ action2 accessRatTensorLiteral accessRatTensorLiteral accessBoolTensorLiteral (zipWithTensor (orderOp op)),
      _
    ]

evalReduceAndTensor ::
  (HasBoolExpr Value Builtin, HasTensorExpr Value Builtin) =>
  EvalSimpleBuiltin TensorReductionArgs Builtin
evalReduceAndTensor = evalReduceTensor accessReduceAnd accessBoolTensorLiteral (accessAndTensor, evalAndBoolTensor) (&&)

evalReduceOrTensor ::
  (HasBoolExpr Value builtin, HasTensorExpr Value builtin, PrintableBuiltin builtin) =>
  EvalSimpleBuiltin TensorReductionArgs builtin
evalReduceOrTensor = evalReduceTensor accessReduceOr accessBoolTensorLiteral (accessOrTensor, evalOrBoolTensor) (||)

-----------------------------------------------------------------------------
-- Generic tensor operations

data TensorLiteralAccessor builtin = forall a. (Eq a) => Wrapper (Accessor (Value builtin) (Tensor a))

class HasPrimitives builtin where
  tensorLiterals :: [TensorLiteralAccessor builtin]
  tensorOp1s :: [builtin]
  tensorOp2s :: [builtin]

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
  (HasPrimitives builtin, BuiltinHasListLiterals builtin, BuiltinHasIndexLiterals builtin, HasTensorExpr Value builtin) =>
  EvalSimpleBuiltin AtArgs builtin
evalAt originalExpr args = case args of
  [tElem, _, argExpr -> t, argExpr -> i] -> goAbstract tElem t i tensorOp1s tensorOp2s
  _ -> originalExpr
  where
    goAbstract ::
      VArg builtin ->
      Value builtin ->
      Value builtin ->
      [(TensorOp1Accessor (Value builtin), EvalSimpleBuiltin _ builtin)] ->
      [(TensorOp2Accessor (Value builtin), EvalSimpleBuiltin _ builtin)] ->
      Value builtin
    goAbstract tElem tensor index op1s op2s =
      case op1s of
        (Access {..}, evalTOp1) : remainingOp1s -> case getExpr tensor of
          Just (argExpr -> ICons _ d ds, xs) -> do
            let makeAt = evaluateAt tElem d ds
            let xsi = makeAt xs index
            evalTOp1 (mkExpr (implicitIrrelevant ds, xsi)) [explicit xsi]
          _ -> goAbstract tElem tensor index remainingOp1s op2s
        [] -> case op2s of
          (Access {..}, evalTOp2) : remainingOps2 -> case getExpr tensor of
            Just (argExpr -> ICons _ d ds, xs, ys) -> do
              let makeAt = evaluateAt tElem d ds
              let xsi = makeAt xs index
              let ysi = makeAt ys index
              evalTOp2 (mkExpr (implicitIrrelevant ds, xsi, ysi)) [explicit xsi, explicit ysi]
            _ -> goAbstract tElem tensor index op1s remainingOps2
          _ -> case index of
            IIndexLiteral i -> goConcrete tensor i tensorLiterals
            _ -> originalExpr

    goConcrete :: Value builtin -> Int -> [TensorLiteralAccessor builtin] -> Value builtin
    goConcrete tensor i literals = case literals of
      Wrapper Access {..} : prims -> case getExpr tensor of
        Just t -> mkExpr (t `at` i)
        Nothing -> goConcrete tensor i prims
      _ -> case tensor of
        _ -> _ -- IStackTensor _ _ _ xs -> argExpr $ xs !! i
        _ -> _ -- IConstTensor t v (ICons _ _ ds) -> IConstTensor t v ds
        _ -> originalExpr

evalStackTensor ::
  (HasPrimitives builtin, BuiltinHasNatLiterals builtin, BuiltinHasListLiterals builtin) =>
  EvalSimpleBuiltin StackTensorArgs builtin
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
    go :: Value builtin -> [Int] -> [Value builtin] -> [TensorLiteralAccessor builtin] -> Value builtin
    go original elemDims args = \case
      Wrapper Access {..} : prims -> case traverse getExpr args of
        Just xss -> mkExpr $ stack elemDims xss
        Nothing -> go original elemDims args prims
      [] -> original

evalConstTensor ::
  (HasPrimitives builtin, BuiltinHasNatLiterals builtin, BuiltinHasListLiterals builtin) =>
  EvalSimpleBuiltin ConstTensorArgs builtin
evalConstTensor originalExpr = \case
  -- Pattern matching on ds here is technically a bug as blocking will not
  -- function correctly. However, to fix it we would need to go via `StackTensor`
  -- and in particular make `StackTensor` take the size argument as an expression.
  -- Our type-system can't handle that easily yet.
  [_tElem, argExpr -> tensorExpr, getDims . argExpr -> Just dims] -> go originalExpr tensorExpr dims tensorLiterals
  _ -> originalExpr
  where
    go :: Value builtin -> Value builtin -> [Int] -> [TensorLiteralAccessor builtin] -> Value builtin
    go original tensorExpr dims = \case
      [] -> original
      Wrapper Access {..} : prims -> case getExpr tensorExpr of
        Just t -> case t of
          ZeroDimTensor v -> mkExpr $ ConstantTensor dims v
          _ -> developerError "Non-zero dimensional tensor argument for ConstTensor"
        Nothing -> go original tensorExpr dims prims

evalForeach :: EvalBuiltin ForeachArgs Builtin m
evalForeach evalApp originalExpr = \case
  [tElem, d@(argExpr -> INatLiteral n), ds, argExpr -> f] -> do
    xs <- traverse (\i -> evalApp f [explicit (IIndexLiteral i)]) [0 .. (n - 1 :: Int)]
    let args = d : ds : tElem : fmap explicit xs
    let newExpr = VBuiltin (BuiltinFunction StackTensor) args
    return $ evalStackTensor newExpr args
  _ -> return originalExpr

evalIterate :: (BuiltinHasNatLiterals builtin) => (Spine builtin -> Value builtin) -> EvalBuiltin _ builtin m
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

-- | A type-class for builtins that can be normalised compositionally.
class (PrintableBuiltin builtin) => NormalisableBuiltin builtin where
  -- This function takes in the original expression (containing both relevant
  -- and irrelevant arguments), the builtin that is in the head position
  -- and the list of computationally relevant arguments.
  evalBuiltinApp ::
    (MonadLogger m) =>
    EvalApp builtin m ->
    Value builtin ->
    builtin ->
    Spine builtin ->
    m (Value builtin)

  blockingArgs ::
    builtin ->
    BlockingArgs

-----------------------------------------------------------------------------
-- Eval domains

instance HasSimple Builtin where
  evaluationPrimitives b = case b of
    Equals dom op -> (_, evalEquals dom op)
    Order dom op -> return $ evalOrder dom op originalValue args
    Not -> (accessNotTensor, evalNotBoolTensor)
    And -> (_, evalAndBoolTensor)
    Or -> (_, evalOrBoolTensor)
    Neg dom -> (accessNegRatTensor, evalNeg dom)
    Add dom -> (accessAddRatTensor, evalAdd dom)
    Sub dom -> (accessSubRatTensor, evalSub dom)
    Mul dom -> (accessMulRatTensor, evalMul dom)
    Div dom -> (accessDivRatTensor, evalDiv dom)
    Min dom -> (accessMinRatTensor, evalMin dom)
    Max dom -> (accessMaxRatTensor, evalMax dom)
    PowRat -> (_, evalPowRat)
    ReduceAddRatTensor -> (_, evalReduceAddRatTensor)
    ReduceMulRatTensor -> (_, evalReduceMulRatTensor)
    ReduceMinRatTensor -> (_, evalReduceMinRatTensor)
    ReduceMaxRatTensor -> (_, evalReduceMaxRatTensor)
    ReduceAndTensor -> (_, evalReduceAndTensor)
    ReduceOrTensor -> (_, evalReduceOrTensor)
    FromNat FromNatToNat -> (_, evalFromNatToNat)
    FromNat FromNatToIndex -> (_, evalFromNatToIndex)
    FromNat FromNatToRat -> (_, evalFromNatToRat)
    FromRat FromRatToRat -> (_, evalFromRatToRat)
    FromVectorToList -> (_, evalVectorToList)
    If -> (_, evalIf)
    Implies -> (_, evalImplies)
    At -> (_, evalAt)
    StackTensor -> (_, evalStackTensor)
    ConstTensor -> (_, evalConstTensor)
    QuantifyRatTensor {} -> return originalValue
    FoldList -> evalFoldList evalApp originalValue args
    MapList -> evalMapList (VBuiltin $ BuiltinFunction MapList) evalApp originalValue args
    Foreach -> evalForeach evalApp originalValue args
    Iterate -> evalIterate (VBuiltin (BuiltinFunction Iterate)) evalApp originalValue args
      where
        nonSimple = _

instance NormalisableBuiltin Builtin where
  evalBuiltinApp evalApp b normArgs =
    case getBuiltinFunction b of
      Nothing -> return originalExpr
      Just f -> case f of
        QuantifyRatTensor {} -> return originalValue
        FoldList -> evalFoldList evalApp originalValue args
        MapList -> evalMapList (VBuiltin $ BuiltinFunction MapList) evalApp originalValue args
        Foreach -> evalForeach evalApp originalValue args
        Iterate -> evalIterate (VBuiltin (BuiltinFunction Iterate)) evalApp originalValue args
        _ -> evaluateSimply b args

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
evalLinearityFoldList :: EvalBuiltin _ LinearityBuiltin m
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
evalPolarityFoldList :: EvalBuiltin _ PolarityBuiltin m
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
