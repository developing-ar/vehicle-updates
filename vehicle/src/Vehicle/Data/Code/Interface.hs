module Vehicle.Data.Code.Interface where

import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Tensor
import Vehicle.Prelude

--------------------------------------------------------------------------------
-- Interface to standard builtins
--------------------------------------------------------------------------------

class HasBuiltinConstructor expr where
  accessBuiltinConstructor :: Accessor (expr builtin) (builtin, [GenericArg (expr builtin)])

mkBuiltin ::
  (HasBuiltinConstructor expr) =>
  Accessor builtin a ->
  a ->
  [GenericArg (expr builtin)] ->
  expr builtin
mkBuiltin accessBuiltin v args = mkExpr accessBuiltinConstructor (mkExpr accessBuiltin v, args)

getBuiltin ::
  (HasBuiltinConstructor expr) =>
  Accessor builtin a ->
  expr builtin ->
  Maybe (a, [GenericArg (expr builtin)])
getBuiltin accessBuiltin e = case getExpr accessBuiltinConstructor e of
  Just (b, args) -> case getExpr accessBuiltin b of
    Just v -> Just (v, args)
    _ -> Nothing
  _ -> Nothing

-- At various points in the compiler, we have different sets of builtins (e.g.
-- first time we type-check we use the standard set of builtins + type +
-- type classes, but when checking polarity and linearity information we
-- subsitute out all the types and type-classes for new types.)
--
-- The interfaces defined in this file allow us to abstract over the exact set
-- of builtins being used, and therefore allows us to define operations
-- (e.g. normalisation) once, rather than once for each builtin type.

type Op1Accessor expr = Accessor expr expr

type Op2Accessor expr = Accessor expr (expr, expr)

type TensorOp1Accessor expr = Accessor expr (GenericArg expr, expr)

type TensorOp2Accessor expr = Accessor expr (GenericArg expr, expr, expr)

type TensorReductionAccessor expr = Accessor expr (GenericArg expr, expr, expr)

singleElement :: Accessor expr (Tensor a) -> Accessor expr a
singleElement accessTensor =
  Access
    { getExpr = \case
        (getExpr accessTensor -> Just (ZeroDimTensor v)) -> Just v
        _ -> Nothing,
      mkExpr = mkExpr accessTensor . ZeroDimTensor
    }

noArgs ::
  (HasBuiltinConstructor expr) =>
  Accessor builtin a ->
  Accessor (expr builtin) a
noArgs access =
  Access
    { getExpr = \case
        (getBuiltin access -> Just (b, [])) -> Just b
        _ -> Nothing,
      mkExpr = \b -> mkBuiltin access b []
    }

op1Args :: (HasBuiltinConstructor expr) => Accessor builtin () -> Op1Accessor (expr builtin)
op1Args access =
  Access
    { getExpr = \case
        (getBuiltin access -> Just ((), [xs])) -> Just (argExpr xs)
        _ -> Nothing,
      mkExpr = \xs -> mkBuiltin access () [explicit xs]
    }

op2Args :: (HasBuiltinConstructor expr) => Accessor builtin () -> Op2Accessor (expr builtin)
op2Args access =
  Access
    { getExpr = \case
        (getBuiltin access -> Just ((), [xs, ys])) -> Just (argExpr xs, argExpr ys)
        _ -> Nothing,
      mkExpr = \(xs, ys) -> mkBuiltin access () [explicit xs, explicit ys]
    }

tensorOp1Args ::
  (HasBuiltinConstructor expr) =>
  Accessor builtin () ->
  TensorOp1Accessor (expr builtin)
tensorOp1Args access =
  Access
    { getExpr = \case
        (getBuiltin access -> Just ((), [ds, xs])) -> Just (ds, argExpr xs)
        _ -> Nothing,
      mkExpr = \(ds, xs) -> mkBuiltin access () [ds, explicit xs]
    }

tensorOp2Args ::
  (HasBuiltinConstructor expr) =>
  Accessor builtin () ->
  TensorOp2Accessor (expr builtin)
tensorOp2Args access =
  Access
    { getExpr = \case
        (getBuiltin access -> Just ((), [ds, xs, ys])) -> Just (ds, argExpr xs, argExpr ys)
        _ -> Nothing,
      mkExpr = \(ds, xs, ys) -> mkBuiltin access () [ds, explicit xs, explicit ys]
    }

tensorReductionArgs ::
  (HasBuiltinConstructor expr) =>
  Accessor builtin () ->
  TensorReductionAccessor (expr builtin)
tensorReductionArgs access =
  Access
    { getExpr = \case
        (getBuiltin access -> Just ((), [ds, e, xs])) -> Just (ds, argExpr e, argExpr xs)
        _ -> Nothing,
      mkExpr = \(ds, e, xs) -> mkBuiltin access () [ds, explicit e, explicit xs]
    }

--------------------------------------------------------------------------------
-- Boolean operations
--------------------------------------------------------------------------------

type HasBoolExpr expr builtin = (HasBuiltinConstructor expr, BuiltinHasBoolLiterals builtin)

accessBoolTensorLiteral :: (HasBoolExpr expr builtin) => Accessor (expr builtin) BoolTensor
accessBoolTensorLiteral = noArgs accessBoolTensorLitBuiltin

accessNotTensor :: (HasBoolExpr expr builtin) => TensorOp1Accessor (expr builtin)
accessNotTensor = tensorOp1Args accessNotBuiltin

accessAndTensor :: (HasBoolExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessAndTensor = tensorOp2Args accessAndBuiltin

accessOrTensor :: (HasBoolExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessOrTensor = tensorOp2Args accessOrBuiltin

accessImpliesTensor :: (HasBoolExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessImpliesTensor = tensorOp2Args accessImpliesBuiltin

accessReduceAnd :: (HasBoolExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceAnd = tensorReductionArgs accessReduceAndBuiltin

accessReduceOr :: (HasBoolExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceOr = tensorReductionArgs accessReduceOrBuiltin

accessIf :: (HasBoolExpr expr builtin) => Accessor (expr builtin) (GenericArg (expr builtin), expr builtin, expr builtin, expr builtin)
accessIf =
  Access
    { getExpr = \case
        (getBuiltin accessIfBuiltin -> Just ((), [t, c, x, y])) -> Just (t, argExpr c, argExpr x, argExpr y)
        _ -> Nothing,
      mkExpr = \(t, c, x, y) -> mkBuiltin accessIfBuiltin () [t, explicit c, explicit x, explicit y]
    }

pattern IBoolTensorLiteral :: (HasBoolExpr expr builtin) => BoolTensor -> expr builtin
pattern IBoolTensorLiteral n <- (getExpr accessBoolTensorLiteral -> Just n)
  where
    IBoolTensorLiteral n = mkExpr accessBoolTensorLiteral n

pattern IBoolLiteral :: (HasBoolExpr expr builtin) => Bool -> expr builtin
pattern IBoolLiteral n = IBoolTensorLiteral (ZeroDimTensor n)

--------------------------------------------------------------------------------
-- Indices

type HasIndexExpr expr builtin = (HasBuiltinConstructor expr, BuiltinHasIndexLiterals builtin)

accessIndexLiteral :: (HasIndexExpr expr builtin) => Accessor (expr builtin) Int
accessIndexLiteral = noArgs accessIndexLitBuiltin

accessIndexTensorLiteral :: (HasIndexExpr expr builtin) => Accessor (expr builtin) IndexTensor
accessIndexTensorLiteral = noArgs accessIndexTensorLitBuiltin

pattern IIndexLiteral :: (HasIndexExpr expr builtin) => Int -> expr builtin
pattern IIndexLiteral n <- (getExpr accessIndexLiteral -> Just n)
  where
    IIndexLiteral n = mkExpr accessIndexLiteral n

pattern IIndexTensor :: (HasIndexExpr expr builtin) => Tensor Int -> expr builtin
pattern IIndexTensor n <- (getExpr accessIndexTensorLiteral -> Just n)
  where
    IIndexTensor n = mkExpr accessIndexTensorLiteral n

--------------------------------------------------------------------------------
-- Naturals

type HasNatExpr expr builtin = (HasBuiltinConstructor expr, BuiltinHasNatLiterals builtin)

accessNatLiteral :: (HasNatExpr expr builtin) => Accessor (expr builtin) Int
accessNatLiteral = noArgs accessNatLitBuiltin

accessNatTensorLiteral :: (HasNatExpr expr builtin) => Accessor (expr builtin) NatTensor
accessNatTensorLiteral = noArgs accessNatTensorLitBuiltin

accessAddNat :: (HasNatExpr expr builtin) => Op2Accessor (expr builtin)
accessAddNat = op2Args accessAddNatBuiltin

accessMulNat :: (HasNatExpr expr builtin) => Op2Accessor (expr builtin)
accessMulNat = op2Args accessMulNatBuiltin

pattern INatLiteral :: (HasNatExpr expr builtin) => Int -> expr builtin
pattern INatLiteral n <- (getExpr accessNatLiteral -> Just n)
  where
    INatLiteral n = mkExpr accessNatLiteral n

pattern INatTensor :: (HasNatExpr expr builtin) => Tensor Int -> expr builtin
pattern INatTensor n <- (getExpr accessNatTensorLiteral -> Just n)
  where
    INatTensor n = mkExpr accessNatTensorLiteral n

--------------------------------------------------------------------------------
-- Rationals

type HasRatExpr expr builtin = (HasBuiltinConstructor expr, BuiltinHasRatLiterals builtin)

accessRatTensorLiteral :: (HasRatExpr expr builtin) => Accessor (expr builtin) RatTensor
accessRatTensorLiteral = noArgs accessRatTensorLitBuiltin

accessNegRatTensor :: (HasRatExpr expr builtin) => TensorOp1Accessor (expr builtin)
accessNegRatTensor = tensorOp1Args accessNegRatTensorBuiltin

accessAddRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessAddRatTensor = tensorOp2Args accessAddRatTensorBuiltin

accessMulRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessMulRatTensor = tensorOp2Args accessMulRatTensorBuiltin

accessSubRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessSubRatTensor = tensorOp2Args accessSubRatTensorBuiltin

accessDivRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessDivRatTensor = tensorOp2Args accessDivRatTensorBuiltin

accessMinRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessMinRatTensor = tensorOp2Args accessMinRatTensorBuiltin

accessMaxRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessMaxRatTensor = tensorOp2Args accessMaxRatTensorBuiltin

accessReduceAddRat :: (HasRatExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceAddRat = tensorReductionArgs accessReduceAddRatBuiltin

accessReduceMulRat :: (HasRatExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceMulRat = tensorReductionArgs accessReduceMulRatBuiltin

accessReduceMinRat :: (HasRatExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceMinRat = tensorReductionArgs accessReduceMinRatBuiltin

accessReduceMaxRat :: (HasRatExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceMaxRat = tensorReductionArgs accessReduceMaxRatBuiltin

pattern IRatTensor :: (HasRatExpr expr builtin) => Tensor Rational -> expr builtin
pattern IRatTensor n <- (getExpr accessRatTensorLiteral -> Just n)
  where
    IRatTensor n = mkExpr accessRatTensorLiteral n

pattern IRatLiteral :: (HasRatExpr expr builtin) => Rational -> expr builtin
pattern IRatLiteral n = IRatTensor (ZeroDimTensor n)

--------------------------------------------------------------------------------
-- Lists

type HasListExpr expr builtin = (HasBuiltinConstructor expr, BuiltinHasListLiterals builtin)

accessNil ::
  (HasListExpr expr builtin) =>
  Accessor (expr builtin) (GenericArg (expr builtin))
accessNil = do
  Access
    { getExpr = \case
        (getBuiltin accessNilBuiltin -> Just ((), [t])) -> Just t
        _ -> Nothing,
      mkExpr = \t -> mkBuiltin accessNilBuiltin () [t]
    }

accessCons ::
  (HasListExpr expr builtin) =>
  Accessor (expr builtin) (GenericArg (expr builtin), GenericArg (expr builtin), GenericArg (expr builtin))
accessCons =
  Access
    { getExpr = \case
        (getBuiltin accessConsBuiltin -> Just ((), [t, x, xs])) -> Just (t, x, xs)
        _ -> Nothing,
      mkExpr = \(t, x, xs) -> mkBuiltin accessConsBuiltin () [t, x, xs]
    }

pattern INil ::
  (HasListExpr expr builtin) =>
  GenericArg (expr builtin) ->
  expr builtin
pattern INil t <- (getExpr accessNil -> Just t)
  where
    INil t = mkExpr accessNil t

pattern ICons ::
  (HasListExpr expr builtin) =>
  GenericArg (expr builtin) ->
  GenericArg (expr builtin) ->
  GenericArg (expr builtin) ->
  expr builtin
pattern ICons t x xs <- (getExpr accessCons -> Just (t, x, xs))
  where
    ICons t x xs = mkExpr accessCons (t, x, xs)

mkListExpr ::
  (HasListExpr expr builtin) =>
  expr builtin ->
  [expr builtin] ->
  expr builtin
mkListExpr tElem = foldr cons nil
  where
    nil = INil (implicit tElem)
    cons x xs = ICons (implicit tElem) (explicit x) (explicit xs)

{-
,

mkDims :: (HasNatLits expr, HasStandardListLits expr) => expr -> [Int] -> expr
mkDims natType ds = mkListExpr natType (fmap INatLiteral ds)

getDim :: (HasNatLits expr) => expr -> Maybe Int
getDim = \case
  INatLiteral n -> Just n
  _ -> Nothing

getDimsExprs :: (HasNatLits expr, HasStandardListLits expr) => expr -> Either expr [expr]
getDimsExprs = \case
  INil _ -> return []
  ICons _ d ds -> (argExpr d :) <$> getDimsExprs (argExpr ds)
  e -> throwError e

getDims :: (HasNatLits expr, HasStandardListLits expr) => expr -> Maybe [Int]
getDims v = case getDimsExprs v of
  Left {} -> Nothing
  Right xs -> traverse getDim xs
-}

--------------------------------------------------------------------------------
-- Tensors

type HasTensorExpr expr builtin = (HasBuiltinConstructor expr, BuiltinHasTensors builtin)

accessStackTensor ::
  (HasTensorExpr expr builtin) =>
  Accessor (expr builtin) (GenericArg (expr builtin), GenericArg (expr builtin), GenericArg (expr builtin), [GenericArg (expr builtin)])
accessStackTensor =
  Access
    { getExpr = \case
        (getBuiltin accessStackTensorBuiltin -> Just ((), d : ds : t : xs)) -> Just (d, ds, t, xs)
        _ -> Nothing,
      mkExpr = \(d, ds, t, xs) -> mkBuiltin accessStackTensorBuiltin () (d : ds : t : xs)
    }

accessConstTensor ::
  (HasTensorExpr expr builtin) =>
  Accessor (expr builtin) (GenericArg (expr builtin), expr builtin, expr builtin)
accessConstTensor =
  Access
    { getExpr = \case
        (getBuiltin accessConstTensorBuiltin -> Just ((), [t, v, ds])) -> Just (t, argExpr v, argExpr ds)
        _ -> Nothing,
      mkExpr = \(t, v, ds) -> mkBuiltin accessConstTensorBuiltin () [t, explicit v, explicit ds]
    }

accessAtTensor ::
  (HasTensorExpr expr builtin) =>
  Accessor (expr builtin) (GenericArg (expr builtin), GenericArg (expr builtin), GenericArg (expr builtin), expr builtin, expr builtin)
accessAtTensor =
  Access
    { getExpr = \case
        (getBuiltin accessAtTensorBuiltin -> Just ((), [t, d, ds, xs, i])) -> Just (t, d, ds, argExpr xs, argExpr i)
        _ -> Nothing,
      mkExpr = \(t, d, ds, xs, i) -> mkBuiltin accessAtTensorBuiltin () [t, d, ds, explicit xs, explicit i]
    }

accessForeachTensor ::
  (HasTensorExpr expr builtin) =>
  Accessor (expr builtin) (GenericArg (expr builtin), GenericArg (expr builtin), GenericArg (expr builtin), expr builtin)
accessForeachTensor =
  Access
    { getExpr = \case
        (getBuiltin accessAtTensorBuiltin -> Just ((), [t, d, ds, fn])) -> Just (t, d, ds, argExpr fn)
        _ -> Nothing,
      mkExpr = \(t, d, ds, fn) -> mkBuiltin accessAtTensorBuiltin () [t, d, ds, explicit fn]
    }

pattern IStackTensor :: (HasTensorExpr expr builtin) => GenericArg (expr builtin) -> GenericArg (expr builtin) -> GenericArg (expr builtin) -> [GenericArg (expr builtin)] -> expr builtin
pattern IStackTensor d ds t xs <- (getExpr accessStackTensor -> Just (d, ds, t, xs))
  where
    IStackTensor d ds t xs = mkExpr accessStackTensor (d, ds, t, xs)

pattern IConstTensor :: (HasTensorExpr expr builtin) => GenericArg (expr builtin) -> expr builtin -> expr builtin -> expr builtin
pattern IConstTensor t v ds <- (getExpr accessConstTensor -> Just (t, v, ds))
  where
    IConstTensor t v ds = mkExpr accessConstTensor (t, v, ds)

constantMatching :: (Eq a, HasTensorExpr expr builtin) => a -> Accessor (expr builtin) a -> Destruct (expr builtin) ()
constantMatching value access e = case getExpr accessConstTensor e of
  Just (_, b, _) -> case getExpr access b of
    Just v | v == value -> Just ()
    _ -> Nothing
  _ -> Nothing

{-
pattern IBoolConstTensor :: (HasBoolLits expr) => expr -> expr -> expr
pattern IBoolConstTensor value dims <- (getBoolConstTensor -> Just (value, dims))

pattern IRatConstTensor :: (HasRatLits expr) => expr -> expr -> expr
pattern IRatConstTensor value dims <- (getRatConstTensor -> Just (value, dims))
-}
