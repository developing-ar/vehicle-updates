module Vehicle.Data.Code.Interface where

import Control.Monad.Except (MonadError (..))
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Tensor
import Vehicle.Prelude
import Vehicle.Syntax.Builtin.BasicOperations

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

class IsArgs args where
  accessSpine :: Accessor [GenericArg expr] (args expr)

-- | Arguments for comparisons (==, <= etc.) over Nat
data NatOp2Args expr = NatOp2Args
  { natOp2Arg1 :: expr,
    natOp2Arg2 :: expr
  }

instance IsArgs NatOp2Args where
  accessSpine =
    Access
      { getExpr = \case
          [x, y] -> Just $ NatOp2Args (argExpr x) (argExpr y)
          _ -> Nothing,
        mkExpr = \(NatOp2Args x y) -> explicit <$> [x, y]
      }

-- | Arguments for comparisons (==, <= etc.) over Index
data IndexComparisonArgs expr = IndexCompArgs
  { indexCompSize1 :: GenericArg expr,
    indexCompSize2 :: GenericArg expr,
    indexCompArg1 :: expr,
    indexCompArg2 :: expr
  }

instance IsArgs IndexComparisonArgs where
  accessSpine =
    Access
      { getExpr = \case
          [n1, n2, x, y] -> Just $ IndexCompArgs n1 n2 (argExpr x) (argExpr y)
          _ -> Nothing,
        mkExpr = \(IndexCompArgs n1 n2 x y) -> [n1, n2, explicit x, explicit y]
      }

-- | Arguments for unary tensor operations (e.g. -, not)
data TensorOp1Args expr = TensorOp1Args
  { tensorOp1Dims :: GenericArg expr,
    tensorOp1Arg :: expr
  }

instance IsArgs TensorOp1Args where
  accessSpine =
    Access
      { getExpr = \case
          [ds, x] -> Just $ TensorOp1Args ds (argExpr x)
          _ -> Nothing,
        mkExpr = \(TensorOp1Args ds x) -> [ds, explicit x]
      }

-- | Arguments for binary tensor operations (e.g. +, -)
data TensorOp2Args expr = TensorOp2Args
  { tensorOp2Dims :: GenericArg expr,
    tensorOp2Arg1 :: expr,
    tensorOp2Arg2 :: expr
  }

instance IsArgs TensorOp2Args where
  accessSpine =
    Access
      { getExpr = \case
          [ds, x, y] -> Just $ TensorOp2Args ds (argExpr x) (argExpr y)
          _ -> Nothing,
        mkExpr = \(TensorOp2Args ds x y) -> [ds, explicit x, explicit y]
      }

type TensorReductionArgs = TensorOp2Args

type NatComparisonAccessor expr op = Accessor expr (op, NatOp2Args expr)

type NatOp2Accessor expr = Accessor expr (NatOp2Args expr)

type IndexComparisonAccessor expr op = Accessor expr (op, IndexComparisonArgs expr)

type RatTensorComparisonAccessor expr op = Accessor expr (op, TensorOp2Args expr)

type Op1Accessor expr = Accessor expr expr

type Op2Accessor expr = Accessor expr (expr, expr)

type TensorOp1Accessor expr = Accessor expr (TensorOp1Args expr)

type TensorOp2Accessor expr = Accessor expr (TensorOp2Args expr)

type TensorReductionAccessor expr = Accessor expr (TensorReductionArgs expr)

accessNoArgs ::
  (HasBuiltinConstructor expr) =>
  Accessor builtin a ->
  Accessor (expr builtin) a
accessNoArgs access =
  Access
    { getExpr = \case
        (getBuiltin access -> Just (b, [])) -> Just b
        _ -> Nothing,
      mkExpr = \b -> mkBuiltin access b []
    }

accessArgs ::
  (HasBuiltinConstructor expr, IsArgs args) =>
  Accessor builtin () ->
  Accessor (expr builtin) (args (expr builtin))
accessArgs accessOp =
  Access
    { getExpr = \case
        (getBuiltin accessOp -> Just ((), getExpr accessSpine -> Just args)) -> Just args
        _ -> Nothing,
      mkExpr = \args -> mkBuiltin accessOp () (mkExpr accessSpine args)
    }

accessOpAndArgs ::
  (HasBuiltinConstructor expr, IsArgs args) =>
  Accessor builtin op ->
  Accessor (expr builtin) (op, args (expr builtin))
accessOpAndArgs accessOp =
  Access
    { getExpr = \case
        (getBuiltin accessOp -> Just (op, getExpr accessSpine -> Just args)) -> Just (op, args)
        _ -> Nothing,
      mkExpr = \(op, args) -> mkBuiltin accessOp op (mkExpr accessSpine args)
    }

op2Args :: (HasBuiltinConstructor expr) => Accessor builtin () -> Op2Accessor (expr builtin)
op2Args access =
  Access
    { getExpr = \case
        (getBuiltin access -> Just ((), [xs, ys])) -> Just (argExpr xs, argExpr ys)
        _ -> Nothing,
      mkExpr = \(xs, ys) -> mkBuiltin access () [explicit xs, explicit ys]
    }

--------------------------------------------------------------------------------
-- Boolean operations
--------------------------------------------------------------------------------

type HasBoolExpr expr builtin = (HasBuiltinConstructor expr, BuiltinHasBoolLiterals builtin)

accessBoolTensorLiteral :: (HasBoolExpr expr builtin) => Accessor (expr builtin) BoolTensor
accessBoolTensorLiteral = accessNoArgs accessBoolTensorLitBuiltin

accessNotTensor :: (HasBoolExpr expr builtin) => TensorOp1Accessor (expr builtin)
accessNotTensor = accessArgs accessNotBuiltin

accessAndTensor :: (HasBoolExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessAndTensor = accessArgs accessAndBuiltin

accessOrTensor :: (HasBoolExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessOrTensor = accessArgs accessOrBuiltin

accessImpliesTensor :: (HasBoolExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessImpliesTensor = accessArgs accessImpliesBuiltin

accessReduceAnd :: (HasBoolExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceAnd = accessArgs accessReduceAndBuiltin

accessReduceOr :: (HasBoolExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceOr = accessArgs accessReduceOrBuiltin

accessIf :: (HasBoolExpr expr builtin) => Accessor (expr builtin) (GenericArg (expr builtin), expr builtin, expr builtin, expr builtin)
accessIf =
  Access
    { getExpr = \case
        (getBuiltin accessIfBuiltin -> Just ((), [t, c, x, y])) -> Just (t, argExpr c, argExpr x, argExpr y)
        _ -> Nothing,
      mkExpr = \(t, c, x, y) -> mkBuiltin accessIfBuiltin () [t, explicit c, explicit x, explicit y]
    }

accessOrderIndex :: (HasBoolExpr expr builtin) => IndexComparisonAccessor (expr builtin) OrderOp
accessOrderIndex = accessOpAndArgs accessOrderIndexBuiltin

accessOrderNat :: (HasBoolExpr expr builtin) => NatComparisonAccessor (expr builtin) OrderOp
accessOrderNat = accessOpAndArgs accessOrderNatBuiltin

accessOrderRatTensor :: (HasBoolExpr expr builtin) => RatTensorComparisonAccessor (expr builtin) OrderOp
accessOrderRatTensor = accessOpAndArgs accessOrderRatTensorBuiltin

accessEqIndex :: (HasBoolExpr expr builtin) => IndexComparisonAccessor (expr builtin) EqualityOp
accessEqIndex = accessOpAndArgs accessEqRatTensorBuiltin

accessEqNat :: (HasBoolExpr expr builtin) => NatComparisonAccessor (expr builtin) EqualityOp
accessEqNat = accessOpAndArgs accessEqNatBuiltin

accessEqRatTensor :: (HasBoolExpr expr builtin) => RatTensorComparisonAccessor (expr builtin) EqualityOp
accessEqRatTensor = accessOpAndArgs accessEqRatTensorBuiltin

accessQuantifyRatTensor :: (HasBoolExpr expr builtin) => Accessor (expr builtin) (Quantifier, GenericArg (expr builtin), expr builtin)
accessQuantifyRatTensor =
  Access
    { getExpr = \case
        (getBuiltin accessQuantifyRatTensorBuiltin -> Just (q, [ds, fn])) -> Just (q, ds, argExpr fn)
        _ -> Nothing,
      mkExpr = \(q, ds, fn) -> mkBuiltin accessQuantifyRatTensorBuiltin q [ds, explicit fn]
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
accessIndexLiteral = accessNoArgs accessIndexLitBuiltin

accessIndexTensorLiteral :: (HasIndexExpr expr builtin) => Accessor (expr builtin) IndexTensor
accessIndexTensorLiteral = accessNoArgs accessIndexTensorLitBuiltin

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

accessNatType :: (HasNatExpr expr builtin) => Accessor (expr builtin) ()
accessNatType = accessNoArgs accessNatTypeBuiltin

accessNatLiteral :: (HasNatExpr expr builtin) => Accessor (expr builtin) Int
accessNatLiteral = accessNoArgs accessNatLitBuiltin

accessNatTensorLiteral :: (HasNatExpr expr builtin) => Accessor (expr builtin) NatTensor
accessNatTensorLiteral = accessNoArgs accessNatTensorLitBuiltin

accessAddNat :: (HasNatExpr expr builtin) => Op2Accessor (expr builtin)
accessAddNat = op2Args accessAddNatBuiltin

accessMulNat :: (HasNatExpr expr builtin) => Op2Accessor (expr builtin)
accessMulNat = op2Args accessMulNatBuiltin

pattern INatType :: (HasNatExpr expr builtin) => expr builtin
pattern INatType <- (getExpr accessNatType -> Just ())
  where
    INatType = mkExpr accessNatType ()

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
accessRatTensorLiteral = accessNoArgs accessRatTensorLitBuiltin

accessNegRatTensor :: (HasRatExpr expr builtin) => TensorOp1Accessor (expr builtin)
accessNegRatTensor = accessArgs accessNegRatTensorBuiltin

accessAddRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessAddRatTensor = accessArgs accessAddRatTensorBuiltin

accessMulRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessMulRatTensor = accessArgs accessMulRatTensorBuiltin

accessSubRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessSubRatTensor = accessArgs accessSubRatTensorBuiltin

accessDivRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessDivRatTensor = accessArgs accessDivRatTensorBuiltin

accessMinRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessMinRatTensor = accessArgs accessMinRatTensorBuiltin

accessMaxRatTensor :: (HasRatExpr expr builtin) => TensorOp2Accessor (expr builtin)
accessMaxRatTensor = accessArgs accessMaxRatTensorBuiltin

accessReduceAddRat :: (HasRatExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceAddRat = accessArgs accessReduceAddRatBuiltin

accessReduceMulRat :: (HasRatExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceMulRat = accessArgs accessReduceMulRatBuiltin

accessReduceMinRat :: (HasRatExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceMinRat = accessArgs accessReduceMinRatBuiltin

accessReduceMaxRat :: (HasRatExpr expr builtin) => TensorReductionAccessor (expr builtin)
accessReduceMaxRat = accessArgs accessReduceMaxRatBuiltin

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
  Accessor (expr builtin) (GenericArg (expr builtin), expr builtin, expr builtin)
accessCons =
  Access
    { getExpr = \case
        (getBuiltin accessConsBuiltin -> Just ((), [t, x, xs])) -> Just (t, argExpr x, argExpr xs)
        _ -> Nothing,
      mkExpr = \(t, x, xs) -> mkBuiltin accessConsBuiltin () [t, explicit x, explicit xs]
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
  expr builtin ->
  expr builtin ->
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
    cons = ICons (implicit tElem)

mkDims :: (HasNatExpr expr builtin, HasListExpr expr builtin) => [Int] -> expr builtin
mkDims ds = mkListExpr INatType (fmap INatLiteral ds)

getDim :: (HasNatExpr expr builtin) => expr builtin -> Maybe Int
getDim = \case
  INatLiteral n -> Just n
  _ -> Nothing

getDimsExprs :: (HasNatExpr expr builtin, HasListExpr expr builtin) => expr builtin -> Either (expr builtin) [expr builtin]
getDimsExprs = \case
  INil _ -> return []
  ICons _ d ds -> (d :) <$> getDimsExprs ds
  e -> throwError e

getDims :: (HasNatExpr expr builtin, HasListExpr expr builtin) => expr builtin -> Maybe [Int]
getDims v = case getDimsExprs v of
  Left {} -> Nothing
  Right xs -> traverse getDim xs

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
  (HasBuiltinConstructor expr, BuiltinHasForeach builtin) =>
  Accessor (expr builtin) (GenericArg (expr builtin), GenericArg (expr builtin), GenericArg (expr builtin), expr builtin)
accessForeachTensor =
  Access
    { getExpr = \case
        (getBuiltin accessForeachTensorBuiltin -> Just ((), [t, d, ds, fn])) -> Just (t, d, ds, argExpr fn)
        _ -> Nothing,
      mkExpr = \(t, d, ds, fn) -> mkBuiltin accessForeachTensorBuiltin () [t, d, ds, explicit fn]
    }

pattern IStackTensor :: (HasTensorExpr expr builtin) => GenericArg (expr builtin) -> GenericArg (expr builtin) -> GenericArg (expr builtin) -> [GenericArg (expr builtin)] -> expr builtin
pattern IStackTensor d ds t xs <- (getExpr accessStackTensor -> Just (d, ds, t, xs))
  where
    IStackTensor d ds t xs = mkExpr accessStackTensor (d, ds, t, xs)

pattern IConstTensor :: (HasTensorExpr expr builtin) => GenericArg (expr builtin) -> expr builtin -> expr builtin -> expr builtin
pattern IConstTensor t v ds <- (getExpr accessConstTensor -> Just (t, v, ds))
  where
    IConstTensor t v ds = mkExpr accessConstTensor (t, v, ds)

{-
pattern IBoolConstTensor :: (HasBoolLits expr) => expr -> expr -> expr
pattern IBoolConstTensor value dims <- (getBoolConstTensor -> Just (value, dims))

pattern IRatConstTensor :: (HasRatLits expr) => expr -> expr -> expr
pattern IRatConstTensor value dims <- (getRatConstTensor -> Just (value, dims))
-}
