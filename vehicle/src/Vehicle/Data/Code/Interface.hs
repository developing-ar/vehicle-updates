module Vehicle.Data.Code.Interface where

import Control.Monad.Except (MonadError (..))
import Vehicle.Data.Tensor
import Vehicle.Prelude

--------------------------------------------------------------------------------
-- Interface to standard builtins
--------------------------------------------------------------------------------

-- At various points in the compiler, we have different sets of builtins (e.g.
-- first time we type-check we use the standard set of builtins + type +
-- type classes, but when checking polarity and linearity information we
-- subsitute out all the types and type-classes for new types.)
--
-- The interfaces defined in this file allow us to abstract over the exact set
-- of builtins being used, and therefore allows us to define operations
-- (e.g. normalisation) once, rather than once for each builtin type.

data Accessor expr a = Access
  { getExpr :: expr -> Maybe a,
    mkExpr :: a -> expr
  }

--------------------------------------------------------------------------------
-- Naturals

class HasBoolLits expr where
  accessBoolTensorLiteral :: Accessor expr BoolTensor

pattern IBoolTensorLiteral :: (HasBoolLits expr) => BoolTensor -> expr
pattern IBoolTensorLiteral n <- (getExpr accessBoolTensorLiteral -> Just n)
  where
    IBoolTensorLiteral n = mkExpr accessBoolTensorLiteral n

pattern IBoolLiteral :: (HasBoolLits expr) => Bool -> expr
pattern IBoolLiteral n = IBoolTensorLiteral (ZeroDimTensor n)

--------------------------------------------------------------------------------
-- Indices

class HasIndexLits expr where
  accessIndexLiteral :: Accessor expr Int
  accessIndexTensorLiteral :: Accessor expr IndexTensor

pattern IIndexLiteral :: (HasIndexLits expr) => Int -> expr
pattern IIndexLiteral n <- (getExpr accessIndexLiteral -> Just n)
  where
    IIndexLiteral n = mkExpr accessIndexLiteral n

pattern IIndexTensor :: (HasIndexLits expr) => Tensor Int -> expr
pattern IIndexTensor n <- (getExpr accessIndexTensorLiteral -> Just n)
  where
    IIndexTensor n = mkExpr accessIndexTensorLiteral n

--------------------------------------------------------------------------------
-- Naturals

class HasNatLits expr where
  accessNatLiteral :: Accessor expr Int
  accessNatTensorLiteral :: Accessor expr NatTensor

pattern INatLiteral :: (HasNatLits expr) => Int -> expr
pattern INatLiteral n <- (getExpr accessNatLiteral -> Just n)
  where
    INatLiteral n = mkExpr accessNatLiteral n

pattern INatTensor :: (HasNatLits expr) => Tensor Int -> expr
pattern INatTensor n <- (getExpr accessNatTensorLiteral -> Just n)
  where
    INatTensor n = mkExpr accessNatTensorLiteral n

--------------------------------------------------------------------------------
-- Rationals

class HasRatLits expr where
  accessRatTensor :: Accessor expr RatTensor

pattern IRatTensor :: (HasRatLits expr) => Tensor Rational -> expr
pattern IRatTensor n <- (getExpr accessRatTensor -> Just n)
  where
    IRatTensor n = mkExpr accessRatTensor n

pattern IRatLiteral :: (HasRatLits expr) => Rational -> expr
pattern IRatLiteral n = IRatTensor (ZeroDimTensor n)

--------------------------------------------------------------------------------
-- Lists

class HasStandardListLits expr where
  accessNil :: Accessor expr (GenericArg expr)
  accessCons :: Accessor expr (GenericArg expr, GenericArg expr, GenericArg expr)

pattern INil :: (HasStandardListLits expr) => GenericArg expr -> expr
pattern INil t <- (getExpr accessNil -> Just t)
  where
    INil t = mkExpr accessNil t

pattern ICons :: (HasStandardListLits expr) => GenericArg expr -> GenericArg expr -> GenericArg expr -> expr
pattern ICons t x xs <- (getExpr accessCons -> Just (t, x, xs))
  where
    ICons t x xs = mkExpr accessCons (t, x, xs)

mkListExpr :: (HasStandardListLits expr) => expr -> [expr] -> expr
mkListExpr tElem = foldr cons nil
  where
    nil = INil (implicit tElem)
    cons x xs = ICons (implicit tElem) (explicit x) (explicit xs)

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

--------------------------------------------------------------------------------
-- Tensors

class HasTensorPseudoConstructors expr where
  accessStackTensor :: Accessor expr (GenericArg expr, GenericArg expr, GenericArg expr, [GenericArg expr])
  accessConstTensor :: Accessor expr (GenericArg expr, expr, expr)

pattern IStackTensor :: (HasTensorPseudoConstructors expr) => GenericArg expr -> GenericArg expr -> GenericArg expr -> [GenericArg expr] -> expr
pattern IStackTensor d ds t xs <- (getExpr accessStackTensor -> Just (d, ds, t, xs))
  where
    IStackTensor d ds t xs = mkExpr accessStackTensor (d, ds, t, xs)

pattern IConstTensor :: (HasTensorPseudoConstructors expr) => GenericArg expr -> expr -> expr -> expr
pattern IConstTensor t v ds <- (getExpr accessConstTensor -> Just (t, v, ds))
  where
    IConstTensor t v ds = mkExpr accessConstTensor (t, v, ds)

{-
pattern IBoolConstTensor :: (HasBoolLits expr) => expr -> expr -> expr
pattern IBoolConstTensor value dims <- (getBoolConstTensor -> Just (value, dims))

pattern IRatConstTensor :: (HasRatLits expr) => expr -> expr -> expr
pattern IRatConstTensor value dims <- (getRatConstTensor -> Just (value, dims))
-}
