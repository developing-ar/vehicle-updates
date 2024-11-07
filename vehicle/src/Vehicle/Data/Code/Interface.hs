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

--------------------------------------------------------------------------------
-- Naturals

class HasBoolLits expr where
  mkBoolTensorLit :: Tensor Bool -> expr
  getBoolTensorLit :: expr -> Maybe (Tensor Bool)

  getBoolConstTensor :: expr -> Maybe (expr, expr)

pattern IBoolTensor :: (HasBoolLits expr) => Tensor Bool -> expr
pattern IBoolTensor n <- (getBoolTensorLit -> Just n)
  where
    IBoolTensor n = mkBoolTensorLit n

pattern IBoolLiteral :: (HasBoolLits expr) => Bool -> expr
pattern IBoolLiteral n = IBoolTensor (ZeroDimTensor n)

pattern IBoolConstTensor :: (HasBoolLits expr) => expr -> expr -> expr
pattern IBoolConstTensor value dims <- (getBoolConstTensor -> Just (value, dims))

--------------------------------------------------------------------------------
-- Indices

class HasIndexLits expr where
  mkIndexLit :: Int -> expr
  getIndexLit :: expr -> Maybe Int

  mkIndexTensorLit :: Tensor Int -> expr
  getIndexTensorLit :: expr -> Maybe (Tensor Int)

pattern IIndexLiteral :: (HasIndexLits expr) => Int -> expr
pattern IIndexLiteral n <- (getIndexLit -> Just n)
  where
    IIndexLiteral n = mkIndexLit n

pattern IIndexTensor :: (HasIndexLits expr) => Tensor Int -> expr
pattern IIndexTensor n <- (getIndexTensorLit -> Just n)
  where
    IIndexTensor n = mkIndexTensorLit n

--------------------------------------------------------------------------------
-- Naturals

class HasNatLits expr where
  mkNatLit :: Int -> expr
  getNatLit :: expr -> Maybe Int

  mkNatTensorLit :: Tensor Int -> expr
  getNatTensorLit :: expr -> Maybe (Tensor Int)

pattern INatLiteral :: (HasNatLits expr) => Int -> expr
pattern INatLiteral n <- (getNatLit -> Just n)
  where
    INatLiteral n = mkNatLit n

pattern INatTensor :: (HasNatLits expr) => Tensor Int -> expr
pattern INatTensor n <- (getNatTensorLit -> Just n)
  where
    INatTensor n = mkNatTensorLit n

--------------------------------------------------------------------------------
-- Rationals

class HasRatLits expr where
  mkRatTensorLit :: RationalTensor -> expr
  getRatTensorLit :: expr -> Maybe RationalTensor

  getRatConstTensor :: expr -> Maybe (expr, expr)

pattern IRatTensor :: (HasRatLits expr) => Tensor Rational -> expr
pattern IRatTensor n <- (getRatTensorLit -> Just n)
  where
    IRatTensor n = mkRatTensorLit n

pattern IRatLiteral :: (HasRatLits expr) => Rational -> expr
pattern IRatLiteral n = IRatTensor (ZeroDimTensor n)

pattern IRatConstTensor :: (HasRatLits expr) => expr -> expr -> expr
pattern IRatConstTensor value dims <- (getRatConstTensor -> Just (value, dims))

--------------------------------------------------------------------------------
-- Lists

class HasStandardListLits expr where
  getNil :: expr -> Maybe (GenericArg expr)
  mkNil :: GenericArg expr -> expr

  getCons :: expr -> Maybe (GenericArg expr, GenericArg expr, GenericArg expr)
  mkCons :: GenericArg expr -> GenericArg expr -> GenericArg expr -> expr

pattern INil :: (HasStandardListLits expr) => GenericArg expr -> expr
pattern INil t <- (getNil -> Just t)
  where
    INil t = mkNil t

pattern ICons :: (HasStandardListLits expr) => GenericArg expr -> GenericArg expr -> GenericArg expr -> expr
pattern ICons t x xs <- (getCons -> Just (t, x, xs))
  where
    ICons t x xs = mkCons t x xs

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
-- Vectors

-- | Class for expressions that have vectors where all elements have a single
-- type and therefore the type is at the start
class HasStandardVecLits expr where
  mkHomoVector :: GenericArg expr -> [GenericArg expr] -> expr
  getHomoVector :: expr -> Maybe (GenericArg expr, [GenericArg expr])

pattern IVecLiteral :: (HasStandardVecLits expr) => GenericArg expr -> [GenericArg expr] -> expr
pattern IVecLiteral t xs <- (getHomoVector -> Just (t, xs))
  where
    IVecLiteral t xs = mkHomoVector t xs

--------------------------------------------------------------------------------
-- Constructors

class HasUnitLits expr where
  mkUnitLit :: expr
  isUnitLit :: expr -> Bool

pattern IUnitLiteral :: (HasUnitLits expr) => expr
pattern IUnitLiteral <- (isUnitLit -> True)
  where
    IUnitLiteral = mkUnitLit
