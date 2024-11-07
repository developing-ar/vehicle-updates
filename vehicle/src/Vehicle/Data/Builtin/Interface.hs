module Vehicle.Data.Builtin.Interface where

import Vehicle.Data.Builtin.Core
import Vehicle.Data.Tensor (Tensor)

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
-- In these classes we need to separate out the types from the literals, as
-- various sets of builtins may have the literals but not the types (e.g.
-- `LinearityBuiltin`)
--------------------------------------------------------------------------------
-- HasBool

class BuiltinHasBoolLiterals builtin where
  mkBoolBuiltinTensorLit :: Tensor Bool -> builtin
  getBoolBuiltinTensorLit :: builtin -> Maybe (Tensor Bool)

--------------------------------------------------------------------------------
-- HasIndex

class BuiltinHasIndexLiterals builtin where
  mkIndexBuiltinLit :: Int -> builtin
  getIndexBuiltinLit :: builtin -> Maybe Int

class BuiltinHasIndexTensorLiterals builtin where
  mkIndexBuiltinTensorLit :: Tensor Int -> builtin
  getIndexBuiltinTensorLit :: builtin -> Maybe (Tensor Int)

--------------------------------------------------------------------------------
-- HasNat

class BuiltinHasNatLiterals builtin where
  mkNatBuiltinLit :: Int -> builtin
  getNatBuiltinLit :: builtin -> Maybe Int

class BuiltinHasNatTensorLiterals builtin where
  mkNatBuiltinTensorLit :: Tensor Int -> builtin
  getNatBuiltinTensorLit :: builtin -> Maybe (Tensor Int)

--------------------------------------------------------------------------------
-- HasRat

class BuiltinHasRatLiterals builtin where
  mkRatBuiltinTensorLit :: Tensor Rational -> builtin
  getRatBuiltinTensorLit :: builtin -> Maybe (Tensor Rational)

--------------------------------------------------------------------------------
-- HasList

class BuiltinHasListLiterals builtin where
  mkBuiltinNil :: builtin
  isBuiltinNil :: builtin -> Bool

  mkBuiltinCons :: builtin
  isBuiltinCons :: builtin -> Bool

--------------------------------------------------------------------------------
-- HasRat

class BuiltinHasConstTensor builtin where
  mkConstTensorBuiltin :: builtin
  isConstTensorBuiltin :: builtin -> Bool

--------------------------------------------------------------------------------
-- BuiltinHasStandardData

-- | Indicates that this set of builtins has the standard builtin constructors
-- and functions.
class BuiltinHasStandardData builtin where
  mkBuiltinConstructor :: BuiltinConstructor -> builtin
  getBuiltinConstructor :: builtin -> Maybe BuiltinConstructor

  mkBuiltinFunction :: BuiltinFunction -> builtin
  getBuiltinFunction :: builtin -> Maybe BuiltinFunction

--------------------------------------------------------------------------------
-- BuiltinHasStandardTypes

-- | Indicates that this set of builtins has the standard set of types.
class BuiltinHasStandardTypes builtin where
  mkBuiltinType :: BuiltinType -> builtin
  getBuiltinType :: builtin -> Maybe BuiltinType

  mkNatInDomainConstraint :: builtin

--------------------------------------------------------------------------------
-- HasStandardBuiltins

-- | Indicates that this set of builtins has the standard set of constructors,
-- functions and types.
class BuiltinHasStandardTypeClasses builtin where
  mkBuiltinTypeClass :: TypeClass -> builtin

--------------------------------------------------------------------------------
-- HasStandardBuiltins

-- | Indicates that this set of builtins has the standard set of constructors,
-- functions and types.
type HasStandardBuiltins builtin =
  ( BuiltinHasStandardTypes builtin,
    BuiltinHasStandardData builtin
  )

{-
--------------------------------------------------------------------------------
-- HasTensorBuiltins

class BuiltinHasRatTensor builtin where
  mkRatTensorBuiltin :: RatTensorBuiltin -> builtin
  getRatTensorBuiltin :: builtin -> Maybe RatTensorBuiltin

class (BuiltinHasRatTensor builtin) => BuiltinHasBoolTensor builtin where
  mkBoolTensorBuiltin :: BoolTensorBuiltin -> builtin
  getBoolTensorBuiltin :: builtin -> Maybe BoolTensorBuiltin

--------------------------------------------------------------------------------
-- Dimension builtins

class BuiltinHasDimensionTypes builtin where
  mkDimensionTypeBuiltin :: DimensionTypeBuiltin -> builtin
  getDimensionTypeBuiltin :: builtin -> Maybe DimensionTypeBuiltin

class BuiltinHasDimensionData builtin where
  mkDimensionDataBuiltin :: DimensionDataBuiltin -> builtin
  getDimensionDataBuiltin :: builtin -> Maybe DimensionDataBuiltin

--------------------------------------------------------------------------------
-- Dimensions

data DimensionTypeBuiltin
  = DimensionType
  | DimensionsType
  | DimensionIndexType
  | TensorType
  deriving (Show, Eq, Generic)

data DimensionDataBuiltin
  = Dimension Int
  | DimensionNil
  | DimensionCons
  | DimensionIndex Int
  | DimensionLookup
  | DimensionIndexTensor (Tensor Int)
  | StackTensor Int
  | ConstTensor
  deriving (Show, Eq, Generic)

--------------------------------------------------------------------------------
-- Rational tensor builtins

data RatTensorBuiltin
  = RatTensor (Tensor Rational)
  | RatType
  | RatLiteral Rational
  | NegRatTensor
  | AddRatTensor
  | SubRatTensor
  | MulRatTensor
  | DivRatTensor
  | MinRatTensor
  | MaxRatTensor
  | ReduceAddRatTensor
  | ReduceMulRatTensor
  | ReduceMinRatTensor
  | ReduceMaxRatTensor
  | SearchRatTensor
  deriving (Show, Eq, Generic)

--------------------------------------------------------------------------------
-- Boolean tensor builtins

data BoolTensorBuiltin
  = BoolType
  | AndBoolTensor
  | OrBoolTensor
  | NotBoolTensor
  | EqualsRatTensor EqualityOp
  | OrderRatTensor OrderOp
  | ReduceAndTensor
  | ReduceOrTensor
  | QuantifyRatTensor Quantifier
  deriving (Show, Eq, Generic)
-}
