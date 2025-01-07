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

type Destruct expr v = expr -> Maybe v

type Construct expr v = v -> expr

data Accessor expr v = Access
  { getExpr :: Destruct expr v,
    mkExpr :: Construct expr v
  }

--------------------------------------------------------------------------------
-- In these classes we need to separate out the types from the literals, as
-- various sets of builtins may have the literals but not the types (e.g.
-- `LinearityBuiltin`)
--------------------------------------------------------------------------------
-- HasBool

class BuiltinHasBoolLiterals builtin where
  accessBoolTensorLitBuiltin :: Accessor builtin (Tensor Bool)

  accessNotBuiltin :: Accessor builtin ()
  accessAndBuiltin :: Accessor builtin ()
  accessOrBuiltin :: Accessor builtin ()
  accessImpliesBuiltin :: Accessor builtin ()
  accessReduceAndBuiltin :: Accessor builtin ()
  accessReduceOrBuiltin :: Accessor builtin ()
  accessIfBuiltin :: Accessor builtin ()

  accessOrderIndexBuiltin :: Accessor builtin OrderOp
  accessOrderNatBuiltin :: Accessor builtin OrderOp
  accessOrderRatTensorBuiltin :: Accessor builtin OrderOp
  accessEqualIndexBuiltin :: Accessor builtin EqualityOp
  accessEqualNatBuiltin :: Accessor builtin EqualityOp
  accessEqualRatTensorBuiltin :: Accessor builtin EqualityOp

--------------------------------------------------------------------------------
-- HasIndex

class BuiltinHasIndexLiterals builtin where
  accessIndexLitBuiltin :: Accessor builtin Int
  accessIndexTensorLitBuiltin :: Accessor builtin (Tensor Int)

--------------------------------------------------------------------------------
-- HasNat

class BuiltinHasNatLiterals builtin where
  accessNatLitBuiltin :: Accessor builtin Int
  accessNatTensorLitBuiltin :: Accessor builtin (Tensor Int)

  accessAddNatBuiltin :: Accessor builtin ()
  accessMulNatBuiltin :: Accessor builtin ()

--------------------------------------------------------------------------------
-- HasList

class BuiltinHasListLiterals builtin where
  accessNilBuiltin :: Accessor builtin ()
  accessConsBuiltin :: Accessor builtin ()

--------------------------------------------------------------------------------
-- HasTensors

class BuiltinHasTensors builtin where
  accessStackTensorBuiltin :: Accessor builtin ()
  accessConstTensorBuiltin :: Accessor builtin ()
  accessAtTensorBuiltin :: Accessor builtin ()
  accessForeachTensorBuiltin :: Accessor builtin ()

--------------------------------------------------------------------------------
-- HasRat

class (BuiltinHasTensors builtin) => BuiltinHasRatLiterals builtin where
  accessRatTensorLitBuiltin :: Accessor builtin (Tensor Rational)

  accessNegRatTensorBuiltin :: Accessor builtin ()
  accessAddRatTensorBuiltin :: Accessor builtin ()
  accessMulRatTensorBuiltin :: Accessor builtin ()
  accessSubRatTensorBuiltin :: Accessor builtin ()
  accessDivRatTensorBuiltin :: Accessor builtin ()
  accessMinRatTensorBuiltin :: Accessor builtin ()
  accessMaxRatTensorBuiltin :: Accessor builtin ()
  accessReduceAddRatBuiltin :: Accessor builtin ()
  accessReduceMulRatBuiltin :: Accessor builtin ()
  accessReduceMinRatBuiltin :: Accessor builtin ()
  accessReduceMaxRatBuiltin :: Accessor builtin ()

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
