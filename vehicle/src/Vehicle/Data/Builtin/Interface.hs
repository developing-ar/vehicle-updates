module Vehicle.Data.Builtin.Interface where

import Data.Maybe (isJust)
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Code.Expr
import Vehicle.Data.Tensor (Tensor)
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
-- Conversion

class ConvertableBuiltin builtin1 builtin2 where
  convertBuiltin :: Provenance -> builtin1 -> Expr builtin2

instance ConvertableBuiltin builtin builtin where
  convertBuiltin = Builtin

instance ConvertableBuiltin BuiltinType Builtin where
  convertBuiltin p = Builtin p . BuiltinType

instance ConvertableBuiltin TypeClassOp Builtin where
  convertBuiltin p = Builtin p . TypeClassOp

instance ConvertableBuiltin BuiltinConstructor Builtin where
  convertBuiltin p = Builtin p . BuiltinConstructor

instance ConvertableBuiltin BuiltinFunction Builtin where
  convertBuiltin p = Builtin p . BuiltinFunction

instance ConvertableBuiltin ComparisonOp Builtin where
  convertBuiltin p = convertBuiltin p . CompareTC

convertExprBuiltins ::
  forall builtin1 builtin2.
  (ConvertableBuiltin builtin1 builtin2) =>
  Expr builtin1 ->
  Expr builtin2
convertExprBuiltins = mapBuiltins $ \p b args ->
  normAppList (convertBuiltin p b) args

--------------------------------------------------------------------------------
-- Printing

class (Show builtin, Pretty builtin, ConvertableBuiltin builtin Builtin) => PrintableBuiltin builtin where
  -- | Convert expressions with the builtin back to expressions with the standard
  -- builtin type. Used for printing.
  coercionArgs :: builtin -> Maybe ([Arg builtin] -> Expr builtin)

isCoercionExpr :: (PrintableBuiltin builtin) => Expr builtin -> Bool
isCoercionExpr = \case
  Builtin _ b -> isJust $ coercionArgs b
  App (Builtin _ b) _ -> isJust $ coercionArgs b
  _ -> False

-- | Use to convert builtins for printing that have no representation in the
-- standard `Builtin` type.
cheatConvertBuiltin :: Provenance -> Doc a -> Expr builtin
cheatConvertBuiltin p b = FreeVar p $ stdlibIdentifier $ layoutAsText b

--------------------------------------------------------------------------------
-- In these classes we need to separate out the types from the literals, as
-- various sets of builtins may have the literals but not the types (e.g.
-- `LinearityBuiltin`)
--------------------------------------------------------------------------------
-- HasBool

type Destruct expr v = expr -> Maybe v

type Construct expr v = v -> expr

data Accessor expr v = Access
  { getExpr :: Destruct expr v,
    mkExpr :: Construct expr v
  }

class BuiltinHasBoolLiterals builtin where
  accessBoolTensorLitBuiltin :: Accessor builtin (Tensor Bool)

  accessNotBuiltin :: Accessor builtin ()
  accessAndBuiltin :: Accessor builtin ()
  accessOrBuiltin :: Accessor builtin ()
  accessImpliesBuiltin :: Accessor builtin ()
  accessReduceAndBuiltin :: Accessor builtin ()
  accessReduceOrBuiltin :: Accessor builtin ()
  accessIfBuiltin :: Accessor builtin ()

  accessCompareIndexBuiltin :: Accessor builtin ComparisonOp
  accessCompareNatBuiltin :: Accessor builtin ComparisonOp
  accessCompareRatTensorBuiltin :: Accessor builtin ComparisonOp

  accessQuantifyRatTensorBuiltin :: Accessor builtin Quantifier

class BuiltinHasIndexLiterals builtin where
  accessIndexLitBuiltin :: Accessor builtin Int
  accessIndexTensorLitBuiltin :: Accessor builtin (Tensor Int)

class BuiltinHasNatLiterals builtin where
  accessNatLitBuiltin :: Accessor builtin Int
  accessNatTensorLitBuiltin :: Accessor builtin (Tensor Int)

  accessAddNatBuiltin :: Accessor builtin ()
  accessMulNatBuiltin :: Accessor builtin ()

class BuiltinHasNatType builtin where
  accessNatTypeBuiltin :: Accessor builtin ()

class BuiltinHasListLiterals builtin where
  accessNilBuiltin :: Accessor builtin ()
  accessConsBuiltin :: Accessor builtin ()

  accessMapListBuiltin :: Accessor builtin ()
  accessFoldListBuiltin :: Accessor builtin ()

class BuiltinHasTensors builtin where
  accessStackTensorBuiltin :: Accessor builtin ()
  accessConstTensorBuiltin :: Accessor builtin ()
  accessAtTensorBuiltin :: Accessor builtin ()

class BuiltinHasForeach builtin where
  accessForeachTensorBuiltin :: Accessor builtin ()

class (BuiltinHasTensors builtin) => BuiltinHasRatLiterals builtin where
  accessRatTensorLitBuiltin :: Accessor builtin (Tensor Rational)

  accessNegRatTensorBuiltin :: Accessor builtin ()
  accessAddRatTensorBuiltin :: Accessor builtin ()
  accessMulRatTensorBuiltin :: Accessor builtin ()
  accessSubRatTensorBuiltin :: Accessor builtin ()
  accessDivRatTensorBuiltin :: Accessor builtin ()
  accessMinRatTensorBuiltin :: Accessor builtin ()
  accessMaxRatTensorBuiltin :: Accessor builtin ()
  accessPowRatTensorBuiltin :: Accessor builtin ()
  accessReduceAddRatBuiltin :: Accessor builtin ()
  accessReduceMulRatBuiltin :: Accessor builtin ()
  accessReduceMinRatBuiltin :: Accessor builtin ()
  accessReduceMaxRatBuiltin :: Accessor builtin ()

-- | Indicates that this set of builtins has the standard builtin constructors
-- and functions.
class BuiltinHasStandardData builtin where
  accessBuiltinConstructor :: Accessor builtin BuiltinConstructor
  accessBuiltinFunction :: Accessor builtin BuiltinFunction

-- | Indicates that this set of builtins has the standard set of types.
class BuiltinHasStandardTypes builtin where
  accessBuiltinType :: Accessor builtin BuiltinType

class BuiltinHasIterate builtin where
  accessIterateBuiltin :: Accessor builtin ()

-- | Indicates that this set of builtins has the standard set of constructors,
-- functions and types.
class BuiltinHasStandardTypeClasses builtin where
  mkBuiltinTypeClass :: TypeClass -> builtin

-- | Indicates that this set of builtins has the standard set of constructors,
-- functions and types.
type HasStandardBuiltins builtin =
  ( BuiltinHasStandardTypes builtin,
    BuiltinHasStandardData builtin
  )
