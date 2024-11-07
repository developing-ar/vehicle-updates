module Vehicle.Data.Builtin.Loss
  ( module Vehicle.Data.Builtin.Loss,
    module Vehicle.Syntax.Builtin.BasicOperations,
  )
where

import GHC.Generics (Generic)
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Tensor (Tensor)
import Vehicle.Prelude (Pretty (..))
import Vehicle.Syntax.Builtin.BasicOperations

--------------------------------------------------------------------------------
-- Builtin datatype

-- | Constructors for types in the language. The types and type-classes
-- are viewed as constructors for `Type`.
data LossBuiltinType
  = UnitType
  | IndexType
  | NatType
  | RatType
  | ListType
  | TensorType
  deriving (Eq, Ord, Show)

instance Pretty LossBuiltinType where
  pretty = \case
    UnitType -> "Unit"
    IndexType -> "Index"
    NatType -> "Nat"
    RatType -> "RatElement"
    ListType -> "List"
    TensorType -> "Tensor"

--------------------------------------------------------------------------------
-- Builtin datatype

-- | Constructors for types in the language. The types and type-classes
-- are viewed as constructors for `Type`.
data LossBuiltinConstructor
  = Nil
  | Cons
  | UnitLiteral
  | IndexLiteral Int
  | IndexTensorLiteral (Tensor Int)
  | NatLiteral Int
  | NatTensorLiteral (Tensor Int)
  | RatTensorLiteral (Tensor Rational)
  deriving (Eq, Ord, Show, Generic)

instance Pretty LossBuiltinConstructor where
  pretty = \case
    Nil -> "nil"
    Cons -> "::"
    UnitLiteral -> "()"
    IndexLiteral x -> pretty x
    IndexTensorLiteral x -> pretty x
    NatLiteral x -> pretty x
    NatTensorLiteral x -> pretty x
    RatTensorLiteral x -> pretty x

--------------------------------------------------------------------------------
-- Functions

data LossBuiltinFunction
  = -- Rat operations
    Add AddDomain
  | Mul MulDomain
  | Neg NegDomain
  | Sub SubDomain
  | Div DivDomain
  | Min MinDomain
  | Max MaxDomain
  | PowRat
  | -- Rat tensor operations
    ReduceAddRatTensor
  | ReduceMulRatTensor
  | ReduceMinRatTensor
  | ReduceMaxRatTensor
  | -- Generic tensor operations
    At
  | StackTensor
  | ConstTensor
  | SearchRatTensor
  deriving (Eq, Ord, Show, Generic)

-- TODO all the show instances should really be obtainable from the grammar
-- somehow.
instance Pretty LossBuiltinFunction where
  pretty = \case
    Add dom -> "add" <> pretty dom
    Mul dom -> "mul" <> pretty dom
    Neg dom -> "neg" <> pretty dom
    Sub dom -> "sub" <> pretty dom
    Div dom -> "div" <> pretty dom
    Min dom -> "min" <> pretty dom
    Max dom -> "max" <> pretty dom
    PowRat -> "**"
    ReduceAddRatTensor -> "reduceAddRatTensor"
    ReduceMulRatTensor -> "reduceMulRatTensor"
    ReduceMinRatTensor -> "reduceMinRatTensor"
    ReduceMaxRatTensor -> "reduceMaxRatTensor"
    At -> "!"
    StackTensor {} -> "stack"
    ConstTensor -> "const"
    SearchRatTensor -> "search"

--------------------------------------------------------------------------------
-- Builtin datatype

-- | The builtin types after translation to loss functions (missing all builtins
-- that involve the Bool type).
data LossBuiltin
  = LossBuiltinFunction LossBuiltinFunction
  | LossBuiltinType LossBuiltinType
  | LossBuiltinConstructor LossBuiltinConstructor
  deriving (Show, Eq, Generic)

instance Pretty LossBuiltin where
  pretty = pretty . show

instance BuiltinHasIndexLiterals LossBuiltin where
  getIndexBuiltinLit e = case e of
    LossBuiltinConstructor (IndexLiteral n) -> Just n
    _ -> Nothing
  mkIndexBuiltinLit x = LossBuiltinConstructor (IndexLiteral x)

instance BuiltinHasIndexTensorLiterals LossBuiltin where
  mkIndexBuiltinTensorLit b = LossBuiltinConstructor (IndexTensorLiteral b)
  getIndexBuiltinTensorLit = \case
    LossBuiltinConstructor (IndexTensorLiteral b) -> Just b
    _ -> Nothing

instance BuiltinHasNatLiterals LossBuiltin where
  getNatBuiltinLit e = case e of
    LossBuiltinConstructor (NatLiteral b) -> Just b
    _ -> Nothing
  mkNatBuiltinLit x = LossBuiltinConstructor (NatLiteral x)

instance BuiltinHasNatTensorLiterals LossBuiltin where
  mkNatBuiltinTensorLit b = LossBuiltinConstructor (NatTensorLiteral b)
  getNatBuiltinTensorLit = \case
    LossBuiltinConstructor (NatTensorLiteral b) -> Just b
    _ -> Nothing

instance BuiltinHasRatLiterals LossBuiltin where
  mkRatBuiltinTensorLit b = LossBuiltinConstructor (RatTensorLiteral b)
  getRatBuiltinTensorLit = \case
    LossBuiltinConstructor (RatTensorLiteral b) -> Just b
    _ -> Nothing

instance BuiltinHasConstTensor LossBuiltin where
  isConstTensorBuiltin e = case e of
    LossBuiltinFunction ConstTensor -> True
    _ -> False
  mkConstTensorBuiltin = LossBuiltinFunction ConstTensor

instance BuiltinHasListLiterals LossBuiltin where
  isBuiltinNil e = case e of
    LossBuiltinConstructor Nil -> True
    _ -> False
  mkBuiltinNil = LossBuiltinConstructor Nil

  isBuiltinCons e = case e of
    LossBuiltinConstructor Cons -> True
    _ -> False
  mkBuiltinCons = LossBuiltinConstructor Cons
