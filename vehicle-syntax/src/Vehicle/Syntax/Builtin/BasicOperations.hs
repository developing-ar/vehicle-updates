-- | This module exports the datatype representations of the core builtin symbols.
module Vehicle.Syntax.Builtin.BasicOperations where

import Control.DeepSeq (NFData (..))
import Data.Aeson (FromJSON, ToJSON)
import Data.Hashable (Hashable (..))
import Data.Serialize (Serialize)
import Data.Serialize.Text ()
import Data.Text (Text)
import GHC.Generics (Generic)
import Prettyprinter (Doc, Pretty (..))

--------------------------------------------------------------------------------
-- Function positions

-- | Represents whether something is an input or an output of a function
data FunctionPosition
  = FunctionInput Text Int
  | FunctionOutput Text
  deriving (Eq, Ord, Show, Generic)

instance NFData FunctionPosition

instance Hashable FunctionPosition

instance Serialize FunctionPosition

instance Pretty FunctionPosition where
  pretty = \case
    FunctionInput n i -> "Input[" <> pretty n <> "][" <> pretty i <> "]"
    FunctionOutput n -> "Output[" <> pretty n <> "]"

--------------------------------------------------------------------------------
-- EqualityOp

data EqualityOp
  = Eq
  | Neq
  deriving (Eq, Ord, Show, Generic)

instance Hashable EqualityOp

instance Serialize EqualityOp

instance NFData EqualityOp

instance Pretty EqualityOp where
  pretty = \case
    Eq -> "=="
    Neq -> "!="

equalityOpName :: EqualityOp -> Doc a
equalityOpName = \case
  Eq -> "equals"
  Neq -> "notEquals"

equalityOp :: (Eq a) => EqualityOp -> (a -> a -> Bool)
equalityOp Eq = (==)
equalityOp Neq = (/=)

--------------------------------------------------------------------------------
-- Orders

data OrderOp
  = Le
  | Lt
  | Ge
  | Gt
  deriving (Eq, Ord, Show, Generic)

instance NFData OrderOp

instance Hashable OrderOp

instance Serialize OrderOp

instance Pretty OrderOp where
  pretty = \case
    Le -> "<="
    Lt -> "<"
    Ge -> ">="
    Gt -> ">"

orderOp :: (Ord a) => OrderOp -> (a -> a -> Bool)
orderOp Le = (<=)
orderOp Lt = (<)
orderOp Ge = (>=)
orderOp Gt = (>)

orderOpName :: OrderOp -> Doc a
orderOpName = \case
  Le -> "leq"
  Lt -> "lt"
  Ge -> "geq"
  Gt -> "gt"

isStrict :: OrderOp -> Bool
isStrict order = order == Lt || order == Gt

isForward :: OrderOp -> Bool
isForward order = order == Lt || order == Le

flipStrictness :: OrderOp -> OrderOp
flipStrictness = \case
  Le -> Lt
  Lt -> Le
  Ge -> Gt
  Gt -> Ge

flipOrder :: OrderOp -> OrderOp
flipOrder = \case
  Le -> Ge
  Lt -> Gt
  Ge -> Le
  Gt -> Lt

chainable :: OrderOp -> OrderOp -> Bool
chainable e1 e2 = e1 == e2 || e1 == flipStrictness e2

--------------------------------------------------------------------------------
-- Strictness

data Strictness
  = Strict
  | NonStrict
  deriving (Show, Eq, Ord, Generic)

instance NFData Strictness

instance ToJSON Strictness

instance FromJSON Strictness

--------------------------------------------------------------------------------
-- Quantifiers

data Quantifier
  = Forall
  | Exists
  deriving (Show, Eq, Ord, Generic)

instance NFData Quantifier

instance Hashable Quantifier

instance ToJSON Quantifier

instance Serialize Quantifier

instance Pretty Quantifier where
  pretty = \case
    Forall -> "forall"
    Exists -> "exists"

--------------------------------------------------------------------------------
-- Domains

data OrderDomain
  = OrderIndex
  | OrderNat
  | OrderRatTensor
  deriving (Eq, Ord, Show, Generic)

instance NFData OrderDomain

instance Hashable OrderDomain

instance Serialize OrderDomain

instance Pretty OrderDomain where
  pretty = \case
    OrderNat -> "Nat"
    OrderIndex -> "Index"
    OrderRatTensor -> "RatTensor"

data EqualityDomain
  = EqIndex
  | EqNat
  | EqRatTensor
  deriving (Eq, Ord, Show, Generic)

instance NFData EqualityDomain

instance Hashable EqualityDomain

instance Serialize EqualityDomain

instance Pretty EqualityDomain where
  pretty = \case
    EqIndex -> "Index"
    EqNat -> "Nat"
    EqRatTensor -> "RatTensor"

data NegDomain
  = NegRatTensor
  deriving (Eq, Ord, Show, Generic)

instance NFData NegDomain

instance Hashable NegDomain

instance Serialize NegDomain

instance Pretty NegDomain where
  pretty = \case
    NegRatTensor -> "RatTensor"

data AddDomain
  = AddNat
  | AddRatTensor
  deriving (Eq, Ord, Show, Generic)

instance NFData AddDomain

instance Hashable AddDomain

instance Serialize AddDomain

instance Pretty AddDomain where
  pretty = \case
    AddNat -> "Nat"
    AddRatTensor -> "RatTensor"

data SubDomain
  = SubRatTensor
  deriving (Eq, Ord, Show, Generic)

instance NFData SubDomain

instance Hashable SubDomain

instance Serialize SubDomain

instance Pretty SubDomain where
  pretty = \case
    SubRatTensor -> "RatTensor"

data MulDomain
  = MulNat
  | MulRatTensor
  deriving (Eq, Ord, Show, Generic)

instance NFData MulDomain

instance Hashable MulDomain

instance Serialize MulDomain

instance Pretty MulDomain where
  pretty = \case
    MulNat -> "Nat"
    MulRatTensor -> "RatTensor"

data DivDomain
  = DivRatTensor
  deriving (Eq, Ord, Show, Generic)

instance NFData DivDomain

instance Hashable DivDomain

instance Serialize DivDomain

instance Pretty DivDomain where
  pretty = \case
    DivRatTensor -> "RatTensor"

data MinDomain
  = MinRatTensor
  deriving (Eq, Ord, Show, Generic)

instance NFData MinDomain

instance Hashable MinDomain

instance Serialize MinDomain

instance Pretty MinDomain where
  pretty = \case
    MinRatTensor -> "RatTensor"

data MaxDomain
  = MaxRatTensor
  deriving (Eq, Ord, Show, Generic)

instance NFData MaxDomain

instance Hashable MaxDomain

instance Serialize MaxDomain

instance Pretty MaxDomain where
  pretty = \case
    MaxRatTensor -> "RatTensor"

data FromRatDomain
  = FromRatToRat
  deriving (Eq, Ord, Show, Generic)

instance Pretty FromRatDomain where
  pretty = \case
    FromRatToRat -> "Rat"

instance NFData FromRatDomain

instance Hashable FromRatDomain

instance Serialize FromRatDomain

data FromNatDomain
  = -- This is actually needed as it takes an empty type-class parameter (see typing module)
    FromNatToNat
  | FromNatToIndex
  | FromNatToRat
  deriving (Eq, Ord, Show, Generic)

instance Pretty FromNatDomain where
  pretty = \case
    FromNatToNat -> "Nat"
    FromNatToIndex -> "Index"
    FromNatToRat -> "Rat"

instance Serialize FromNatDomain

instance NFData FromNatDomain

instance Hashable FromNatDomain

{-
--------------------------------------------------------------------------------
-- Tensor element types

data TensorElementType
  = BoolElementType
  | IndexElementType
  | NatElementType
  | RatElementType
  deriving (Eq, Ord, Generic, Show)

instance NFData TensorElementType

instance Hashable TensorElementType

instance Serialize TensorElementType

instance Pretty TensorElementType where
  pretty = \case
    BoolElementType -> "Bool"
    NatElementType -> "Bool"
    IndexElementType -> "Bool"
    RatElementType -> "Rat"
-}
