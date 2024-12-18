module Vehicle.Syntax.Builtin.TypeClass where

import Control.DeepSeq (NFData (..))
import Data.Hashable (Hashable (..))
import Data.Serialize (Serialize)
import GHC.Generics (Generic)
import Prettyprinter (Pretty (..))
import Vehicle.Syntax.AST.Decl (ParameterSort)
import Vehicle.Syntax.Builtin.BasicOperations

--------------------------------------------------------------------------------
-- Type classes

data TypeClass
  = -- Operation type-classes
    HasEq EqualityOp
  | HasOrd OrderOp
  | HasQuantifier Quantifier
  | HasAdd
  | HasSub
  | HasMul
  | HasDiv
  | HasNeg
  | HasFold
  | HasMap
  | HasQuantifierIn Quantifier
  | -- Literal type-classes
    HasNatLits
  | HasRatLits
  | HasVecLits
  | -- Overloading of the tensor type
    IsTensorType
  | -- Declaration type restrictions
    ValidPropertyType
  | ValidParameterType ParameterSort
  | ValidNetworkType
  | ValidNetworkTensorType
  | ValidDatasetType
  | ValidDatasetListElementType
  | ValidDatasetTensorElementType
  deriving (Eq, Ord, Generic, Show)

instance NFData TypeClass

instance Hashable TypeClass

instance Serialize TypeClass

instance Pretty TypeClass where
  pretty = \case
    HasEq {} -> "HasEq"
    HasOrd {} -> "HasOrd"
    HasQuantifier q -> "Has" <> pretty q
    HasQuantifierIn q -> "Has" <> pretty q <> "In"
    HasAdd -> "HasAdd"
    HasSub -> "HasSub"
    HasMul -> "HasMul"
    HasDiv -> "HasDiv"
    HasNeg -> "HasNeg"
    HasMap -> "HasMap"
    HasFold -> "HasFold"
    HasNatLits -> "HasNatLiterals"
    HasRatLits -> "HasRatLiterals"
    HasVecLits -> "HasVecLiterals"
    IsTensorType -> "IsTensorType"
    ValidPropertyType -> "ValidPropertyType"
    ValidParameterType {} -> "ValidParameterType"
    ValidNetworkType -> "ValidNetworkType"
    ValidNetworkTensorType -> "ValidNetworkTensorType"
    ValidDatasetType -> "ValidDatasetType"
    ValidDatasetListElementType -> "ValidDatasetListElementType"
    ValidDatasetTensorElementType -> "ValidDatasetTensorElementType"

-- Builtin operations for type-classes
data TypeClassOp
  = -- | Needed to overload `Bool`/`Rat` as both `BoolElementType` in `Tensor Bool dims` and as `Tensor Bool []` in `Bool`
    FromNatTC
  | FromRatTC
  | -- Note we need to have `FromNat` and `FromRat` as actual functions as the
    -- `fromNat` requires us to inspect the actual value being cast in the type-checker
    -- when casting to `Index`. No such restriction applies to vector literals so we can
    -- have it as a literal in the type-class.
    VecLiteralTC
  | NegTC
  | AddTC
  | SubTC
  | MulTC
  | DivTC
  | EqualsTC EqualityOp
  | OrderTC OrderOp
  | MapTC
  | FoldTC
  | QuantifierTC Quantifier
  | TensorTypeTC
  deriving (Eq, Ord, Generic, Show)

instance NFData TypeClassOp

instance Hashable TypeClassOp

instance Serialize TypeClassOp

instance Pretty TypeClassOp where
  pretty = \case
    NegTC -> "-"
    AddTC -> "+"
    SubTC -> "-"
    MulTC -> "*"
    DivTC -> "/"
    FromNatTC -> "fromNat"
    FromRatTC -> "fromRat"
    VecLiteralTC {} -> "vec"
    EqualsTC op -> pretty op
    OrderTC op -> pretty op
    MapTC -> "map"
    FoldTC -> "fold"
    QuantifierTC q -> pretty q
    TensorTypeTC -> "TensorTC"
