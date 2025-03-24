module Vehicle.Syntax.Builtin.Derived where

import Control.DeepSeq (NFData)
import Data.Hashable (Hashable)
import Data.Serialize (Serialize)
import Data.Text (pack)
import GHC.Generics (Generic)
import Prettyprinter (Pretty (..))
import Vehicle.Syntax.AST.Name
import Vehicle.Syntax.Builtin.BasicOperations

data DerivedFunction
  = TypeAnn
  | QuantifyIndex Quantifier
  | QuantifyInList Quantifier
  | CompareRatTensorReduced ComparisonOp
  | AppendList
  deriving (Eq, Show, Ord, Generic)

instance Pretty DerivedFunction where
  pretty = \case
    TypeAnn -> "typeAnn"
    QuantifyIndex q -> pretty q <> "Index"
    QuantifyInList q -> pretty q <> "InList"
    AppendList -> "appendList"
    CompareRatTensorReduced op -> comparisonOpName op <> "RatTensorReduced"

instance HasIdentifier DerivedFunction where
  identifierOf f = stdlibIdentifier $ pack $ show f

instance HasName DerivedFunction Name where
  nameOf = nameOf . identifierOf

instance NFData DerivedFunction

instance Hashable DerivedFunction

instance Serialize DerivedFunction
