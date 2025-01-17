module Vehicle.Data.Assertion where

import Control.DeepSeq (NFData)
import Data.Aeson (FromJSON, ToJSON)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import GHC.Generics
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Code.BooleanExpr (MaybeTrivial (..))
import Vehicle.Data.Code.LinearExpr
import Vehicle.Data.Hashing ()
import Vehicle.Data.Tensor (RatTensor, Tensor (..), TensorShape, allTensor)
import Vehicle.Prelude

--------------------------------------------------------------------------------
-- Relations

data Relation
  = OEq
  | OLe
  | OLt
  deriving (Eq, Ord)

relationToComparisonOp :: Relation -> ComparisonOp
relationToComparisonOp = \case
  OEq -> Eq
  OLe -> Le
  OLt -> Lt

instance Pretty Relation where
  pretty = pretty . relationToComparisonOp

--------------------------------------------------------------------------------
-- Strictness

data InequalityRelation
  = Strict
  | NonStrict
  deriving (Show, Eq, Ord, Generic)

instance NFData InequalityRelation

instance ToJSON InequalityRelation

instance FromJSON InequalityRelation

inequalityToRelation :: InequalityRelation -> Relation
inequalityToRelation = \case
  Strict -> OLe
  NonStrict -> OLt

instance Pretty InequalityRelation where
  pretty = pretty . inequalityToRelation

--------------------------------------------------------------------------------
-- Normalisation relations

data NormalisedRelation rel constant = NormalisedRelation
  { relation :: rel,
    linearExpr :: LinearExpr constant
  }
  deriving (Show, Eq, Ord, Generic)

instance (NFData constant, NFData rel) => NFData (NormalisedRelation rel constant)

instance (ToJSON constant, ToJSON rel) => ToJSON (NormalisedRelation rel constant)

instance (FromJSON constant, FromJSON rel) => FromJSON (NormalisedRelation rel constant)

--------------------------------------------------------------------------------
-- Assertions

type Inequality constant = NormalisedRelation InequalityRelation constant

type Equality constant = NormalisedRelation () constant

splitRelation :: NormalisedRelation Relation constant -> Either (Inequality constant) (Equality constant)
splitRelation r = case relation r of
  OEq -> Right $ r {relation = ()}
  OLe -> Left $ r {relation = NonStrict}
  OLt -> Left $ r {relation = Strict}

inequalityToNormRelation :: Inequality constant -> NormalisedRelation Relation constant
inequalityToNormRelation r = case relation r of
  Strict -> r {relation = OLt}
  NonStrict -> r {relation = OLe}

type Assertion = NormalisedRelation Relation RatTensor

assertionShape :: Assertion -> TensorShape
assertionShape ass = tensorShape (constantValue $ linearExpr ass)

checkTriviality :: Relation -> RatTensor -> Bool
checkTriviality op tensor = case op of
  OLe -> allTensor (<= 0.0) tensor
  OLt -> allTensor (< 0.0) tensor
  OEq -> isZero tensor

comparisonToAssertion :: ComparisonOp -> LinearExpr RatTensor -> LinearExpr RatTensor -> Assertion
comparisonToAssertion op e1 e2 = case op of
  Ne -> developerError "Cannot convert `Ne` to assertion"
  Eq -> NormalisedRelation OEq $ addExprs 1 (-1) e1 e2
  Lt -> NormalisedRelation OLt $ addExprs 1 (-1) e1 e2
  Le -> NormalisedRelation OLe $ addExprs 1 (-1) e1 e2
  Gt -> NormalisedRelation OLt $ addExprs (-1) 1 e1 e2
  Ge -> NormalisedRelation OLe $ addExprs (-1) 1 e1 e2

eliminateVarsInAssertion :: Map Variable (LinearExpr RatTensor) -> Assertion -> MaybeTrivial Assertion
eliminateVarsInAssertion f NormalisedRelation {..} = case eliminateVars f linearExpr of
  Right newExpr -> NonTrivial $ NormalisedRelation {linearExpr = newExpr, ..}
  Left tensor -> Trivial (checkTriviality relation tensor)

--------------------------------------------------------------------------------
-- Bounds

type Bound constant = Inequality constant

pattern Bound :: InequalityRelation -> LinearExpr constant -> Bound constant
pattern Bound s e = NormalisedRelation s e

{-# COMPLETE Bound #-}

type LowerBound constant = Bound constant

type UpperBound constant = Bound constant

-- | A FM solution for an normalised user variable is two lists of constraints.
-- The variable value must be greater than the first set of assertions, and less than
-- the second set of assertions.
data Bounds constant = Bounds
  { lowerBounds :: [LowerBound constant],
    upperBounds :: [UpperBound constant]
  }
  deriving (Show, Eq, Ord, Generic)

instance (NFData constant) => NFData (Bounds constant)

instance (ToJSON constant) => ToJSON (Bounds constant)

instance (FromJSON constant) => FromJSON (Bounds constant)

--------------------------------------------------------------------------------
-- Variable status

data UnderConstrainedVariableStatus
  = Unconstrained
  | BoundedAbove
  | BoundedBelow
  deriving (Show, Eq, Ord)

instance Pretty UnderConstrainedVariableStatus where
  pretty = \case
    Unconstrained -> "no lower or upper bound"
    BoundedAbove -> "no lower bound"
    BoundedBelow -> "no upper bound"

instance Semigroup UnderConstrainedVariableStatus where
  Unconstrained <> r = r
  r <> Unconstrained = r
  BoundedAbove <> r = r
  r <> BoundedAbove = r
  BoundedBelow <> BoundedBelow = BoundedBelow

prettyUnderConstrainedVariable :: (Pretty var) => (var, UnderConstrainedVariableStatus) -> Doc a
prettyUnderConstrainedVariable (var, constraint) =
  pretty var <+> "-" <+> pretty constraint

checkBoundsExist ::
  (Variable, Bounds constant) ->
  Either (Variable, UnderConstrainedVariableStatus) (NonEmpty (LowerBound constant), NonEmpty (UpperBound constant))
checkBoundsExist (var, Bounds {..}) = case (lowerBounds, upperBounds) of
  ([], []) -> Left (var, Unconstrained)
  ([], _) -> Left (var, BoundedAbove)
  (_, []) -> Left (var, BoundedBelow)
  (l : ls, u : us) -> Right (l :| ls, u :| us)
