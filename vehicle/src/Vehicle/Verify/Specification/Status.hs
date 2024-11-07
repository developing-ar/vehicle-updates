module Vehicle.Verify.Specification.Status where

import Data.Set (Set)
import System.Console.ANSI (Color (..))
import Vehicle.Compile.Prelude
import Vehicle.Data.Code.BooleanExpr (MaybeTrivial (..))
import Vehicle.Data.QuantifiedVariable
import Vehicle.Data.Tensor (RationalTensor)
import Vehicle.Verify.Core
import Vehicle.Verify.QueryFormat.Core (QueryVariable)
import Vehicle.Verify.Specification (QueryMetaData)

class IsVerified a where
  isVerified :: a -> Bool

instance IsVerified (QueryResult witness) where
  isVerified = \case
    SAT {} -> True
    UnSAT -> False

evaluateQuery :: QuerySetNegationStatus -> QueryResult witness -> Bool
evaluateQuery negated q = negated `xor` isVerified q

--------------------------------------------------------------------------------
-- Verification status of a single property

data VerificationError
  = UnsupportedMultipleNetworks MetaNetwork
  | VerifierTerminatedByOS Int
  | VerifierError String
  | VerifierOutputMalformed (Doc ())
  | VerifierIncompleteWitness (Set QueryVariable)
  | VerifierTimedOut
  deriving (Show)

isTimeoutError :: VerificationError -> Bool
isTimeoutError = \case
  VerifierTimedOut -> True
  _ -> False

type CompletedPropertyStatus =
  MaybeTrivial (QuerySetNegationStatus, QueryResult UserVariableAssignment)

data PropertyStatus
  = PropertyCompleted CompletedPropertyStatus
  | PropertyErrored (QueryMetaData, VerificationError)

instance IsVerified PropertyStatus where
  isVerified = \case
    PropertyCompleted maybeResult -> case maybeResult of
      Trivial b -> b
      NonTrivial (negated, result) -> evaluateQuery negated result
    PropertyErrored {} -> False

--------------------------------------------------------------------------------
-- Verification status of a multi property

statusSymbol :: Maybe Bool -> String
statusSymbol verified = do
  let (colour, symbol) = case verified of
        Just True -> (Green, "🗸")
        Nothing -> (Yellow, "?")
        Just False -> (Red, "✗")
  setTextColour colour symbol

prettyUserVariableAssignment :: (Name, RationalTensor) -> Doc a
prettyUserVariableAssignment (var, variableValue) =
  pretty var <> ":" <+> pretty variableValue
