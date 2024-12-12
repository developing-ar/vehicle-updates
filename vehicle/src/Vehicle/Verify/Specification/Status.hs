module Vehicle.Verify.Specification.Status where

import Data.List.Split (chunksOf)
import Data.Set (Set)
import Data.Text (Text)
import System.Console.ANSI (Color (..))
import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.BooleanExpr (MaybeTrivial (..))
import Vehicle.Data.Code.Interface
import Vehicle.Data.QuantifiedVariable
import Vehicle.Data.Tensor (RationalTensor, TensorShape)
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

instance Pretty PropertyStatus where
  pretty propertyStatus = do
    let (verified, evidenceText) = case propertyStatus of
          PropertyCompleted maybeResult -> do
            case maybeResult of
              Trivial status -> (status, "(trivial)")
              NonTrivial (negated, status) -> do
                let witnessText = if negated then "counterexample" else "witness"
                case status of
                  UnSAT -> (negated, "proved no" <+> witnessText <+> "exists")
                  SAT Nothing -> (not negated, "no" <> witnessText <+> "found")
                  SAT Just {} -> (not negated, witnessText <+> "found")
          PropertyErrored (_, err) -> (False, if isTimeoutError err then "verifier timed out" else "verifier errored")
    pretty (statusSymbol verified) <+> "-" <+> evidenceText

--------------------------------------------------------------------------------
-- Verification status of a multi property

statusSymbol :: Bool -> String
statusSymbol verified = do
  let (colour, symbol) = if verified then (Green, "🗸") else (Red, "✗")
  setTextColour colour symbol

prettyNameAndStatus :: Text -> Bool -> Doc a
prettyNameAndStatus name verified = do
  pretty (statusSymbol verified) <+> pretty name

prettyUserVariableAssignment :: (Name, RationalTensor) -> Doc a
prettyUserVariableAssignment (var, variableValue) =
  pretty var <> ":" <+> pretty variableValue

assignmentToExpr :: TensorShape -> [Rational] -> Expr Builtin
assignmentToExpr [] [x] = IRatLiteral mempty (toRational x)
assignmentToExpr [] _ = developerError "Malformed tensor"
assignmentToExpr (dim : dims) xs = do
  let vecConstructor = Builtin mempty (BuiltinConstructor $ LVec dim)
  let inputVarIndicesChunks = chunksOf (product dims) xs
  let elems = fmap (Arg mempty Explicit Relevant . assignmentToExpr dims) inputVarIndicesChunks
  normAppList vecConstructor elems
