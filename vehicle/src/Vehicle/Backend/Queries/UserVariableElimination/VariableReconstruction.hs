module Vehicle.Backend.Queries.UserVariableElimination.VariableReconstruction where

import Data.Foldable (foldlM)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set qualified as Set
import Vehicle.Backend.Queries.UserVariableElimination.Core
import Vehicle.Compile.FourierMotzkinElimination
import Vehicle.Compile.Prelude
import Vehicle.Data.Code.LinearExpr (evaluateExpr)
import Vehicle.Data.QuantifiedVariable
import Vehicle.Data.Tensor (RationalTensor, Tensor (..), pattern ZeroDimTensor)
import Vehicle.Verify.QueryFormat.Core
import Vehicle.Verify.Verifier.Core

--------------------------------------------------------------------------------
-- Variable reconstruction

reconstructUserVars ::
  (MonadLogger m) =>
  UserVariableReconstruction ->
  QueryVariableAssignment ->
  m UserVariableAssignment
reconstructUserVars (Reconstruction variables steps) networkVariableAssignment =
  logCompilerPass MidDetail "calculation of problem space witness" $ do
    let queryVariables = fmap (\(_a, _b, c) -> c) variables
    let vehicleVariableCtx = reverse $ fmap (\(_a, b, _c) -> b) variables
    logDebug MidDetail $ pretty steps
    let assignment = createInitialAssignment queryVariables networkVariableAssignment
    alteredAssignment <- foldlM applyReconstructionStep assignment steps
    finalAssignment <- createFinalAssignment vehicleVariableCtx alteredAssignment
    logDebug MidDetail $ "User variables:" <+> pretty finalAssignment
    return finalAssignment

--------------------------------------------------------------------------------
-- Mixed variable assignments

data MixedVariableAssignment = VariableAssignment
  { variableValues :: Map Variable RationalTensor,
    userVariables :: [TensorVariable]
  }

instance Pretty MixedVariableAssignment where
  pretty VariableAssignment {..} =
    "Variable values:" <+> prettyMap variableValues
      <> line
      <> "User variables:" <+> pretty userVariables
      <> line

-- | Lookups the values in the variable assignment and removes them from the
-- assignment. Returns either the first missing variable or the list of values
-- and the resulting assignment.
lookupElementVariables ::
  MixedVariableAssignment ->
  Tensor Variable ->
  Either Variable (Tensor Rational)
lookupElementVariables VariableAssignment {..} = traverse op
  where
    op var = case Map.lookup var variableValues of
      Nothing -> Left var
      Just (ZeroDimTensor value) -> Right value
      Just _ -> developerError "Element variables should have an empty tensor shape"

createInitialAssignment ::
  GenericBoundCtx (Maybe QueryVariable) ->
  QueryVariableAssignment ->
  MixedVariableAssignment
createInitialAssignment queryVariables (QueryVariableAssignment valuesByQueryVar) = do
  let queryVariableMap = Map.fromList $ mapMaybe (\(a, v) -> fmap (,v) a) $ zip queryVariables [0 ..]
  let mapQueryVariable var = fromMaybe (developerError ("Missing query variable" <+> pretty var)) (Map.lookup var queryVariableMap)
  let valuesByNetworkVar = ZeroDimTensor <$> Map.mapKeys mapQueryVariable valuesByQueryVar
  VariableAssignment
    { variableValues = valuesByNetworkVar,
      userVariables = mempty
    }

applyReconstructionStep ::
  (MonadLogger m) =>
  MixedVariableAssignment ->
  UserVariableReconstructionStep ->
  m MixedVariableAssignment
applyReconstructionStep assignment@VariableAssignment {..} step = do
  logDebug MidDetail $ "Variable assignment:" <> line <> indent 2 (pretty assignment)
  case step of
    ReconstructTensor varType var tensorVars ->
      logCompilerSection MidDetail ("Collapsing variables" <+> pretty tensorVars <+> "to single variable" <+> pretty var) $
        unreduceVariable varType var tensorVars assignment
    SolveEquality isTensorVar var eq -> do
      logCompilerSection MidDetail ("Reintroducing Gaussian-eliminated variable" <+> quotePretty var) $ do
        logDebug MidDetail $ "Using" <+> pretty step
        let errorOrValue = evaluateExpr eq variableValues
        case errorOrValue of
          Left missingVar -> developerError $ "Missing variable" <+> quotePretty missingVar <+> "required in Gaussian elimination of" <+> quotePretty var
          Right value -> do
            logDebug MidDetail $ "Result:" <+> pretty var <+> "=" <+> pretty value
            return $
              VariableAssignment
                { variableValues = Map.insert var value variableValues,
                  userVariables = if isTensorVar then var : userVariables else userVariables
                }
    SolveInequalities var solution -> do
      logCompilerSection MidDetail ("Reintroducing Fourier-Motzkin-eliminated variable" <+> quotePretty var) $ do
        let errorOrValue = reconstructFourierMotzkinVariableValue variableValues solution
        case errorOrValue of
          Left missingVar -> developerError $ "Missing variable" <+> quotePretty missingVar <+> "required in Fourier-Motzkin elimination of" <+> quotePretty var
          Right value ->
            return $
              VariableAssignment
                { variableValues = Map.insert var value variableValues,
                  userVariables = userVariables
                }

-- | Unreduces a previously reduced variable, removing the normalised
-- values from the assignment and adding the unreduced value back to the
-- assignment.
unreduceVariable ::
  (MonadLogger m) =>
  VariableType ->
  TensorVariable ->
  Tensor Variable ->
  MixedVariableAssignment ->
  m MixedVariableAssignment
unreduceVariable varType variable elementVariables assignment@VariableAssignment {..} = do
  let variableResults = lookupElementVariables assignment elementVariables
  case variableResults of
    Left missingVar ->
      developerError $
        "When reconstructing variable"
          <+> pretty variable
          <+> "in counter-example,"
          <+> "unable to find variable"
          <+> pretty missingVar
    Right variableValue ->
      return $
        assignment
          { variableValues = Map.insert variable variableValue variableValues,
            userVariables = if varType == UserVariable then variable : userVariables else userVariables
          }

createFinalAssignment ::
  (MonadLogger m) =>
  GenericBoundCtx Name ->
  MixedVariableAssignment ->
  m UserVariableAssignment
createFinalAssignment vehicleVariables (VariableAssignment {..}) = do
  let userVarSet = Set.fromList userVariables
  let userVarAssignments = Map.filterWithKey (\v _ -> v `Set.member` userVarSet) variableValues
  let lookupName lv = lookupLvInBoundCtx lv vehicleVariables
  let stringVarAssignments = Map.mapKeys lookupName userVarAssignments
  return $ UserVariableAssignment $ Map.toList stringVarAssignments
