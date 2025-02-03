module Vehicle.Compile
  ( CompileOptions (..),
    compile,
  )
where

import Control.Monad.Except (MonadError (..))
import Data.Aeson (ToJSON (..))
import Data.Aeson.Encode.Pretty (encodePretty')
import Data.ByteString.Lazy.Char8 (unpack)
import Vehicle.Backend.Agda
import Vehicle.Backend.LossFunction (convertToLossTensors)
import Vehicle.Backend.LossFunction.JSON
import Vehicle.Backend.LossFunction.LogicCompilation (compileLogic)
import Vehicle.Backend.LossFunction.Logics (dslFor)
import Vehicle.Backend.Prelude
import Vehicle.Backend.Queries
import Vehicle.Compile.Dependency (analyseDependenciesAndPrune)
import Vehicle.Compile.Error
import Vehicle.Compile.FunctionaliseResources (functionaliseResources)
import Vehicle.Compile.Monomorphisation (hoistInferableParameters)
import Vehicle.Compile.Prelude as CompilePrelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Compile.Type.Subsystem
import Vehicle.Data.Builtin.Decidability.Type ()
import Vehicle.Data.Builtin.Standard
import Vehicle.Prelude.Logging
import Vehicle.TypeCheck (TypeCheckOptions (..), runCompileMonad, typeCheckUserProg)
import Vehicle.Verify.QueryFormat

--------------------------------------------------------------------------------
-- Interface

data CompileOptions = CompileOptions
  { target :: Target,
    specification :: FilePath,
    declarationsToCompile :: DeclarationNames,
    networkLocations :: NetworkLocations,
    datasetLocations :: DatasetLocations,
    parameterValues :: ParameterValues,
    output :: Maybe FilePath,
    moduleName :: Maybe String,
    verificationCache :: Maybe FilePath,
    outputAsJSON :: Bool
  }
  deriving (Eq, Show)

compile :: (MonadStdIO IO) => LoggingSettings -> CompileOptions -> IO ()
compile loggingSettings options@CompileOptions {..} = runCompileMonad loggingSettings $ do
  (imports, prog) <-
    typeCheckUserProg $
      TypeCheckOptions
        { specification = specification,
          secondaryTypeSystem = Nothing
        }

  let mergedProg = mergeImports imports prog
  prunedProg <- analyseDependenciesAndPrune mergedProg declarationsToCompile

  let resources = Resources specification networkLocations datasetLocations parameterValues
  case target of
    VerifierQueries queryFormatID ->
      compileToQueryFormat prunedProg resources queryFormatID output
    LossFunction differentiableLogic ->
      compileToLossFunction differentiableLogic prunedProg output outputAsJSON
    ITP Agda ->
      compileToAgda options prunedProg

--------------------------------------------------------------------------------
-- Backend-specific compilation functions

compileToQueryFormat ::
  (MonadCompile m, MonadStdIO m) =>
  Prog Builtin ->
  Resources ->
  QueryFormatID ->
  Maybe FilePath ->
  m ()
compileToQueryFormat typedProg resources queryFormatID output = do
  let verifier = queryFormats queryFormatID
  compileToQueries verifier typedProg resources output

compileToAgda ::
  (MonadCompile m, MonadStdIO m) =>
  CompileOptions ->
  Prog Builtin ->
  m ()
compileToAgda CompileOptions {..} typedProg = do
  errorOrDecProg <- decidabilityTypeCheck typedProg
  case errorOrDecProg of
    Left err -> throwError err
    Right decProg -> do
      let agdaOptions = AgdaOptions verificationCache output moduleName
      agdaCode <- compileProgToAgda decProg agdaOptions
      writeAgdaFile output agdaCode

compileToLossFunction ::
  forall m.
  (MonadCompile m, MonadStdIO m) =>
  DifferentiableLogicID ->
  Prog Builtin ->
  Maybe FilePath ->
  Bool ->
  m ()
compileToLossFunction logicID typedProg outputFile outputAsJSON = do
  hoistedProg <- hoistInferableParameters typedProg
  functionalisedProg <- functionaliseResources hoistedProg
  let logic = dslFor logicID
  compiledLogic <- compileLogic logicID logic
  lossTensorProg <- convertToLossTensors compiledLogic functionalisedProg
  jsonProg <- convertToJSONProg lossTensorProg
  let outputText
        | outputAsJSON = pretty $ unpack $ encodePretty' prettyJSONConfig $ toJSON jsonProg
        | otherwise = prettyFriendly (convertFromJSONProg jsonProg)
  writeResultToFile Nothing outputFile outputText
