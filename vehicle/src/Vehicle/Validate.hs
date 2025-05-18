module Vehicle.Validate
  ( ValidateOptions (..),
    validate,
  )
where

import Control.Monad (forM, when)
import Control.Monad.Trans (MonadIO (liftIO))
import Data.Aeson (ToJSON (..), Value (Object), object, (.=))
import Data.Aeson.Encode.Pretty (encodePretty')
import Data.Aeson.Key (fromString)
import Data.ByteString.Lazy.Char8 (unpack)
import System.FilePath ((</>))
import Vehicle.Data.Tensor (RationalTensor)
import Vehicle.Prelude
import Vehicle.Prelude.Logging
import Vehicle.Resource
import Vehicle.Verify.Specification (SpecificationCacheIndex (..), multiPropertyAddresses, properties)
import Vehicle.Verify.Specification.IO (readAssignmentsFromFolder, readPropertyResult, readSpecificationCacheIndex, specificationCacheIndexFileName)

--------------------------------------------------------------------------------
-- Proof validation

data ValidateOptions = ValidateOptions
  { verificationCache :: FilePath,
    outputAsJSON :: Bool,
    outputCounterExamples :: Bool
  }
  deriving (Eq, Show)

validate :: (MonadStdIO IO) => LoggingSettings -> ValidateOptions -> IO ()
validate loggingSettings checkOptions = runLoggerT loggingSettings $ do
  -- If the user has specified no logging target for check mode then
  -- default to command-line.
  status <- checkSpecificationStatus checkOptions
  counterExamples <- collectCounterexamples checkOptions

  if not $ outputAsJSON checkOptions
    then do
      -- Pretty print the status and counter-examples
      programOutput $ pretty status
      when (outputCounterExamples checkOptions) $ do
        programOutput $ line <> "Counterexamples:" <> line <> pretty counterExamples
    else do
      let statusJSON =
            if not $ outputCounterExamples checkOptions
              then toJSON status
              else do
                let nonEmptyCounterExamples = filter (\(CounterExampleResult assignments _) -> not (null assignments)) counterExamples
                 in case toJSON status of
                      Object o -> Object (o <> case toJSON (object ["counter-examples" .= toJSON nonEmptyCounterExamples]) of Object o' -> o'; _ -> mempty)
                      v -> v
      programOutput $ pretty $ unpack $ encodePretty' prettyJSONConfig statusJSON

checkSpecificationStatus ::
  (MonadIO m, MonadLogger m) =>
  ValidateOptions ->
  m ValidateResult
checkSpecificationStatus ValidateOptions {..} = do
  let cacheIndexFile = specificationCacheIndexFileName verificationCache
  SpecificationCacheIndex {..} <- liftIO $ readSpecificationCacheIndex cacheIndexFile
  maybeIntegrityError <- checkIntegrityOfResources resourcesIntegrityInfo
  case maybeIntegrityError of
    Just err -> return $ IntegrityError err
    Nothing -> do
      let propertyAddresses = concatMap (multiPropertyAddresses . snd) properties
      statuses <- forM propertyAddresses $ readPropertyResult verificationCache
      if and statuses
        then return Verified
        else return Unverified

-- | Collect counterexamples for all assignments in the verification cache.
collectCounterexamples :: (MonadStdIO m, MonadLogger m) => ValidateOptions -> m [CounterExampleResult]
collectCounterexamples ValidateOptions {..} = do
  let cacheIndexFile = specificationCacheIndexFileName verificationCache
  SpecificationCacheIndex {..} <- readSpecificationCacheIndex cacheIndexFile
  let propertyAddresses = concatMap (multiPropertyAddresses . snd) properties
  results <- forM propertyAddresses $ \addr -> do
    let assignmentsFolder = verificationCache </> layoutAsString (pretty addr) <> "-assignments"
    assignments <- readAssignmentsFromFolder assignmentsFolder
    return $ CounterExampleResult assignments (show $ pretty addr)
  return results

data ValidateResult
  = Verified
  | Unverified
  | IntegrityError ResourceIntegrityError

instance Pretty ValidateResult where
  pretty Verified = "Status: verified"
  pretty Unverified = "Status: unverified"
  pretty (IntegrityError err) = "Status: unknown" <> line <> line <> pretty err

instance ToJSON ValidateResult where
  toJSON validateResult = case validateResult of
    Verified -> object ["status" .= ("verified" :: String)]
    Unverified -> object ["status" .= ("unverified" :: String)]
    IntegrityError err ->
      object
        [ "status" .= ("unknown" :: String),
          "error" .= (show $ pretty err :: String)
        ]

data CounterExampleResult
  = CounterExampleResult
  { assignments :: [(String, RationalTensor)],
    property :: String
  }
  deriving (Show, Eq)

instance Pretty CounterExampleResult where
  pretty (CounterExampleResult assignments propertyName)
    | null assignments = mempty
    | otherwise =
        pretty propertyName
          <> line
          <> vsep (map (\(name, tensor) -> indent 2 $ pretty name <> ": " <> pretty tensor) assignments)

instance ToJSON CounterExampleResult where
  toJSON (CounterExampleResult assignments propertyName)
    | null assignments = toJSON ()
    | otherwise =
        object
          [ "property" .= propertyName,
            "assignments" .= map (\(name, tensor) -> object [fromString name .= show (pretty tensor)]) assignments
          ]
