{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Vehicle.Verify.Specification.Execute.Reporting
  ( MonadProgressReporter (..),
    ProgressEvent (..),
    runTextProgressReporterT,
    runJSONProgressReporterT,
  )
where

import Control.Monad (when)
import Control.Monad.Except (ExceptT, MonadTrans (..))
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Identity (IdentityT)
import Control.Monad.Reader (MonadReader (..), ReaderT (..))
import Control.Monad.State (StateT (..), evalStateT, execStateT)
import Data.Aeson qualified as Aeson
import Data.Aeson.Types
import Data.ByteString.Lazy qualified as LazyText
import Data.ByteString.Lazy.Char8 qualified as BSL
import Data.Text (pack)
import GHC.Generics (Generic)
import Prettyprinter (fill)
import System.IO (stdout)
import System.ProgressBar
import Vehicle.Compile.Prelude
import Vehicle.Data.Code.BooleanExpr (MaybeTrivial (..))
import Vehicle.Data.QuantifiedVariable (UserVariableAssignment (..))
import Vehicle.Data.Tensor (TensorIndices)
import Vehicle.Prelude.IO qualified as VIO (MonadStdIO (writeStdoutLn))
import Vehicle.Verify.Core
import Vehicle.Verify.Specification (QueryMetaData (..))
import Vehicle.Verify.Specification.Status
import Vehicle.Verify.Verifier.Core

--------------------------------------------------------------------------------
-- Interface
--------------------------------------------------------------------------------
--
-- Mechanism for reporting events that happen during execution of a verification plan

class MonadProgressReporter m where
  reportMultiProperty :: Name -> m () -> m ()
  reportProperty :: PropertyAddress -> m PropertyStatus -> m PropertyStatus
  reportQuery :: QueryAddress -> m (QueryResult UserVariableAssignment) -> m (QueryResult UserVariableAssignment)

instance (MonadProgressReporter m) => MonadProgressReporter (ReaderT a m)

instance (MonadProgressReporter m) => MonadProgressReporter (ExceptT a m)

--------------------------------------------------------------------------------
-- Multi-property summary

data MultiPropertySummary = MultiPropertySummary
  { numberVerified :: Int,
    numberFalsified :: Int,
    numberTimedOut :: Int,
    numberErrored :: Int
  }
  deriving (Generic)

instance Semigroup MultiPropertySummary where
  s1 <> s2 =
    MultiPropertySummary
      { numberVerified = numberVerified s1 + numberVerified s2,
        numberFalsified = numberFalsified s1 + numberFalsified s2,
        numberTimedOut = numberTimedOut s1 + numberTimedOut s2,
        numberErrored = numberErrored s1 + numberErrored s2
      }

instance Monoid MultiPropertySummary where
  mempty =
    MultiPropertySummary
      { numberVerified = 0,
        numberFalsified = 0,
        numberTimedOut = 0,
        numberErrored = 0
      }

instance ToJSON MultiPropertySummary

makeMultiPropertyStatus :: PropertyStatus -> MultiPropertySummary
makeMultiPropertyStatus status = case status of
  PropertyErrored (_, VerifierTimedOut) -> mempty {numberTimedOut = 1}
  PropertyErrored _ -> mempty {numberErrored = 1}
  _
    | isVerified status -> mempty {numberVerified = 1}
    | otherwise -> mempty {numberFalsified = 1}

--------------------------------------------------------------------------------
-- Property summary

data PropertySummary

--------------------------------------------------------------------------------
-- Query event

-- JSON event types
newtype QuerySummary = QuerySummary
  { satisfied :: Bool
  }
  deriving (Generic)

instance ToJSON QuerySummary

--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------
-- Text progress reporter

newtype TextReporterT m a = TextReporterT
  { unTextReporterT :: StateT MultiPropertySummary (ReaderT (Maybe (ProgressBar ())) m) a
  }
  deriving (Functor, Applicative, Monad)

runTextProgressReporterT :: (MonadIO m) => TextReporterT m a -> m a
runTextProgressReporterT fn = do
  programOutput "Beginning verification"
  result <- runReaderT (evalStateT (unTextReporterT fn) mempty) Nothing
  programOutput "Verification complete"
  return result

instance (MonadStdIO m) => MonadProgressReporter (TextReporterT m) where
  reportMultiProperty name checkMultiPropertyFn = TextReporterT $ do
    _
    result <- unTextReporterT checkMultiPropertyFn
    textMultiPropertyComplete name _ -- programOutput $ "  " <> finalDoc
    return result

  reportProperty propertyAddress checkPropertyFn = TextReporterT $ do
    progressBar <- createProgressBar propertyAddress _
    result <- unTextReporterT checkPropertyFn
    propertyCompleteText result progressBar
    return result

  reportQuery queryAddress checkQueryFn = TextReporterT $ do
    progressBar <- asks _
    result <- unTextReporterT checkQueryFn
    textQueryComplete progressBar
    return result

instance (MonadLogger m) => MonadLogger (TextReporterT m) where
  enterCompilerPass = lift . enterCompilerPass
  exitCompilerPass = lift exitCompilerPass
  setCallDepth = lift . setCallDepth
  getCallDepth = lift getCallDepth
  incrCallDepth = lift incrCallDepth
  decrCallDepth = lift decrCallDepth
  getDebugLevel = lift getDebugLevel
  logMessage = lift . logMessage
  logWarning = lift . logWarning

createProgressBar :: (MonadStdIO m) => PropertyAddress -> Int -> m (ProgressBar ())
createProgressBar (PropertyAddress _ name indices) numberOfQueries = do
  let propertyName = LazyText.fromStrict $ intercalate "!" (name : fmap (pack . show) indices)
  let style =
        defStyle
          { stylePrefix = msg ("  " <> propertyName),
            stylePostfix = exact <> msg " queries",
            styleWidth = ConstantWidth 80
          }
  let initialProgress = Progress 0 numberOfQueries ()
  liftIO $ hNewProgressBar stdout style 10 initialProgress

propertyCompleteText :: PropertyStatus -> ProgressBar () -> m ()
propertyCompleteText propertyStatus progressBar = do
  -- Print result to command line
  let verifierName = pretty (verifierID verifier)
  let (verified, evidenceText) = case propertyStatus of
        PropertyCompleted maybeResult -> do
          case maybeResult of
            Trivial status -> (Just status, "(trivial)")
            NonTrivial (negated, status) -> do
              let witnessText = if negated then "counterexample" else "witness"
              case status of
                UnSAT -> (Just negated, verifierName <+> "proved no" <+> witnessText <+> "exists")
                SAT Nothing -> (Just (not negated), verifierName <+> "found no" <> witnessText)
                SAT Just {} -> (Just (not negated), verifierName <+> "found a" <+> witnessText)
        PropertyErrored (_, err) -> do
          let cause = if isTimeoutError err then "timed out" else "errored"
          (Nothing, verifierName <+> cause)
  VIO.writeStdoutLn (layoutAsText $ "    result: " <> pretty (statusSymbol verified) <+> "-" <+> evidenceText)
  -- Output any additional information
  case result of
    PropertyCompleted status -> case status of
      NonTrivial (_, SAT (Just (UserVariableAssignment assignments))) -> do
        -- Output assignments to command line
        unless noSatPrint $ do
          let assignmentDocs = vsep (fmap prettyUserVariableAssignment assignments)
          let witnessDoc = indent 6 assignmentDocs
          liftIO $ TIO.hPutStrLn stdout (layoutAsText witnessDoc)

        -- Output assignments to file
        let witnessFolder = verificationCache </> layoutAsString (pretty address) <> "-assignments"
        liftIO $ createDirectoryIfMissing True witnessFolder
        forM_ assignments $ \(var, tensor) -> do
          let file = witnessFolder </> show var
          let dims = Vector.fromList (shapeOf tensor)
          -- TODO got to be a better way to do this conversion...
          let unboxedVector = Vector.fromList $ BoxedVector.toList (fmap realToFrac (Tensor.toVector tensor))
          let idxData = IDXDoubles IDXDouble dims unboxedVector
          liftIO $ encodeIDXFile idxData file
      _ -> return ()
    PropertyErrored (QueryMetaData {..}, err) -> do
      let VerificationErrorAction {..} = convertVerificationError verifier queryAddress err

      reproducerMessage <-
        if reproducerIsUseful
          then createReproducer verifier verifierExecutable verificationCache metaNetwork queryAddress
          else return ""

      unless (isTimeoutError err) $ do
        let finalMessage = "\nError: " <> verificationErrorMessage <> reproducerMessage
        writeStderrLn (layoutAsText finalMessage)

  -- Close progress bar if human mode and incomplete
  when (queriesExecuted < numberOfQueries) $
    closePropertyProgressBar progressBar

closeProgressBar :: (MonadIO m) => ProgressBar () -> m ()
closeProgressBar _ = VIO.writeStdoutLn ""

textQueryComplete :: (MonadIO m) => ProgressBar () -> m ()
textQueryComplete progressBar = liftIO $ incProgress progressBar 1

textMultiPropertyComplete :: (MonadLogger m) => Name -> MultiPropertySummary -> m ()
textMultiPropertyComplete name MultiPropertySummary {..} = do
  let results =
        [ ("verified", numberVerified),
          ("falsified", numberFalsified),
          ("timed-out", numberTimedOut),
          ("errored", numberErrored)
        ] ::
          [(String, Int)]
  let totalSize = sum $ fmap snd results

  when (totalSize > 1) $ do
    let maxTextLength = maximum $ fmap (length . fst) results
    let prettyResult (t, x) = fill (maxTextLength + 1) (pretty t <> ":") <+> pretty x <> "/" <> pretty totalSize
    let finalDoc = pretty name <> ":" <> line <> indent 4 (vsep (fmap prettyResult results))
    programOutput finalDoc

--------------------------------------------------------------------------------
-- JSON progress reporter

newtype JSONReporterT m a = JSONReporterT
  { unJSONReporterT :: IdentityT m a
  }
  deriving (Functor, Applicative, Monad)

runJSONProgressReporterT :: (MonadIO m) => JSONReporterT m a -> m a
runJSONProgressReporterT fn = do
  outputEvent VerificationStart
  result <- _ $ unJSONReporterT fn
  outputEvent VerificationFinished
  return result

data ProgressEvent
  = VerificationStart
  | MultiPropertyStart Name
  | PropertyStart PropertyAddress
  | QueryStart QueryAddress
  | QueryComplete QueryAddress Bool
  | PropertyComplete PropertyAddress PropertySummary
  | MultiPropertyComplete Name MultiPropertySummary
  | VerificationFinished
  deriving (Generic)

instance (MonadStdIO m) => MonadProgressReporter (JSONReporterT m) where
  reportMultiProperty name checkMultiProperty = JSONReporterT $ do
    outputEvent $ MultiPropertyStart name
    result <- unJSONReporterT checkMultiProperty
    outputEvent $ MultiPropertyComplete name _
    return result

  reportProperty propertyAddress checkPropertyFn = JSONReporterT $ do
    outputEvent $ PropertyStart propertyAddress
    result <- unJSONReporterT checkPropertyFn
    outputEvent $ PropertyComplete propertyAddress _
    return result

  reportQuery queryAddress checkQueryFn = JSONReporterT $ do
    outputEvent $ QueryStart queryAddress
    result <- unJSONReporterT checkQueryFn
    outputEvent $ QueryComplete queryAddress (querySatisified result)
    return result

instance (MonadLogger m) => MonadLogger (JSONReporterT m) where
  enterCompilerPass = lift . enterCompilerPass
  exitCompilerPass = lift exitCompilerPass
  setCallDepth = lift . setCallDepth
  getCallDepth = lift getCallDepth
  incrCallDepth = lift incrCallDepth
  decrCallDepth = lift decrCallDepth
  getDebugLevel = lift getDebugLevel
  logMessage = lift . logMessage
  logWarning = lift . logWarning

outputEvent :: (MonadStdIO m) => ProgressEvent -> m ()
outputEvent event = liftIO $ BSL.putStrLn $ Aeson.encode event
