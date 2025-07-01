module Vehicle.Backend.Agda.Interact
  ( writeAgdaFile,
    writeResultToFile,
  )
where

import Control.Monad.IO.Class (MonadIO (..))
import Data.Version (makeVersion)
import Vehicle.Backend.Prelude
import Vehicle.Prelude
import Vehicle.Prelude.Logging

writeAgdaFile ::
  (MonadLogger m, MonadIO m, MonadStdIO m) =>
  Maybe FilePath ->
  Doc a ->
  m ()
writeAgdaFile = writeResultToFile (Just agdaOutputFormat)

agdaOutputFormat :: ExternalOutputFormat
agdaOutputFormat =
  ExternalOutputFormat
    { formatName = "Agda",
      formatVersion = Just $ makeVersion [2, 6, 2],
      commentStyle = Line "--",
      emptyLines = True
    }
