module Vehicle.List where

import Control.Monad.IO.Class (MonadIO (..))
import Data.Aeson (ToJSON (..))
import Data.Aeson.Encode.Pretty (encodePretty')
import Data.ByteString.Lazy.Char8 (unpack)
import Data.Text (Text, pack)
import GHC.Generics
import Vehicle.Backend.Prelude
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude hiding (Dataset, Network, Parameter)
import Vehicle.Compile.Print
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Prelude.Logging.Instance
import Vehicle.TypeCheck (TypeCheckOptions (..), runCompileMonad, typeCheckUserProg)

newtype ListOptions = ListOptions {specification :: FilePath}
  deriving (Eq, Show)

list :: (MonadStdIO IO) => LoggingSettings -> OutputAsJSON -> ListOptions -> IO ()
list loggingSettings outputAsJSON ListOptions {..} = runCompileMonad loggingSettings outputAsJSON $ do
  -- always typecheck first
  (imports, typedProg) <-
    typeCheckUserProg $
      TypeCheckOptions
        { specification = specification,
          secondaryTypeSystem = Nothing
        }
  let mergedProg = mergeImports imports typedProg
  printListableEntities mergedProg outputAsJSON

printListableEntities ::
  (MonadIO m, MonadCompile m, PrintableBuiltin builtin) =>
  Prog builtin ->
  Bool ->
  m ()
printListableEntities (Main decls) outputAsJSON = do
  let annotatedListEntities = filter (\decl -> isAbstractDecl decl || isPropertyDecl decl) decls
  let listDecls =
        foldl
          convertListEntity
          []
          annotatedListEntities
  let outputDocs =
        if outputAsJSON
          then pretty $ unpack $ encodePretty' prettyJSONConfig $ toJSON listDecls
          else pretty listDecls
  programOutput outputDocs
  where
    convertListEntity :: (PrintableBuiltin builtin) => [ListEntity] -> Decl builtin -> [ListEntity]
    convertListEntity accList decl = case convertDeclToListEntity decl of
      Nothing -> accList
      Just listEntity -> listEntity : accList

-- | Data Structure for listable entities
data ListEntity = ListEntity
  { entity :: ListableEntity,
    entityName :: Text,
    entityType :: Text,
    entityProvenance :: Provenance
  }
  deriving (Eq, Show, Generic)

instance ToJSON ListEntity

instance Pretty ListEntity where
  pretty listEntity =
    pretty (entity listEntity)
      <+> pretty (entityName listEntity)
      <+> pretty (entityType listEntity)
      <+> pretty (entityProvenance listEntity)

declToListableEntity :: Decl builtin -> Maybe ListableEntity
declToListableEntity b = case b of
  DefAbstract _ _ sort _ -> case sort of
    NetworkDef -> Just Network
    DatasetDef -> Just Dataset
    ParameterDef _ -> Just Parameter
    PostulateDef -> Nothing
  DefFunction _ _ anns _ _ -> if AnnProperty `elem` anns then Just Property else Nothing
  DefRecord {} -> Nothing

convertDeclToListEntity :: (PrintableBuiltin builtin) => Decl builtin -> Maybe ListEntity
convertDeclToListEntity decl = case declToListableEntity decl of
  Nothing -> Nothing
  Just listableEntity ->
    Just $
      ListEntity
        { entity = listableEntity,
          entityName = identifierName $ identifierOf decl,
          entityType = pack $ show $ prettyFriendlyEmptyCtx (typeOf decl),
          entityProvenance = provenanceOf decl
        }
