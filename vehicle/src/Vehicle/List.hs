module Vehicle.List where

import Control.Monad.IO.Class (MonadIO (..))
import Data.Aeson (ToJSON (..))
import Data.Aeson.Encode.Pretty (encodePretty')
import Data.ByteString.Lazy.Char8 (unpack)
import Data.Text (Text, pack)
import GHC.Generics
import Vehicle.Backend.Prelude
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Prelude.Logging.Instance
import Vehicle.TypeCheck (TypeCheckOptions (..), runCompileMonad, typeCheckUserProg)

data ListOptions = ListOptions
  { listEntities :: ListableEntities,
    specification :: FilePath
  }
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
  case listEntities of
    ListableVariables {} -> printVariables mergedProg outputAsJSON
    ListableResources resourceType -> printResources mergedProg resourceType outputAsJSON

printResources ::
  (MonadIO m, MonadCompile m, PrintableBuiltin builtin) =>
  Prog builtin ->
  ListableResources ->
  Bool ->
  m ()
printResources (Main decls) listEntities outputAsJSON = do
  let filterFn = case listEntities of
        ExternalResources -> isExternalResourceDecl
        Properties -> isPropertyDecl
  let filteredDecls = filter filterFn decls
  let listDecls =
        fmap
          ( \decl ->
              convertDeclToListEntity
                decl
                $ maybe "" pretty (abstractSortOf decl)
          )
          filteredDecls
  let outputDocs =
        if outputAsJSON
          then pretty $ unpack $ encodePretty' prettyJSONConfig $ toJSON listDecls
          else pretty listDecls
  programOutput outputDocs

quantifiedVariableToListEntity :: Expr builtin -> Maybe ListEntity
quantifiedVariableToListEntity = \case
  BoundVar prov idx -> Just $ ListEntity {entitySort = "variable", entityName = pack (show idx), entityType = "quantified", entityProvenance = prov}
  _ -> Nothing

parseGenericProgForQuantifiedVariable :: GenericDecl (Expr builtin) -> Maybe ListEntity
parseGenericProgForQuantifiedVariable = \case
  DefFunction _ _ _ _ expr -> quantifiedVariableToListEntity expr
  DefAbstract _ _ _ expr -> quantifiedVariableToListEntity expr
  DefRecord _ _ _ expr _ -> quantifiedVariableToListEntity expr

listQuantifiedVariables :: [GenericDecl (Expr builtin)] -> [ListEntity]
listQuantifiedVariables [] = []
listQuantifiedVariables (decl : decls) = case parseGenericProgForQuantifiedVariable decl of
  Just entity -> entity : listQuantifiedVariables decls
  Nothing -> listQuantifiedVariables decls

printVariables ::
  (MonadIO m, MonadCompile m, PrintableBuiltin builtin) =>
  Prog builtin ->
  Bool ->
  m ()
printVariables (Main decls) outputAsJSON = do
  let listDecls = listQuantifiedVariables decls
  let outputDocs =
        if outputAsJSON
          then pretty $ unpack $ encodePretty' prettyJSONConfig $ toJSON listDecls
          else pretty listDecls
  programOutput outputDocs

-- | Data Structure for listable entities
data ListEntity = ListEntity
  { entitySort :: Text,
    entityName :: Text,
    entityType :: Text,
    entityProvenance :: Provenance
  }
  deriving (Eq, Show, Generic)

instance ToJSON ListEntity

instance Pretty ListEntity where
  pretty listEntity =
    pretty (entitySort listEntity)
      <+> pretty (entityName listEntity)
      <+> pretty (entityType listEntity)
      <+> pretty (entityProvenance listEntity)

convertDeclToListEntity :: (PrintableBuiltin builtin) => Decl builtin -> Doc a -> ListEntity
convertDeclToListEntity decl entitySort =
  ListEntity
    { entitySort = pack $ show entitySort,
      entityName = identifierName $ identifierOf decl,
      entityType = pack $ show $ prettyFriendlyEmptyCtx (typeOf decl),
      entityProvenance = provenanceOf decl
    }
