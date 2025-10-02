module Vehicle.List where

import Control.Monad
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Writer (MonadWriter (tell), execWriterT)
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
import Vehicle.Syntax.Builtin (Builtin (BuiltinFunction), BuiltinFunction (QuantifyRatTensor))
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

-- | Print all the listable entities in the program
printListableEntities ::
  (MonadIO m, MonadCompile m, PrintableBuiltin Builtin) =>
  Prog Builtin ->
  Bool ->
  m ()
printListableEntities (Main decls) outputAsJSON = do
  let annotatedListEntities = filter (\decl -> isAbstractDecl decl || isPropertyDecl decl) decls
  let listDecls =
        foldl
          convertListEntity
          []
          annotatedListEntities
  quantifiedVars <- execWriterT (listQuantifiedVariables decls)
  let allListEntities = listDecls ++ quantifiedVars
  let outputDocs =
        if outputAsJSON
          then pretty $ unpack $ encodePretty' prettyJSONConfig $ toJSON allListEntities
          else pretty allListEntities
  programOutput outputDocs
  where
    convertListEntity :: (PrintableBuiltin Builtin) => [ListEntity] -> Decl Builtin -> [ListEntity]
    convertListEntity accList decl = case convertDeclToListEntity decl of
      Nothing -> accList
      Just listEntity -> listEntity : accList

-- | Traverse the program to find all quantified variables
listQuantifiedVariables :: (MonadWriter [ListEntity] m) => [GenericDecl (Expr Builtin)] -> m ()
listQuantifiedVariables decls = forM_ decls traverseDeclsQ
  where
    traverseDeclsQ :: (MonadWriter [ListEntity] m) => GenericDecl (Expr Builtin) -> m ()
    traverseDeclsQ decl = case bodyOf decl of
      Nothing -> return ()
      Just e -> do
        _ <- traverseBuiltinsM filterQuantifiedVariables e
        return ()

    filterQuantifiedVariables :: (MonadWriter [ListEntity] m) => BuiltinUpdate m Builtin Builtin
    filterQuantifiedVariables p b args = case b of
      BuiltinFunction (QuantifyRatTensor _) -> case args of
        [_, Arg _ _ _ (Lam _ binder _)] -> case getBinderNameAndType binder of
          Just (name, typ, prov) -> do
            tell [ListEntity {entity = QuantifiedVariable, entityName = name, entityType = typ, entityProvenance = prov}]
            return (Builtin p b)
          Nothing -> return (Builtin p b)
        _ -> return (Builtin p b)
      _ -> return (Builtin p b)

    getBinderNameAndType :: Binder Builtin -> Maybe (Text, Text, Provenance)
    getBinderNameAndType binder = case nameOf binder of
      Nothing -> Nothing
      Just v -> Just (v, pack $ show $ prettyFriendlyEmptyCtx (typeOf binder), provenanceOf binder)

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

declToListableEntity :: Decl Builtin -> Maybe ListableEntity
declToListableEntity b = case b of
  DefAbstract _ _ sort _ -> case sort of
    NetworkDef -> Just Network
    DatasetDef -> Just Dataset
    ParameterDef _ -> Just Parameter
    PostulateDef -> Nothing
  DefFunction _ _ anns _ _ -> if AnnProperty `elem` anns then Just Property else Nothing
  DefRecord {} -> Nothing

convertDeclToListEntity :: (PrintableBuiltin Builtin) => Decl Builtin -> Maybe ListEntity
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
