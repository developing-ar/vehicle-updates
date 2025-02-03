module Vehicle.Backend.Queries.Error
  ( diagnoseNonLinearity,
    diagnoseAlternatingQuantifiers,
  )
where

import Control.Monad.Except (MonadError (..))
import Vehicle.Backend.Prelude (TypingSystem (..))
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Compile.Type.Core (emptyInstanceDatabase)
import Vehicle.Compile.Type.Subsystem (typeCheckWithSubsystem)
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Data.Builtin.Linearity
import Vehicle.Data.Builtin.Linearity.Type ()
import Vehicle.Data.Builtin.Polarity
import Vehicle.Data.Builtin.Polarity.Type ()
import Vehicle.Data.Builtin.Standard
import Vehicle.Verify.QueryFormat.Core (QueryFormatID)

diagnoseNonLinearity ::
  forall m.
  (MonadCompile m) =>
  QueryFormatID ->
  Prog Builtin ->
  DeclProvenance ->
  m CompileError
diagnoseNonLinearity queryFormat prog propertyProv@(propertyIdentifier, _) = do
  setCallDepth 0
  logDebug MinDetail $
    "ERROR: found non-linear property. Switching to linearity type-checking mode for"
      <+> quotePretty propertyIdentifier
      <> line

  subTypedProg <- typeCheckWithSubsystem LinearityTypes emptyInstanceDatabase handleUnexpectedError prog

  -- Extract and diagnose the type.
  propertyType <- findDeclType propertyIdentifier subTypedProg
  case propertyType of
    Builtin _ (Linearity (NonLinear source)) -> do
      throwError $ UnsupportedNonLinearConstraint queryFormat propertyProv (Right source)
    _ -> handleUnexpectedError (DevError $ "Unexpected linearity type for property" <+> quotePretty propertyIdentifier)
  where
    handleUnexpectedError :: (MonadCompile m) => CompileError -> m a
    handleUnexpectedError err =
      throwError $ UnsupportedNonLinearConstraint queryFormat propertyProv (Left err)

diagnoseAlternatingQuantifiers ::
  forall m.
  (MonadCompile m) =>
  QueryFormatID ->
  Prog Builtin ->
  DeclProvenance ->
  m CompileError
diagnoseAlternatingQuantifiers queryFormat prog propertyProv@(propertyIdentifier, _) = do
  setCallDepth 0
  logDebug MinDetail $
    "ERROR: found property with alterating quantifiers. Switching to polarity type-checking mode for"
      <+> quotePretty propertyIdentifier
      <> line

  subTypedProg <- typeCheckWithSubsystem PolarityTypes emptyInstanceDatabase handleUnexpectedError prog

  -- Extract and diagnose the type.
  propertyType <- findDeclType propertyIdentifier subTypedProg
  case propertyType of
    Builtin _ (Polarity (MixedSequential q p pp2)) -> do
      throwError $ UnsupportedAlternatingQuantifiers queryFormat propertyProv (Right (q, p, pp2))
    _ -> compilerDeveloperError $ "Unexpected polarity type for property" <+> quotePretty propertyIdentifier <> ":" <+> prettyVerbose propertyType
  where
    handleUnexpectedError :: (MonadCompile m) => CompileError -> m a
    handleUnexpectedError err =
      throwError $ UnsupportedAlternatingQuantifiers queryFormat propertyProv (Left err)

findDeclType :: (MonadCompile m) => Identifier -> Prog builtin -> m (Expr builtin)
findDeclType ident (Main decls) = do
  let candidates = filter (\decl -> identifierOf decl == ident) decls
  case candidates of
    [property] -> return $ typeOf property
    _ -> compilerDeveloperError $ "Could not find property" <+> quotePretty ident <+> "in program after subtyping."

removeImplicitAndInstanceArgs ::
  forall m builtin.
  (MonadCompile m, PrintableBuiltin builtin) =>
  Prog builtin ->
  m (Prog builtin)
removeImplicitAndInstanceArgs prog =
  logCompilerPass MaxDetail "removal of implicit arguments" $ do
    result <- traverse go prog
    logCompilerPassOutput $ prettyExternal result
    return result
  where
    go :: Expr builtin -> m (Expr builtin)
    go expr = case expr of
      App fun args -> do
        fun' <- go fun
        let nonImplicitArgs = NonEmpty.filter isExplicit args
        nonImplicitArgs' <- traverse (traverse go) nonImplicitArgs
        return $ normAppList fun' nonImplicitArgs'
      BoundVar {} -> return expr
      FreeVar {} -> return expr
      Universe {} -> return expr
      Meta {} -> return expr
      Hole {} -> return expr
      Builtin {} -> return expr
      Pi p binder res -> Pi p <$> traverse go binder <*> go res
      Lam p binder body
        | isExplicit binder || not (isTypeUniverse (typeOf binder)) ->
            Lam p <$> traverse go binder <*> go body
        | otherwise -> do
            -- TODO This is a massive hack to get around the unused implicit
            -- {l} argument in `mapVector` in the standard library that isn't
            -- handled by monomorphisation.
            -- STILL NEEDED?
            body' <- go body
            let removedBody = Hole p "_" `substDBInto` body'
            return removedBody
      Let p bound binder body -> Let p <$> go bound <*> traverse go binder <*> go body
