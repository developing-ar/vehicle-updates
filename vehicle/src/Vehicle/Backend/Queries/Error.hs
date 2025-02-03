module Vehicle.Backend.Queries.Error
  ( diagnoseNonLinearity,
    diagnoseAlternatingQuantifiers,
  )
where

import Control.Monad.Except (MonadError (..))
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Compile.Type.Subsystem (linearityTypeCheck, polarityTypeCheck)
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

  errorOrLinearityProg <- linearityTypeCheck prog
  case errorOrLinearityProg of
    Left err -> handleUnexpectedError err
    Right linearityProg -> do
      -- Extract and diagnose the type.
      propertyType <- findDeclType propertyIdentifier linearityProg
      case propertyType of
        Builtin _ (Linearity (NonLinear source)) -> do
          return $ UnsupportedNonLinearConstraint queryFormat propertyProv (Right source)
        _ -> handleUnexpectedError (DevError $ "Unexpected linearity type for property" <+> quotePretty propertyIdentifier)
  where
    handleUnexpectedError :: (MonadCompile m) => CompileError -> m CompileError
    handleUnexpectedError err =
      return $ UnsupportedNonLinearConstraint queryFormat propertyProv (Left err)

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
    "ERROR: found property with alternating quantifiers. Switching to polarity type-checking mode for"
      <+> quotePretty propertyIdentifier
      <> line

  errorOrPolarityProg <- polarityTypeCheck prog
  case errorOrPolarityProg of
    Left err -> handleUnexpectedError err
    Right polarityProg -> do
      -- Extract and diagnose the type.
      propertyType <- findDeclType propertyIdentifier polarityProg
      case propertyType of
        Builtin _ (Polarity (MixedSequential q p pp2)) -> do
          throwError $ UnsupportedAlternatingQuantifiers queryFormat propertyProv (Right (q, p, pp2))
        _ -> compilerDeveloperError $ "Unexpected polarity type for property" <+> quotePretty propertyIdentifier <> ":" <+> prettyVerbose propertyType
  where
    handleUnexpectedError :: (MonadCompile m) => CompileError -> m CompileError
    handleUnexpectedError err =
      return $ UnsupportedAlternatingQuantifiers queryFormat propertyProv (Left err)

findDeclType :: (MonadCompile m) => Identifier -> Prog builtin -> m (Expr builtin)
findDeclType ident (Main decls) = do
  let candidates = filter (\decl -> identifierOf decl == ident) decls
  case candidates of
    [property] -> return $ typeOf property
    _ -> compilerDeveloperError $ "Could not find property" <+> quotePretty ident <+> "in program after subtyping."
