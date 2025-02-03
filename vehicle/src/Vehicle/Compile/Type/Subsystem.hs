module Vehicle.Compile.Type.Subsystem
  ( polarityTypeCheck,
    linearityTypeCheck,
    decidabilityTypeCheck,
    resolveInstanceArgumentsAndCasts,
  )
where

import Control.Monad.Except (runExceptT)
import Data.List.NonEmpty qualified as NonEmpty
import Vehicle.Backend.Prelude
import Vehicle.Compile.Error
import Vehicle.Compile.Monomorphisation (monomorphise)
import Vehicle.Compile.Normalise.NBE (NormalisableBuiltin, findInstanceArg)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyExternal)
import Vehicle.Compile.Type (typeCheckProg)
import Vehicle.Compile.Type.Core (InstanceDatabase, emptyInstanceDatabase)
import Vehicle.Compile.Type.Irrelevance (removeIrrelevantCodeFromProg)
import Vehicle.Compile.Type.System
import Vehicle.Data.Builtin.Decidability (DecidabilityBuiltin)
import Vehicle.Data.Builtin.Decidability.Instances (decidabilityBuiltinInstances)
import Vehicle.Data.Builtin.Decidability.Type ()
import Vehicle.Data.Builtin.Interface.Normalise (NormalisableBuiltin (..))
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Data.Builtin.Linearity (LinearityBuiltin)
import Vehicle.Data.Builtin.Linearity.Type ()
import Vehicle.Data.Builtin.Polarity (PolarityBuiltin)
import Vehicle.Data.Builtin.Polarity.Type ()
import Vehicle.Data.Builtin.Standard
import Vehicle.Libraries.StandardLibrary.Definitions (StdLibFunction (..))

polarityTypeCheck :: (MonadCompile m) => Prog Builtin -> m (Either CompileError (Prog PolarityBuiltin))
polarityTypeCheck = typeCheckWithSubsystem PolarityTypes emptyInstanceDatabase simplifyTypes

linearityTypeCheck :: (MonadCompile m) => Prog Builtin -> m (Either CompileError (Prog LinearityBuiltin))
linearityTypeCheck = typeCheckWithSubsystem LinearityTypes emptyInstanceDatabase simplifyTypes

decidabilityTypeCheck :: (MonadCompile m) => Prog Builtin -> m (Either CompileError (Prog DecidabilityBuiltin))
decidabilityTypeCheck = typeCheckWithSubsystem DecidabilityTypes decidabilityBuiltinInstances return

typeCheckWithSubsystem ::
  forall builtin m.
  (HasTypeSystem builtin, NormalisableBuiltin builtin, MonadCompile m) =>
  SecondaryTypeSystem ->
  InstanceDatabase builtin ->
  (Prog Builtin -> m (Prog Builtin)) ->
  Prog Builtin ->
  m (Either CompileError (Prog builtin))
typeCheckWithSubsystem typingSystem instanceCandidates preprocess prog = do
  logCompilerPass MinDetail ("typing using" <+> quotePretty typingSystem <+> "type subsystem") $ do
    typeClassFreeProg <- resolveInstanceArgumentsAndCasts prog
    preprocessedProg <- preprocess typeClassFreeProg
    runExceptT $ typeCheckProg instanceCandidates mempty preprocessedProg

simplifyTypes ::
  (MonadCompile m) =>
  Prog Builtin ->
  m (Prog Builtin)
simplifyTypes prog = do
  irrelevantFreeProg <- removeIrrelevantCodeFromProg prog
  monomorphsiedProg <- monomorphise isPropertyDecl "-" irrelevantFreeProg
  implicitFreeProg <- removeImplicitArgs monomorphsiedProg
  return implicitFreeProg

resolveInstanceArgumentsAndCasts ::
  forall m builtin.
  (MonadCompile m, NormalisableBuiltin builtin, Show builtin) =>
  Prog builtin ->
  m (Prog builtin)
resolveInstanceArgumentsAndCasts prog =
  logCompilerPass MaxDetail "resolution of instance arguments and casts" $ do
    flip traverseDecls prog $ \decl -> do
      decl1 <- traverse (traverseBuiltinsM removeBuiltinInstances) decl
      decl2 <- traverse (traverseFreeVarsM (const id) removeFreeInstances) decl1
      decl3 <- traverse (traverseBuiltinsM removeCasts) decl2
      return decl3
  where
    removeBuiltinInstances :: BuiltinUpdate m builtin builtin
    removeBuiltinInstances p b args
      | isTypeClassOp b = do
          (inst, remainingArgs) <- findInstanceArg b args
          return $ substArgs inst remainingArgs
      | otherwise = return $ normAppList (Builtin p b) args

    removeFreeInstances :: FreeVarUpdate m builtin
    removeFreeInstances recGo p ident args = do
      args' <- traverse (traverse recGo) args
      if ident == identifierOf StdVectorType
        then do
          (inst, remainingArgs) <- findInstanceArg ident args
          return $ substArgs inst remainingArgs
        else return $ normAppList (FreeVar p ident) args'

    removeCasts :: BuiltinUpdate m builtin builtin
    removeCasts p b args = case isCast b of
      Just f -> f args
      Nothing -> return $ normAppList (Builtin p b) args

removeImplicitArgs ::
  forall m builtin.
  (MonadCompile m, PrintableBuiltin builtin) =>
  Prog builtin ->
  m (Prog builtin)
removeImplicitArgs prog =
  logCompilerPass MaxDetail "removal of implicit arguments" $ do
    result <- traverse go prog
    logCompilerPassOutput $ prettyExternal result
    return result
  where
    go :: Expr builtin -> m (Expr builtin)
    go expr = case expr of
      App fun args -> do
        fun' <- go fun
        let nonImplicitArgs = NonEmpty.filter (not . isImplicit) args
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
