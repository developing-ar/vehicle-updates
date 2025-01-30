module Vehicle.Compile.Type.Subsystem
  ( typeCheckWithSubsystem,
    resolveInstanceArguments,
  )
where

import Control.Monad.Except (runExceptT)
import Data.List.NonEmpty qualified as NonEmpty
import Vehicle.Compile.Error
import Vehicle.Compile.Monomorphisation (monomorphise)
import Vehicle.Compile.Normalise.NBE (NormalisableBuiltin, findInstanceArg)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (PrintableBuiltin, prettyExternal)
import Vehicle.Compile.Type (typeCheckProg)
import Vehicle.Compile.Type.Core (InstanceDatabase)
import Vehicle.Compile.Type.Irrelevance (removeIrrelevantCodeFromProg)
import Vehicle.Compile.Type.System
import Vehicle.Data.Builtin.Interface.Normalise (NormalisableBuiltin (..))
import Vehicle.Data.Builtin.Standard
import Vehicle.Libraries.StandardLibrary.Definitions (StdLibFunction (..))

typeCheckWithSubsystem ::
  forall builtin m.
  (HasTypeSystem builtin, NormalisableBuiltin builtin, MonadCompile m) =>
  InstanceDatabase builtin ->
  (forall a. CompileError -> m a) ->
  Prog Builtin ->
  m (Prog builtin)
typeCheckWithSubsystem instanceCandidates errorHandler prog = do
  typeClassFreeProg <- resolveInstanceArguments prog
  irrelevantFreeProg <- removeIrrelevantCodeFromProg typeClassFreeProg
  monomorphisedProg <- monomorphise isPropertyDecl "-" irrelevantFreeProg
  implicitFreeProg <- removeImplicitAndInstanceArgs monomorphisedProg

  resultOrError <- runExceptT $ typeCheckProg instanceCandidates mempty implicitFreeProg
  case resultOrError of
    Right value -> return value
    Left err -> errorHandler err

resolveInstanceArguments ::
  forall m builtin.
  (MonadCompile m, NormalisableBuiltin builtin, Show builtin) =>
  Prog builtin ->
  m (Prog builtin)
resolveInstanceArguments prog =
  logCompilerPass MaxDetail "resolution of instance arguments" $ do
    flip traverseDecls prog $ \decl -> do
      decl2 <- traverse (traverseBuiltinsM builtinUpdateFunction) decl
      decl3 <- traverse (traverseFreeVarsM (const id) freeVarUpdateFunction) decl2
      return decl3
  where
    builtinUpdateFunction :: BuiltinUpdate m builtin builtin
    builtinUpdateFunction p b args
      | isTypeClassOp b = do
          (inst, remainingArgs) <- findInstanceArg b args
          return $ substArgs inst remainingArgs
      | otherwise = return $ normAppList (Builtin p b) args

    freeVarUpdateFunction :: FreeVarUpdate m builtin
    freeVarUpdateFunction recGo p ident args = do
      args' <- traverse (traverse recGo) args
      if ident == identifierOf StdVectorType
        then do
          (inst, remainingArgs) <- findInstanceArg ident args
          return $ substArgs inst remainingArgs
        else return $ normAppList (FreeVar p ident) args'

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
