module Vehicle.Compile.Type.Subsystem
  ( typeCheckWithSubsystem,
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
import Vehicle.Compile.Type.Core (InstanceDatabase)
import Vehicle.Compile.Type.Irrelevance (removeIrrelevantCodeFromProg)
import Vehicle.Compile.Type.System
import Vehicle.Data.Builtin.Interface.Normalise (NormalisableBuiltin (..))
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Data.Builtin.Standard
import Vehicle.Libraries.StandardLibrary.Definitions (StdLibFunction (..))

typeCheckWithSubsystem ::
  forall builtin m.
  (HasTypeSystem builtin, NormalisableBuiltin builtin, MonadCompile m) =>
  TypingSystem ->
  InstanceDatabase builtin ->
  Prog Builtin ->
  m (Either CompileError (Prog builtin))
typeCheckWithSubsystem typingSystem instanceCandidates prog = do
  logCompilerPass MinDetail ("typing using" <+> quotePretty typingSystem <+> "type subsystem") $ do
    typeClassFreeProg <- resolveInstanceArgumentsAndCasts prog
    irrelevantFreeProg <- removeIrrelevantCodeFromProg typeClassFreeProg
    monomorphisedProg <- monomorphise isPropertyDecl "-" irrelevantFreeProg
    implicitFreeProg <- removeImplicitAndInstanceArgs monomorphisedProg
    runExceptT $ typeCheckProg instanceCandidates mempty implicitFreeProg

resolveInstanceArgumentsAndCasts ::
  forall m builtin.
  (MonadCompile m, NormalisableBuiltin builtin, Show builtin) =>
  Prog builtin ->
  m (Prog builtin)
resolveInstanceArgumentsAndCasts prog =
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
      | otherwise = case isCast b of
          Just f -> f args
          Nothing -> return $ normAppList (Builtin p b) args

    freeVarUpdateFunction :: FreeVarUpdate m builtin
    freeVarUpdateFunction recGo p ident args = do
      args' <- traverse (traverse recGo) args
      if ident == identifierOf StdVectorType
        then do
          (inst, remainingArgs) <- findInstanceArg ident args
          return $ substArgs inst remainingArgs
        else return $ normAppList (FreeVar p ident) args'
