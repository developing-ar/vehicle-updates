{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Vehicle.Compile.Monomorphisation
  ( monomorphise,
    hoistInferableParameters,
  )
where

import Control.Monad (forM_, void)
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks)
import Control.Monad.State
  ( MonadState (..),
    evalStateT,
    gets,
    modify,
  )
import Control.Monad.Writer (MonadWriter (..), runWriterT)
import Data.Bifunctor (Bifunctor (..))
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as Map
  ( delete,
    insertWith,
    lookup,
    member,
    singleton,
  )
import Data.Hashable (Hashable)
import Data.LinkedHashSet (LinkedHashSet)
import Data.LinkedHashSet qualified as HashSet (singleton, toList, union)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set qualified as Set (member, unions)
import Data.Text (Text)
import Data.Text qualified as Text
import Vehicle.Compile.Context.Free (MonadFreeContext)
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyExternal, prettyFriendly, prettyFriendlyEmptyCtx, prettyVerbose)
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Data.Hashing ()

--------------------------------------------------------------------------------
-- Public interface

-- | Tries to monomorphise any polymorphic functions by creating a copy per
-- concrete type each function is used with.
-- Not very sophisticated at the moment, if this needs to be improved perhaps
-- http://mrg.doc.ic.ac.uk/publications/featherweight-go/main.pdf
-- by Wen et al is a good starting point.
monomorphise ::
  forall m builtin.
  (MonadCompile m, Hashable builtin, PrintableBuiltin builtin) =>
  (Decl builtin -> Bool) ->
  (Binder builtin -> Bool) ->
  Text ->
  Prog builtin ->
  m (Prog builtin)
monomorphise isRootDecl isMonomorphisableBinder nameJoiner prog =
  logCompilerPass MinDetail "monomorphisation" $ do
    let readerState = (isRootDecl, isMonomorphisableBinder, nameJoiner)
    (prog2, substitutions) <- runReaderT (evalStateT (runWriterT (monomorphiseProg prog)) mempty) readerState
    result <- runReaderT (insert prog2) substitutions
    logCompilerPassOutput $ prettyFriendly result
    return result

--------------------------------------------------------------------------------
-- Utilities

obtainArgsToMonomorphise ::
  forall builtin.
  (Binder builtin -> Bool) ->
  Type builtin ->
  [Arg builtin] ->
  ([Arg builtin], [Arg builtin])
obtainArgsToMonomorphise shouldMonomorphiseBinder typ appArgs =
  fromMaybe ([], appArgs) (go typ appArgs)
  where
    go :: Type builtin -> [Arg builtin] -> Maybe ([Arg builtin], [Arg builtin])
    go t args = case (t, args) of
      (Pi _ binder result, a : as)
        | shouldMonomorphiseBinder binder || not (isExplicit binder) ->
            Just $ maybe ([a], as) (first (a :)) (go result as)
      _ -> Nothing

--------------------------------------------------------------------------------
-- Pass 2 - collects the sites for monomorphisation

-- | Applications of monomorphisable functions
type CandidateApplications builtin = HashMap Identifier (LinkedHashSet [Arg builtin])

-- | Solution identifier for a candidate monomorphisation application
type SubsitutionSolutions builtin = HashMap (Identifier, [Arg builtin]) Identifier

type MonadCollect builtin m =
  ( MonadCompile m,
    MonadState (CandidateApplications builtin) m,
    MonadWriter (SubsitutionSolutions builtin) m,
    MonadReader (Decl builtin -> Bool, Binder builtin -> Bool, Text) m,
    Hashable builtin,
    PrintableBuiltin builtin
  )

monomorphiseProg :: (MonadCollect builtin m) => Prog builtin -> m (Prog builtin)
monomorphiseProg (Main decls) =
  Main . reverse . concat <$> traverse (monomorphiseDecls True) (reverse decls)

monomorphiseDecls :: (MonadCollect builtin m) => Bool -> Decl builtin -> m [Decl builtin]
monomorphiseDecls top decl = do
  let ident = identifierOf decl
  logCompilerSection MaxDetail ("Checking" <+> quotePretty ident) $ do
    newDecls <- monomorphiseDecl top decl
    forM_ newDecls $ traverse collectReferences
    recursiveReferences <- gets (Map.member ident)
    resursiveDecls <-
      if recursiveReferences
        then monomorphiseDecls False decl
        else return []
    return (newDecls <> resursiveDecls)

monomorphiseDecl :: (MonadCollect builtin m) => Bool -> Decl builtin -> m [Decl builtin]
monomorphiseDecl top decl = do
  logDebug MaxDetail $ prettyExternal decl
  let ident = identifierOf decl
  freeVarApplications <- get
  modify (Map.delete ident)
  case decl of
    DefAbstract {} -> return [decl]
    DefFunction p _ anns t e -> do
      (isRootDecl, _, _) <- ask
      case Map.lookup ident freeVarApplications of
        Nothing -> do
          logDebug MaxDetail $ "No applications of" <+> quotePretty ident <+> "found."
          if isRootDecl decl
            then do
              logDebug MaxDetail "Keeping declaration"
              return [decl]
            else do
              logDebug MaxDetail "Discarding declaration"
              return []
        Just applications -> do
          let applicationList = HashSet.toList applications
          let numberOfApplications = length applicationList
          let allFreeVarsInArgs = Set.unions (freeVarsIn . argExpr <$> concat applicationList)
          let createNewName = numberOfApplications > 1 || not top || ident `Set.member` allFreeVarsInArgs
          logDebug MaxDetail $ "Found" <+> pretty numberOfApplications <+> "type-unique application(s):"
          logDebug MaxDetail $ indent 2 $ prettyVerbose applicationList <> line
          traverse (performMonomorphisation (p, ident, anns, t, e) createNewName) applicationList

performMonomorphisation ::
  (MonadCollect builtin m) =>
  (Provenance, Identifier, [Annotation], Type builtin, Expr builtin) ->
  Bool ->
  [Arg builtin] ->
  m (Decl builtin)
performMonomorphisation (p, ident, anns, typ, body) createNewName args = do
  newIdent <-
    if createNewName
      then changeName ident <$> getMonomorphisedName (nameOf ident) args
      else return ident
  (newType, newBody) <- substituteArgsThrough (typ, body, args)
  tell (Map.singleton (ident, args) newIdent)
  let newDecl = DefFunction p newIdent anns newType newBody
  logDebug MaxDetail $ prettyFriendly newDecl <> line
  return newDecl

substituteArgsThrough ::
  (MonadCollect builtin m) =>
  (Expr builtin, Expr builtin, [Arg builtin]) ->
  m (Expr builtin, Expr builtin)
substituteArgsThrough = \case
  (t, e, []) -> return (t, e)
  (Pi _ _ t, Lam _ _ e, arg : args) -> do
    let expr = argExpr arg
    let t' = expr `substDBInto` t
    let e' = expr `substDBInto` e
    substituteArgsThrough (t', e', args)
  (t, e, args) ->
    developerError $
      "Unexpected type/body of function undergoing monomorphisation"
        <+> line
        <> prettyVerbose t
        <> line
        <> prettyVerbose e
        <> line
        <> prettyVerbose args

collectReferences :: forall builtin m. (MonadCollect builtin m) => Expr builtin -> m ()
collectReferences expr = void $ traverseFreeVarsM (const id) collectReference expr
  where
    collectReference :: FreeVarUpdate m builtin
    collectReference recGo p ident args = do
      logDebug MaxDetail $ "Found application:" <+> quotePretty ident <+> prettyVerbose args
      args' <- traverse (traverse recGo) args
      modify (Map.insertWith HashSet.union ident (HashSet.singleton args'))
      return $ normAppList (FreeVar p ident) args

--------------------------------------------------------------------------------
-- Pass 3 - insert the monorphised identifiers

type MonadInsert builtin m =
  ( MonadCompile m,
    MonadReader (SubsitutionSolutions builtin) m,
    MonadFreeContext builtin m,
    Hashable builtin,
    PrintableBuiltin builtin
  )

insert :: (MonadInsert builtin m) => Prog builtin -> m (Prog builtin)
insert = traverse (traverseCandidateApplications _ (const id) replaceCandidateApplication)
  where
    traverseCandidateApplications ::
      forall m builtin.
      (MonadCompile m, MonadFreeContext builtin m) =>
      (Binder builtin -> Bool) ->
      (Binder builtin -> m (Expr builtin) -> m (Expr builtin)) ->
      (Provenance -> Identifier -> [Arg builtin] -> [Arg builtin] -> m (Expr builtin)) ->
      Expr builtin ->
      m (Expr builtin)
    traverseCandidateApplications shouldMonomorphiseBinder underBinder processApp = do
      traverseFreeVarsM underBinder processApp2
      where
        processApp2 recGo p ident args = do
          let result = splitArgs _ args
          let (argsToMono, remainingArgs) = fromMaybe ([], args) result
          remainingArgs' <- traverse (traverse recGo) (reverse remainingArgs)
          processApp p ident (reverse argsToMono) remainingArgs'

    replaceCandidateApplication ::
      (MonadInsert builtin m) =>
      Provenance ->
      Identifier ->
      [Arg builtin] ->
      [Arg builtin] ->
      m (Expr builtin)
    replaceCandidateApplication p ident monoArgs remainingArgs = do
      solution <- asks (Map.lookup (ident, monoArgs))
      case solution of
        Nothing -> return $ normAppList (FreeVar p ident) (monoArgs <> remainingArgs)
        Just replacementIdent -> return $ normAppList (FreeVar p replacementIdent) remainingArgs

getMonomorphisedName ::
  (MonadCollect builtin m) =>
  Text ->
  [Arg builtin] ->
  m Text
getMonomorphisedName name args = do
  (_, _, nameJoiner) <- ask
  let typeJoiner = getTypeJoiner nameJoiner
  let implicits = mapMaybe getImplicitArg args
  let parts = name : fmap getImplicitName implicits
  return $
    Text.replace "\\" "lam" $
      Text.replace " " nameJoiner $
        Text.replace "->" "" $
          Text.intercalate typeJoiner parts

getImplicitName :: (PrintableBuiltin builtin) => Type builtin -> Text
getImplicitName t = layoutAsText $ prettyFriendlyEmptyCtx t

getTypeJoiner :: Text -> Text
getTypeJoiner nameJoiner = nameJoiner <> nameJoiner

--------------------------------------------------------------------------------
-- Step 5. Hoisting.

hoistInferableParameters :: (MonadCompile m) => Prog builtin -> m (Prog builtin)
hoistInferableParameters (Main ds) = do
  (otherDecls, inferableParameters) <- runWriterT (goDecls ds)
  return $ Main (inferableParameters <> otherDecls)
  where
    goDecls :: (MonadWriter [Decl builtin] m) => [Decl builtin] -> m [Decl builtin]
    goDecls [] = return []
    goDecls (decl : decls) = do
      decls' <- goDecls decls
      case decl of
        DefAbstract _ _ (ParameterDef Inferable) _ -> do
          tell [decl]
          return decls'
        _ -> return $ decl : decls'
