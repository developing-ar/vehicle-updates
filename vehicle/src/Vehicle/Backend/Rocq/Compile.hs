module Vehicle.Backend.Rocq.Compile
  ( RocqOptions (..),
    compileProgToRocq,
  )
where

import Data.Data (Proxy (..))
import Data.Foldable (fold)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (catMaybes)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Vector qualified as Vector
import GHC.Real (denominator, numerator)
import Prettyprinter hiding (hcat, hsep, vcat, vsep)
import System.FilePath (takeBaseName)
import Vehicle.Compile.Context.Bound (getNamedBoundCtx)
import Vehicle.Compile.Context.Name (MonadNameContext, addNameToContext, ixToProperName, runFreshNameContextT)
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude hiding (Module)
import Vehicle.Compile.Print
import Vehicle.Compile.Type.Subsystem (resolveInstanceArgumentsAndCasts)
import Vehicle.Data.Builtin.Decidability
import Vehicle.Data.Builtin.Standard hiding (TensorType)
import Vehicle.Data.Universe (UniverseLevel (..))
import Vehicle.Libraries.StandardLibrary.Definitions (StdLibFunction (..), findStdLibFunction)
import Vehicle.Syntax.Builtin
import Vehicle.Syntax.Sugar
  ( BinderType (..),
    LetBinder,
    foldBinders,
    foldDeclBinders,
  )
import Vehicle.Syntax.Tensor
  ( Tensor (..),
    TensorShape,
    TensorValue (..),
    foldMapTensor,
  )

--------------------------------------------------------------------------------
-- Rocq-specific options

data RocqOptions = RocqOptions
  { output :: Maybe FilePath,
    moduleName :: Maybe String
  }

currentPhase :: Doc ()
currentPhase = "compilation to Rocq"

compileProgToRocq :: (MonadCompile m) => Prog DecidabilityBuiltin -> RocqOptions -> m (Doc a)
compileProgToRocq prog options = logCompilerPass MinDetail currentPhase $ do
  monoProg <- resolveInstanceArgumentsAndCasts prog
  programDoc <- runFreshNameContextT $ compileProg options monoProg
  let programStream = layoutPretty defaultLayoutOptions programDoc

  let programDependencies = fold (reAnnotateS fst programStream)

  let _nameOfModule = Text.pack $ case moduleName options of
        Just name -> name
        _ -> maybe "Spec" takeBaseName (output options)

  let coqProgram =
        unAnnotate
          ( (vsep2 :: [Code] -> Code)
              [ -- optionStatements ["allow-exec"],
                preamble programDependencies,
                -- moduleHeader nameOfModule,
                programDoc
              ]
          )
  return coqProgram

--------------------------------------------------------------------------------
-- Debug functions

logEntry :: (MonadRocqCompile m) => Expr DecidabilityBuiltin -> m ()
logEntry e = do
  incrCallDepth
  ctx <- getNamedBoundCtx (Proxy @())
  logDebug MaxDetail $ "compile-entry" <+> prettyExternal (WithContext e ctx)

logExit :: (MonadRocqCompile m) => Code -> m ()
logExit e = do
  logDebug MaxDetail $ "compile-exit " <+> e
  decrCallDepth

--------------------------------------------------------------------------------
-- Modules

data Dependency
  = RequireImport Library
  | Import Module
  | Open Scope
  deriving (Eq, Ord)

instance Pretty Dependency where
  pretty = \case
    RequireImport l -> "Require Import" <+> pretty l <> "."
    Import m -> "Import" <+> pretty m <> "."
    Open s -> "Open Scope" <+> pretty s <> "."

data Library
  = MathcompSsreflectSsrbool
  | MathcompAlgebraSsralg
  | MathcompSsreflectOrder
  | MathcompSsreflectFintype
  | MathcompSsreflectSeq
  | MathcompSsreflectTuple
  | MathcompAlgebraZmodp
  | MathcompRealsReals
  | VehicleTensor
  | VehicleReal
  | VehicleOrderNotations
  | VehicleUtils
  deriving (Eq, Ord)

instance Pretty Library where
  pretty = \case
    VehicleTensor -> "Vehicle.Tensor"
    VehicleReal -> "Vehicle.Real"
    VehicleOrderNotations -> "Vehicle.OrderNotations"
    VehicleUtils -> "Vehicle.Utils"
    MathcompAlgebraSsralg -> "mathcomp.algebra.ssralg"
    MathcompSsreflectOrder -> "mathcomp.ssreflect.order"
    MathcompSsreflectFintype -> "mathcomp.ssreflect.fintype"
    MathcompSsreflectSsrbool -> "mathcomp.ssreflect.ssrbool"
    MathcompSsreflectSeq -> "mathcomp.ssreflect.seq"
    MathcompSsreflectTuple -> "mathcomp.ssreflect.tuple"
    MathcompAlgebraZmodp -> "mathcomp.algebra.zmodp"
    MathcompRealsReals -> "mathcomp.reals.reals"

data Module
  = DefaultTupleProdOrder
  deriving (Eq, Ord)

instance Pretty Module where
  pretty = \case
    DefaultTupleProdOrder -> "DefaultTupleProdOrder"

data Scope
  = RingScope
  | TensorScope
  | OrderScope
  deriving (Eq, Ord)

instance Pretty Scope where
  pretty = \case
    RingScope -> "ring_scope"
    TensorScope -> "tensor_scope"
    OrderScope -> "order_scope"

preamble :: Set Dependency -> Doc a
preamble deps = vsep $ map pretty (Set.toList deps)

--------------------------------------------------------------------------------
-- Intermediate results of compilation

type Precedence = Int

type Code = Doc (Set Dependency, Precedence)

minPrecedence :: Precedence
minPrecedence = -1000

maxPrecedence :: Precedence
maxPrecedence = 1000

getPrecedence :: Code -> Precedence
getPrecedence e = maybe maxPrecedence snd (docAnn e)

annotateConstant :: [Dependency] -> Code -> Code
annotateConstant dependencies = annotate (Set.fromList dependencies, maxPrecedence)

annotateApp :: (MonadRocqCompile m) => [Dependency] -> Code -> [Arg DecidabilityBuiltin] -> m Code
annotateApp dependencies fun args = do
  (precedence, annDoc) <-
    if null args
      then return (getPrecedence fun, fun)
      else do
        let precedence = 200
        bracketedArgs <- compileArgs precedence args
        return (precedence, hsep (fun : bracketedArgs))

  return $ annotate (Set.fromList dependencies, precedence) annDoc

annotateInfixApp ::
  (MonadRocqCompile m) =>
  [Dependency] ->
  Precedence ->
  Text ->
  Maybe Text ->
  [Arg DecidabilityBuiltin] ->
  m Code
annotateInfixApp dependencies precedence op fallbackOp args
  | not (all isExplicit args) = fallback
  | otherwise = do
      bracketedArgs <- compileArgs precedence args
      let doc = insertInfixArgs op bracketedArgs
      maybe fallback (return . annotate (Set.fromList dependencies, precedence)) doc
  where
    fallback = case fallbackOp of
      Just fOp -> annotateApp dependencies (pretty fOp) args
      Nothing ->
        developerError $
          "too many arguments"
            <+> pretty op
            <+> "with"
            <+> pretty (length args)
            <+> "arguments"

-- | Inserts infix args into the correct positions
-- e.g. insertInfixArgs Nothing "if_then_else_" [a, b, c] = Just "if a then b else c"
-- or. insertInfixArgs Nothing "if_then_else_" "[a, b] = Nothing
insertInfixArgs :: Text -> [Code] -> Maybe Code
insertInfixArgs rawOp as = concatWith (<>) <$> go rawOp as
  where
    go :: Text -> [Code] -> Maybe [Code]
    go opText = \case
      []
        | Text.null opText -> Just []
        | otherwise -> Just [pretty opText]
      arg : args -> do
        let (prefix, maybeSuffix) = Text.break (== '_') opText
        let front = pretty prefix
        back <- Text.uncons maybeSuffix >>= \(_underscore, suffix) -> go suffix args

        Just $
          if Text.null prefix
            then arg : back
            else front : arg : back

argBrackets :: Precedence -> Visibility -> Code -> Code
argBrackets parentPrecedence v e = case v of
  Explicit {}
    | getPrecedence e > parentPrecedence -> e
    | otherwise -> parens e
  Implicit {} -> braces e
  Instance {} -> braces (braces e)

binderBrackets :: Bool -> Visibility -> Code -> Code
binderBrackets True Explicit {} = id
binderBrackets False Explicit {} = parens
binderBrackets _topLevel Implicit {} = braces
binderBrackets _topLevel Instance {} = braces . braces

--------------------------------------------------------------------------------
-- Monad stack

type MonadRocqCompile m =
  ( MonadCompile m,
    MonadNameContext m
  )

--------------------------------------------------------------------------------
-- Program Compilation

compileProg :: (MonadRocqCompile m) => RocqOptions -> Prog DecidabilityBuiltin -> m Code
compileProg opts (Main ds) = vsep2 <$> traverse (compileDecl opts) ds

compileDecl :: (MonadRocqCompile m) => RocqOptions -> Decl DecidabilityBuiltin -> m Code
compileDecl _opts = \case
  DefAbstract _ n _ t ->
    compilePostulate (compileIdentifier n) <$> compileExpr t
  DefFunction _ n anns t e -> do
    let (binders, body) = foldDeclBinders e
    if isProperty anns
      then compileProperty (compileIdentifier n) <$> compileExpr e
      else do
        binders' <- catMaybes <$> mapM compileTopLevelBinder binders
        (_, cbody) <- compileBinders binders (compileExpr body)
        defType <- resolveReturnType binders' t
        return $ compileFunDef (compileIdentifier n) defType binders' cbody

-- | Compile a 'network' declaration
compilePostulate :: Code -> Code -> Code
compilePostulate name t = "Parameter" <+> name <+> ":" <+> align t <> "."

compileExpr :: (MonadRocqCompile m) => Expr DecidabilityBuiltin -> m Code
compileExpr expr = do
  logEntry expr
  result <- case expr of
    Hole {} -> resolutionError currentPhase "Hole"
    Meta {} -> resolutionError currentPhase "Meta"
    Universe _ l -> return $ compileType l
    FreeVar _ n -> return $ annotateConstant [] (pretty (nameOf n))
    BoundVar p ix -> do
      n <- ixToProperName p ix
      return $ annotateConstant [] (pretty n)
    Pi _ binder result -> case binderNamingForm binder of
      OnlyType -> do
        cInput <- compileBinder binder
        cOutput <- addNameToContext binder $ compileExpr result
        return $ annotate ([], 99) $ cInput <+> "->" <+> cOutput
      _ -> do
        let (binders, body) = foldBinders PiBinder binder result
        compileTypeLevelQuantifier Forall (binder :| binders) body
    Let _ bound binder body -> do
      cBoundExpr <- compileLetBinder (binder, bound)
      cBody <- addNameToContext binder $ compileExpr body
      return $ "let" <+> cBoundExpr <+> "in" <+> cBody
    Lam _ binder body -> compileLam binder body
    Builtin _p b -> compileBuiltin b []
    App fun args -> compileApp fun args
  logExit result
  return result

compileType :: UniverseLevel -> Code
compileType (UniverseLevel l)
  | l == 0 = "Prop"
  | otherwise = undefined -- annotateConstant [] ("Prop" <> pretty l)

compileLetBinder ::
  (MonadRocqCompile m) =>
  LetBinder (Expr DecidabilityBuiltin) ->
  m Code
compileLetBinder (binder, expr) = do
  let binderName = pretty (getBinderName binder)
  cExpr <- compileExpr expr
  return $ binderName <+> "=" <+> cExpr

compileIdentifier :: Identifier -> Code
compileIdentifier ident = pretty (nameOf ident :: Name)

compileProperty :: Code -> Code -> Code
compileProperty propertyName propertyBody =
  "Axiom" <+> propertyName <+> ":" <+> propertyBody <> "."

compileTopLevelBinder :: (MonadRocqCompile m) => Binder DecidabilityBuiltin -> m (Maybe Code)
compileTopLevelBinder binder
  | visibilityOf binder /= Explicit = pure Nothing
  | otherwise = do
      let binderName = pretty (getBinderName binder)
      binderType <- compileExpr (typeOf binder)
      pure . Just . parens $ binderName <+> ":" <+> binderType

compileBinders :: (MonadRocqCompile m) => [Binder DecidabilityBuiltin] -> m Code -> m ([Code], Code)
compileBinders [] c = ([],) <$> c
compileBinders (b : bs) c = do
  (cbs, cc) <- addNameToContext b $ compileBinders bs c
  cb <- compileBinder b
  return (cb : cbs, cc)

compileBinder :: (MonadRocqCompile m) => Binder DecidabilityBuiltin -> m Code
compileBinder binder = do
  binderType <- compileExpr (typeOf binder)
  (binderDoc, noExplicitBrackets) <- case binderNamingForm binder of
    OnlyName name -> return (pretty name, True)
    OnlyType -> return (binderType, True)
    NameAndType name -> do
      let annName = annotate (Set.empty, minPrecedence) (pretty name <+> ":" <+> binderType)
      return (annName, False)

  return $ binderBrackets noExplicitBrackets (visibilityOf binder) binderDoc

resolveReturnType :: (MonadRocqCompile m) => [Code] -> Expr DecidabilityBuiltin -> m Code
resolveReturnType (_ : bs) (Pi _ _ r) = resolveReturnType bs r
resolveReturnType _ e = compileExpr e

compileFunDef :: Code -> Code -> [Code] -> Code -> Code
compileFunDef name t bindings e =
  "Definition"
    <+> name
    <+> (if null bindings then mempty else hsep bindings <> " ")
    <> ":"
    <+> align t
    <+> ":="
    <+> e
    <> "."

compileBuiltin :: (MonadRocqCompile m) => DecidabilityBuiltin -> [Arg DecidabilityBuiltin] -> m Code
compileBuiltin b args = case b of
  StandardBuiltinType t -> case t of
    BoolType -> return $ compileType (UniverseLevel 0)
    -- For the Rocq backend, rationals are promoted to reals
    RatType -> return $ annotateConstant [RequireImport VehicleReal, RequireImport MathcompRealsReals] "R"
    UnitType -> return "unit"
    NatType -> return "nat"
    ListType -> annotateApp [] "list" args
    TensorType -> annotateApp [RequireImport VehicleTensor] "tensor" args
    IndexType -> annotateApp [RequireImport MathcompSsreflectFintype] "ordinal" args
  StandardBuiltinConstructor c -> case c of
    Nil -> return "nil"
    Cons -> annotateInfixApp [RequireImport MathcompSsreflectSeq] 60 "_ :: _" (Just "cons") args
    UnitLiteral -> return "tt"
    IndexLiteral n -> return $ compileIndexLiteral n
    NatLiteral n -> return $ compileNatLiteral n
    NatTensorLiteral t -> return $ compileTensorLiteral compileNatLiteral t
    BoolTensorLiteral t -> return $ compileTensorLiteral compileBoolLiteral t
    RatTensorLiteral t -> return $ compileTensorLiteral compileRatLiteral t
    IndexTensorLiteral t -> return $ compileTensorLiteral compileIndexLiteral t
  StandardBuiltinFunction f -> case f of
    And -> annotateInfixApp [] 40 "_ && _" (Just "andb") args -- https://coq.inria.fr/doc/V8.18.0/refman/language/coq-library.html#notations
    Or -> annotateInfixApp [] 50 "_ || _" (Just "orb") args
    Not -> annotateInfixApp [RequireImport MathcompSsreflectSsrbool] 35 "~~ _" (Just "negb") args
    Implies -> annotateInfixApp [RequireImport MathcompSsreflectSsrbool] 55 "_ ==> _" (Just "implb") args
    Add AddNat -> annotateInfixApp [RequireImport MathcompAlgebraSsralg, Open RingScope] 50 "_ + _" (Just "GRing.add") args
    Mul MulNat -> annotateInfixApp [RequireImport MathcompAlgebraSsralg, Open RingScope] 40 "_ * _" (Just "GRing.mul") args
    Add AddRatTensor -> annotateInfixApp [] 50 "_ + _" (Just "addt") args
    Sub SubRatTensor -> annotateInfixApp [] 50 "_ - _" (Just "subt") args
    Mul MulRatTensor -> annotateInfixApp [] 40 "_ * _" (Just "mult") args
    Div DivRatTensor -> annotateInfixApp [] 40 "_ / _" (Just "divt") args
    Neg NegRatTensor -> annotateApp [] "negt" args
    Min MinRatTensor -> annotateApp [] "mint" args
    Max MaxRatTensor -> annotateApp [] "maxt" args
    Compare CompareIndex op -> compileComparison True op args
    Compare CompareNat op -> compileComparison True op args
    Compare CompareRatTensor op -> compileComparison True op args
    FoldList -> annotateApp [RequireImport MathcompSsreflectSeq] "foldr" args
    MapList -> annotateApp [RequireImport MathcompSsreflectSeq] "map" args
    ReduceAndTensor -> annotateApp [RequireImport VehicleTensor] "reduceAnd" args
    ReduceOrTensor -> annotateApp [RequireImport VehicleTensor] "reduceOr" args
    ReduceAddRatTensor -> annotateApp [] "reduceAdd" args
    ReduceMinRatTensor -> annotateApp [] "reduceMin" args
    ReduceMaxRatTensor -> annotateApp [] "reduceMax" args
    ReduceMulRatTensor -> annotateApp [] "reduceMul" args
    ConstTensor -> annotateApp [] "constTensor" args
    QuantifyRatTensor q -> case reverse args of
      (ExplicitArg _ _ (Lam _ binder body)) : _ -> compileTypeLevelQuantifier q [binder] body
      _ -> unsupportedArgsError
    At -> annotateApp [RequireImport MathcompSsreflectTuple] "tnth" args
    If -> annotateInfixApp [RequireImport MathcompSsreflectSsrbool] 200 "if _ then _ else _" (Just "if_expr") args -- TODO : Check precedence
    Foreach -> annotateApp [RequireImport VehicleTensor] "foreach" args
    StackTensor -> compileStack args
    -- let as = compileArgs maxPrecedence args
    -- annotateApp [Import VehicleTensor] "stack" (compileTensorLiteral id as)
    Iterate -> unsupportedError
    PowRat -> unsupportedError
  DecidabilityBuiltinFunction f -> case f of
    TypeTrue -> return "True"
    TypeFalse -> return "False"
    TypeNot -> annotateInfixApp [] 75 "~ _" (Just "not") args
    TypeAnd -> annotateInfixApp [] 80 "_ /\\ _" (Just "and") args
    TypeOr -> annotateInfixApp [] 85 "_ \\/ _" (Just "or") args
    TypeImplies -> annotateInfixApp [RequireImport MathcompSsreflectSsrbool] minPrecedence "_ -> _" (Just "implies") args
    TypeCompare CompareIndex op -> compileComparison False op args
    TypeCompare CompareNat op -> compileComparison False op args
    TypeCompare CompareRatTensor op -> compileComparison False op args
    BoolTensorToType -> monoError
  DecidabilityBuiltinTypeClass {} -> monoError
  DecidabilityBuiltinTypeClassOp {} -> monoError
  where
    unsupportedError :: a
    unsupportedError =
      developerError $
        "compilation of builtin" <+> quotePretty b <+> "to Rocq unsupported"

    unsupportedArgsError :: (MonadRocqCompile m) => m a
    unsupportedArgsError = do
      compilerDeveloperError $
        "compilation of"
          <+> quotePretty b
          <+> "with args"
          <+> prettyVerbose args
          <+> "to Rocq unsupported"

    monoError :: a
    monoError =
      developerError $
        "Monomorphisation should have got rid of"
          <+> quotePretty (show b)

compileApp :: (MonadRocqCompile m) => Expr DecidabilityBuiltin -> NonEmpty (Arg DecidabilityBuiltin) -> m Code
compileApp fun args = do
  let userArgs = NonEmpty.filter (not . wasInsertedByCompiler) args
  case fun of
    Builtin _p b ->
      compileBuiltin b userArgs
    FreeVar _ (findStdLibFunction -> Just stdlibFn) ->
      compileStdLibFunction stdlibFn userArgs
    _ -> do
      cFun <- compileExpr fun
      annotateApp [] cFun userArgs

compileStdLibFunction :: (MonadRocqCompile m) => StdLibFunction -> [Arg DecidabilityBuiltin] -> m Code
compileStdLibFunction fn args = case fn of
  StdId -> annotateApp [] "id" args
  StdExistsIndex -> unsupported -- annotateApp [VehicleUtils] Nothing "existsIndex" args
  StdForallIndex -> unsupported -- annotateApp [VehicleUtils] Nothing "forallIndex" args
  StdVectorType -> unsupported
  StdAppendList -> annotateInfixApp [RequireImport MathcompSsreflectSeq] 5 "_++_" (Just "cat") args
  StdForallInList -> unsupported
  StdExistsInList -> unsupported
  StdTypeAnn -> annotateInfixApp [] 0 "(_:_)" Nothing args
  where
    unsupported = developerError $ "Compilation of stdlib function" <+> quotePretty fn <+> "not implemented"

compileTypeLevelQuantifier ::
  (MonadRocqCompile m) =>
  Quantifier ->
  NonEmpty (Binder DecidabilityBuiltin) ->
  Expr DecidabilityBuiltin ->
  m Code
compileTypeLevelQuantifier q binders body = do
  (cBinders, cBody) <- compileBinders (NonEmpty.toList binders) (compileExpr body)
  quant <- case q of
    Forall -> return "forall"
    Exists -> return "exists"
  return $ quant <+> hsep cBinders <> "," <+> cBody

compileArg :: (MonadRocqCompile m) => Precedence -> Arg DecidabilityBuiltin -> m Code
compileArg precedence arg = do
  body <- compileExpr (argExpr arg)
  return $ argBrackets precedence (visibilityOf arg) body

compileArgs :: (MonadRocqCompile m) => Precedence -> [Arg DecidabilityBuiltin] -> m [Code]
compileArgs precedence = traverse (compileArg precedence)

compileIndexLiteral :: Int -> Code
compileIndexLiteral i =
  annotateConstant
    [ RequireImport MathcompAlgebraSsralg,
      RequireImport MathcompSsreflectFintype,
      RequireImport MathcompAlgebraZmodp,
      Open RingScope
    ]
    (pretty i)

compileNatLiteral :: Int -> Code
compileNatLiteral = pretty

compileTensorLiteral :: (a -> Code) -> Tensor a -> Code
compileTensorLiteral compileElement =
  foldMapTensor compileElement compileTensorLayer
  where
    compileTensorLayer :: TensorShape -> [Code] -> Code
    compileTensorLayer _shape xs = annotate ([RequireImport MathcompSsreflectTuple], maxPrecedence) "[tuple" <+> concatWith (surround "; ") xs <> "]"

compileBoolLiteral :: Bool -> Code
compileBoolLiteral = \case
  True -> "true"
  False -> "false"

compileRatLiteral :: Rational -> Code
compileRatLiteral r = annotate ([RequireImport MathcompAlgebraSsralg, Open RingScope], minPrecedence) rat
  where
    num = pretty $ numerator r
    denom = compileNatLiteral (fromInteger $ denominator r)
    rat = (if denominator r == 1 then num else num <+> "/" <+> denom) <+> ":" <+> "R"

compileLam :: (MonadRocqCompile m) => Binder DecidabilityBuiltin -> Expr DecidabilityBuiltin -> m Code
compileLam binder expr = do
  let (binders, body) = foldBinders LamBinder binder expr
  (cBinders, cBody) <- compileBinders (binder : binders) (compileExpr body)
  return $ annotate (mempty, minPrecedence) ("fun" <+> hsep cBinders <+> "=>" <+> cBody)

compileComparison :: (MonadRocqCompile m) => Bool -> ComparisonOp -> [Arg DecidabilityBuiltin] -> m Code
compileComparison decidable op = do
  let (opP, opDec) = case op of
        Le -> ("<=", "<=")
        Lt -> ("<", "<")
        Ge -> (">=", ">=")
        Gt -> (">", ">")
        Eq -> ("=", "==")
        Ne -> ("<>", "!=")
  let opDoc = "_ " <> (if decidable then opDec else opP) <> " _"
  annotateInfixApp
    [ RequireImport MathcompSsreflectSsrbool,
      RequireImport MathcompSsreflectOrder,
      Import DefaultTupleProdOrder,
      Open OrderScope
    ] 70 opDoc Nothing

compileStack :: (MonadRocqCompile m) => [Arg DecidabilityBuiltin] -> m Code
compileStack args = do
  as <- compileArgs minPrecedence args
  let tensor = Tensor [length as] (Values $ Vector.fromList as)
  let argtuple = compileTensorLiteral id tensor
  return $ annotate ([RequireImport VehicleTensor], 200) $ "stack" <+> argtuple
