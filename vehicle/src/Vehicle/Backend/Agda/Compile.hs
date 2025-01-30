module Vehicle.Backend.Agda.Compile
  ( AgdaOptions (..),
    compileProgToAgda,
  )
where

import Control.Monad.Reader (runReaderT)
import Data.Foldable (fold)
import Data.List (sort)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (mapMaybe)
import Data.Proxy (Proxy (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Real (denominator, numerator)
import Prettyprinter hiding (hcat, hsep, vcat, vsep)
import System.FilePath (takeBaseName)
import Vehicle.Backend.Agda.CapitaliseTypeNames (capitaliseTypeNames)
import Vehicle.Compile.Context.Bound (getNamedBoundCtx)
import Vehicle.Compile.Context.Name (MonadNameContext, addNameToContext, ixToProperName, runFreshNameContextT)
import Vehicle.Compile.Error
import Vehicle.Compile.Monomorphisation
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Data.Builtin.Decidability
import Vehicle.Data.Builtin.Standard (BuiltinType (..))
import Vehicle.Data.Builtin.Standard hiding (TensorType)
import Vehicle.Data.Universe (UniverseLevel (..))
import Vehicle.Libraries.StandardLibrary.Definitions
import Vehicle.Syntax.Sugar
import Vehicle.Syntax.Tensor (Tensor, TensorShape, foldMapTensor)

--------------------------------------------------------------------------------
-- Agda-specific options

data AgdaOptions = AgdaOptions
  { verificationCache :: Maybe FilePath,
    output :: Maybe FilePath,
    moduleName :: Maybe String
  }

compileProgToAgda :: (MonadCompile m) => Prog DecidabilityBuiltin -> AgdaOptions -> m (Doc a)
compileProgToAgda prog options = logCompilerPass MinDetail currentPhase $
  flip runReaderT (options, BoolLevel) $ do
    monoProg <- monomorphise isPropertyDecl "-" prog
    prog2 <- capitaliseTypeNames monoProg
    programDoc <- runFreshNameContextT $ compileProg options prog2
    let programStream = layoutPretty defaultLayoutOptions programDoc
    -- Collects dependencies by first discarding precedence info and then
    -- folding using Set Monoid
    let progamDependencies = fold (reAnnotateS fst programStream)

    let nameOfModule = Text.pack $ case moduleName options of
          Just name -> name
          _ -> maybe "Spec" takeBaseName (output options)

    let agdaProgram =
          unAnnotate
            ( (vsep2 :: [Code] -> Code)
                [ optionStatements ["allow-exec"],
                  importStatements progamDependencies,
                  moduleHeader nameOfModule,
                  programDoc
                ]
            )

    return agdaProgram

--------------------------------------------------------------------------------
-- Debug functions

type MonadAgdaCompile m =
  ( MonadCompile m,
    MonadNameContext m
  )

logEntry :: (MonadAgdaCompile m) => Expr DecidabilityBuiltin -> m ()
logEntry e = do
  incrCallDepth
  ctx <- getNamedBoundCtx (Proxy @())
  logDebug MaxDetail $ "compile-entry" <+> prettyExternal (WithContext e ctx)

logExit :: (MonadAgdaCompile m) => Code -> m ()
logExit e = do
  logDebug MaxDetail $ "compile-exit " <+> e
  decrCallDepth

--------------------------------------------------------------------------------
-- Modules

-- | All possible Agda modules the program may depend on.
data Dependency
  = -- Vehicle Agda library (hopefully will migrate these with time)
    VehicleCore
  | VehicleUtils
  | DataTensor
  | DataTensorInstances
  | DataTensorAll
  | DataTensorAny
  | -- Standard library
    DataUnit
  | DataEmpty
  | DataProduct
  | DataSum
  | DataNat
  | DataNatInstances
  | DataNatDivMod
  | DataInteger
  | DataIntegerInstances
  | DataIntegerDivMod
  | DataRat
  | DataRatInstances
  | DataBool
  | DataBoolInstances
  | DataFin
  | DataList
  | DataListInstances
  | DataListAll
  | DataListAny
  | DataVector
  | DataVectorInstances
  | DataVectorAll
  | DataVectorAny
  | FunctionBase
  | PropEquality
  | RelNullary
  | RelNullaryDecidable
  deriving (Eq, Ord)

instance Pretty Dependency where
  pretty = \case
    VehicleCore -> "Vehicle"
    VehicleUtils -> "Vehicle.Utils"
    DataTensor -> "Vehicle.Data.Tensor"
    DataTensorInstances -> "Vehicle.Data.Tensor.Instances"
    DataTensorAll -> "Vehicle.Data.Tensor.Relation.Unary.All as" <+> tensorQualifier
    DataTensorAny -> "Vehicle.Data.Tensor.Relation.Unary.Any as" <+> tensorQualifier
    DataUnit -> "Data.Unit"
    DataEmpty -> "Data.Empty"
    DataProduct -> "Data.Product"
    DataSum -> "Data.Sum"
    DataNat -> "Data.Nat as" <+> natQualifier <+> "using" <+> parens "ℕ"
    DataNatInstances -> "Data.Nat.Instances"
    DataNatDivMod -> "Data.Nat.DivMod as" <+> natQualifier
    DataInteger -> "Data.Integer as" <+> intQualifier <+> "using" <+> parens "ℤ"
    DataIntegerInstances -> "Data.Integer.Instances"
    DataIntegerDivMod -> "Data.Int.DivMod as" <+> intQualifier
    DataRat -> "Data.Rational as" <+> ratQualifier <+> "using" <+> parens "ℚ"
    DataRatInstances -> "Data.Rational.Instances"
    DataBool -> "Data.Bool as" <+> boolQualifier <+> "using" <+> parens "Bool; true; false; if_then_else_"
    DataBoolInstances -> "Data.Bool.Instances"
    DataFin -> "Data.Fin as" <+> finQualifier <+> "using" <+> parens "Fin; #_"
    DataList -> "Data.List.Base"
    DataListInstances -> "Data.List.Instances"
    DataListAll -> "Data.List.Relation.Unary.All as" <+> listQualifier
    DataListAny -> "Data.List.Relation.Unary.Any as" <+> listQualifier
    DataVector -> "Data.Vec.Functional" <+> "renaming" <+> parens "[] to []ᵥ; _∷_ to _∷ᵥ_"
    DataVectorInstances -> "Data.Vec.Functional.Instances"
    DataVectorAll -> "Data.Vec.Functional.Relation.Unary.All as" <+> vectorQualifier
    DataVectorAny -> "Data.Vec.Functional.Relation.Unary.Any as" <+> vectorQualifier
    FunctionBase -> "Function.Base"
    PropEquality -> "Relation.Binary.PropositionalEquality"
    RelNullary -> "Relation.Nullary"
    RelNullaryDecidable -> "Relation.Nullary.Decidable"

optionStatement :: Text -> Doc a
optionStatement option = "{-# OPTIONS --" <> pretty option <+> "#-}"

optionStatements :: [Text] -> Doc a
optionStatements = vsep . map optionStatement

importStatement :: Dependency -> Doc a
importStatement dep = "open import" <+> pretty dep

importStatements :: Set Dependency -> Doc a
importStatements deps = vsep $ map importStatement dependencies
  where
    dependencies = sort (VehicleCore : Set.toList deps)

moduleHeader :: Text -> Doc a
moduleHeader moduleName = "module" <+> pretty moduleName <+> "where"

boolQualifier :: Doc a
boolQualifier = "𝔹"

finQualifier :: Doc a
finQualifier = "Fin"

natQualifier :: Doc a
natQualifier = "ℕ"

intQualifier :: Doc a
intQualifier = "ℤ"

ratQualifier :: Doc a
ratQualifier = "ℚ"

listQualifier :: Doc a
listQualifier = "List"

vectorQualifier :: Doc a
vectorQualifier = "Vector"

tensorQualifier :: Doc a
tensorQualifier = "Tensor"

indentCode :: Code -> Code
indentCode = indent 2

scopeCode :: Code -> Code -> Code
scopeCode keyword code = keyword <> line <> indentCode code

--------------------------------------------------------------------------------
-- Intermediate results of compilation

-- | Marks if the current boolean expression is compiled to `Set` or `Bool`
data BoolLevel = TypeLevel | BoolLevel
  deriving (Eq)

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

annotateApp :: (MonadAgdaCompile m) => [Dependency] -> Code -> [Arg DecidabilityBuiltin] -> m Code
annotateApp dependencies fun = \case
  [] -> return $ annotate (Set.fromList dependencies, getPrecedence fun) fun
  args -> do
    let precedence = 20
    bracketedArgs <- compileArgs precedence args
    return $ annotate (Set.fromList dependencies, precedence) (hsep (fun : bracketedArgs))

annotateInfixApp ::
  (MonadAgdaCompile m) =>
  [Dependency] ->
  Precedence ->
  Maybe Code ->
  Text ->
  [Arg DecidabilityBuiltin] ->
  m Code
annotateInfixApp dependencies precedence qualifier op args
  | not (all isExplicit args) =
      annotateApp dependencies _ args
  | otherwise = do
      bracketedArgs <- compileArgs precedence args
      let doc = insertInfixArgs True (Text.split "_" op) bracketedArgs
      return $ annotate (Set.fromList dependencies, precedence) doc

insertInfixArgs :: Bool -> [Text] -> [Code] -> Code
insertInfixArgs first fragments args = case (fragments, args) of
  ([], _ : _) ->
    developerError $
      "was expecting no more than 1 argument for"
        <+> op
        <+> "but found the following arguments:"
        <+> list args
  a : as -> do
    let qualifierDoc = maybe "" (<> ".") qualifier
    _

argBrackets :: Precedence -> Visibility -> Code -> Code
argBrackets parentPrecedence v e = case v of
  Explicit {}
    | getPrecedence e > parentPrecedence -> e
    | otherwise -> parens e
  Implicit {} -> braces e
  Instance {} -> braces (braces e)

binderBrackets :: Bool -> Visibility -> Code -> Code
binderBrackets topLevel = \case
  Explicit {} | topLevel -> id
  Explicit {} | otherwise -> parens
  Implicit {} -> braces
  Instance {} -> braces . braces

--------------------------------------------------------------------------------
-- Program Compilation

compileProg :: (MonadAgdaCompile m) => AgdaOptions -> Prog DecidabilityBuiltin -> m Code
compileProg opts (Main ds) = vsep2 <$> traverse (compileDecl opts) ds

compileDecl :: (MonadAgdaCompile m) => AgdaOptions -> Decl DecidabilityBuiltin -> m Code
compileDecl opts = \case
  DefAbstract _ n _ t ->
    compilePostulate (compileIdentifier n) <$> compileExpr t
  DefFunction _ n anns t e -> do
    let (binders, body) = foldDeclBinders e
    if isProperty anns
      then compileProperty opts (compileIdentifier n) =<< compileExpr e
      else do
        let binders' = mapMaybe compileTopLevelBinder binders
        (_, cbody) <- compileBinders binders (compileExpr body)
        compileFunDef (compileIdentifier n) <$> compileExpr t <*> pure binders' <*> pure cbody

compileExpr :: (MonadAgdaCompile m) => Expr DecidabilityBuiltin -> m Code
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
        return $ cInput <+> "→" <+> cOutput
      _ -> do
        let (binders, body) = foldBinders PiBinder binder result
        compileTypeLevelQuantifier Forall (binder :| binders) body
    Let _ bound binder body -> do
      cBoundExpr <- compileLetBinder (binder, bound)
      cBody <- addNameToContext binder $ compileExpr body
      return $ "let" <+> cBoundExpr <+> "in" <+> cBody
    Lam _ binder body -> compileLam binder body
    Builtin _ b -> compileBuiltin b []
    App fun args -> compileApp fun args

  logExit result
  return result

compileArg :: (MonadAgdaCompile m) => Precedence -> Arg DecidabilityBuiltin -> m Code
compileArg precedence arg = do
  body <- compileExpr (argExpr arg)
  return $ argBrackets precedence (visibilityOf arg) body

compileArgs :: (MonadAgdaCompile m) => Precedence -> [Arg DecidabilityBuiltin] -> m [Code]
compileArgs precedence = traverse (compileArg precedence)

compileLetBinder ::
  (MonadAgdaCompile m) =>
  LetBinder (Expr DecidabilityBuiltin) ->
  m Code
compileLetBinder (binder, expr) = do
  let binderName = pretty (getBinderName binder)
  cExpr <- compileExpr expr
  return $ binderName <+> "=" <+> cExpr

compileLam :: (MonadAgdaCompile m) => Binder DecidabilityBuiltin -> Expr DecidabilityBuiltin -> m Code
compileLam binder expr = do
  let (binders, body) = foldBinders LamBinder binder expr
  (cBinders, cBody) <- compileBinders (binder : binders) (compileExpr body)
  return $ annotate (mempty, minPrecedence) ("λ" <+> hsep cBinders <+> "→" <+> cBody)

compileIdentifier :: Identifier -> Code
compileIdentifier ident = pretty (nameOf ident :: Name)

compileType :: UniverseLevel -> Code
compileType (UniverseLevel l)
  | l == 0 = "Set"
  | otherwise = annotateConstant [] ("Set" <> pretty l)

compileTopLevelBinder :: Binder DecidabilityBuiltin -> Maybe Code
compileTopLevelBinder binder
  | visibilityOf binder /= Explicit = Nothing
  | otherwise = do
      let binderName = pretty (getBinderName binder)
      let addBrackets = binderBrackets True (visibilityOf binder)
      Just $ addBrackets binderName

compileBinders :: (MonadAgdaCompile m) => [Binder DecidabilityBuiltin] -> m Code -> m ([Code], Code)
compileBinders [] c = ([],) <$> c
compileBinders (b : bs) c = do
  (cbs, cc) <- addNameToContext b $ compileBinders bs c
  cb <- compileBinder b
  return (cb : cbs, cc)

compileBinder :: (MonadAgdaCompile m) => Binder DecidabilityBuiltin -> m Code
compileBinder binder = do
  binderType <- compileExpr (typeOf binder)
  (binderDoc, noExplicitBrackets) <- case binderNamingForm binder of
    OnlyName name -> return (pretty name, True)
    OnlyType -> return (binderType, True)
    NameAndType name -> do
      let annName = "(" <> pretty name <+> ":" <+> binderType <> ")"
      return (annName, False)

  return $ binderBrackets noExplicitBrackets (visibilityOf binder) binderDoc

compileApp :: (MonadAgdaCompile m) => Expr DecidabilityBuiltin -> NonEmpty (Arg DecidabilityBuiltin) -> m Code
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

compileStdLibFunction :: (MonadAgdaCompile m) => StdLibFunction -> [Arg DecidabilityBuiltin] -> m Code
compileStdLibFunction fn args = case fn of
  StdId -> annotateApp [FunctionBase] "id" args
  StdBigAnd -> _
  StdBigOr -> _
  StdExistsIndex -> _
  StdForallIndex -> _
  StdEqualsBool -> _
  StdNotEqualsBool -> _
  StdAppendList -> _
  StdVectorType -> _
  StdForallIn -> case args of
    [_, RelevantImplicitArg _ tCont, _, _, RelevantExplicitArg _ lam, RelevantExplicitArg _ cont] ->
      compileQuantIn Forall tCont lam cont
    _ -> developerError ""
  StdExistsIn -> case args of
    [RelevantImplicitArg _ tCont, _, _, RelevantExplicitArg _ lam, RelevantExplicitArg _ cont] ->
      Just <$> compileQuantIn Exists tCont lam cont
    _ -> return Nothing
  StdTypeAnn -> annotateInfixApp [FunctionBase] 0 Nothing "_∋_" args

compileBuiltin :: (MonadAgdaCompile m) => DecidabilityBuiltin -> [Arg DecidabilityBuiltin] -> m Code
compileBuiltin b args = case b of
  StandardBuiltinType t -> case t of
    BoolType -> compileType (UniverseLevel 0)
    RatType -> annotateConstant [DataRat] ratQualifier
    UnitType -> annotateConstant [DataUnit] "⊤"
    NatType -> annotateConstant [DataNat] natQualifier
    ListType -> annotateApp [DataList] "List" args
    TensorType -> annotateApp [DataTensor] "Tensor" args
    IndexType -> annotateApp [DataFin] "Fin" args
  DecidabilityBuiltinType t -> case t of
    DecBoolType -> annotateConstant [DataBool] "Bool"
  StandardBuiltinConstructor c -> case c of
    Nil -> annotateConstant [DataList] "[]"
    Cons -> annotateInfixApp [DataList] 5 Nothing "_∷_" args
    UnitLiteral -> annotateConstant [DataUnit] "tt"
    IndexLiteral n -> compileIndexLiteral (toInteger n)
    NatLiteral n -> compileNatLiteral (toInteger n)
    NatTensorLiteral t -> compileTensorLiteral compileIntLiteral t
    BoolTensorLiteral t -> compileTensorLiteral compileBoolLiteral t
    RatTensorLiteral t -> compileTensorLiteral compileRatLiteral t
    IndexTensorLiteral t -> compileTensorLiteral compileIndexLiteral t
  DecidabilityBuiltinConstructor c -> case c of
    DecBoolTensor t -> compileTensorLiteral compileDecBoolLiteral t
  StandardBuiltinFunction f -> case f of
    And -> annotateInfixApp [DataProduct] 2 Nothing "_×_" args
    Or -> annotateInfixApp [DataSum] 1 Nothing "_⊎_" args
    Not -> annotateInfixApp [RelNullary] 3 Nothing "¬_" args
    Implies -> annotateInfixOp2 [] minPrecedence Nothing arrow args "→"
    Add dom -> compileAdd dom args
    Sub SubRatTensor -> annotateInfixApp [DataTensor] 6 (Just tensorQualifier) "_-_" args
    Mul MulNat -> annotateInfixApp [DataNat] 7 (Just natQualifier) "_*_" args
    Mul MulRatTensor -> annotateInfixApp [DataRat] 7 (Just tensorQualifier) "_*_" args
    Div DivRatTensor -> annotateInfixApp [DataTensor] 7 (Just tensorQualifier) "_÷_" args
    Neg NegRatTensor -> annotateInfixApp [DataTensor] 8 (Just tensorQualifier) "-_" args
    Min MinRatTensor -> annotateInfixApp [DataTensor] 6 (Just tensorQualifier) "_⊓_" args
    Max MaxRatTensor -> annotateInfixApp [DataTensor] 7 (Just tensorQualifier) "_⊔_" args
    Compare dom ord -> compileComparison False ord dom args
    FoldList -> annotateApp [DataList] (listQualifier <> ".foldr") args
    MapList -> annotateApp [DataList] (listQualifier <> ".map") args
    ReduceAndTensor -> annotateApp [DataTensor] "reduceAnd" args
    ReduceOrTensor -> annotateApp [DataTensor] "reduceOr" args
    ReduceAddRatTensor -> annotateApp [DataTensor] "reduceAdd" args
    ReduceMinRatTensor -> annotateApp [DataTensor] "reduceMin" args
    ReduceMaxRatTensor -> annotateApp [DataTensor] "reduceMax" args
    ReduceMulRatTensor -> annotateApp [DataTensor] "reduceMul" args
    ConstTensor -> annotateApp [DataTensor] "constTensor" args
    QuantifyRatTensor q -> case reverse args of
      (ExplicitArg _ _ (Lam _ binder body)) : _ -> compileTypeLevelQuantifier q [binder] body
      _ -> unsupportedArgsError
    -- Needs to be special cased as `At` in Agda is simply function application.
    At -> annotateInfixApp [FunctionBase] (-1) Nothing "_$_" args
    If -> annotateInfixApp [DataBool] 0 Nothing "if_then_else_" args
    Foreach -> unsupportedError
    Iterate -> unsupportedError
    StackTensor {} -> unsupportedError
    PowRat -> unsupportedError
  DecidabilityBuiltinFunction f -> case f of
    DecNot -> annotateApp [DataBool] "not" args
    DecAnd -> annotateInfixApp [DataBool] 6 Nothing "_∧_" args
    DecOr -> annotateInfixApp [DataBool] 5 Nothing "_∨_" args
    DecImplies -> annotateInfixApp [VehicleUtils] 4 Nothing "_⇒_" args
    DecCompare dom ord -> compileComparison True ord dom args
    DecReduceAndTensor -> _
    DecReduceOrTensor -> _
  DecidabilityBuiltinTypeClass {} -> monoError
  DecidabilityBuiltinTypeClassOp {} -> monoError
  where
    unsupportedError :: a
    unsupportedError =
      developerError $
        "compilation of builtin" <+> quotePretty b <+> "to Agda unsupported"

    unsupportedArgsError :: a
    unsupportedArgsError = do
      developerError $
        "compilation of"
          <+> quotePretty b
          <+> "with args"
          <+> prettyVerbose args
          <+> "to Agda unsupported"

    monoError :: a
    monoError =
      developerError $
        "Monomorphisation should have got rid of"
          <+> quotePretty (show b)

compileTypeLevelQuantifier ::
  (MonadAgdaCompile m) =>
  Quantifier ->
  NonEmpty (Binder DecidabilityBuiltin) ->
  Expr DecidabilityBuiltin ->
  m Code
compileTypeLevelQuantifier q binders body = do
  (cBinders, cBody) <- compileBinders (NonEmpty.toList binders) (compileExpr body)
  quant <- case q of
    Forall -> return "∀"
    Exists -> return $ annotateConstant [DataProduct] "∃ λ"
  return $ quant <+> hsep cBinders <+> "→" <+> cBody

compileQuantIn :: Bool -> Quantifier -> Expr DecidabilityBuiltin -> Expr DecidabilityBuiltin -> Expr DecidabilityBuiltin -> Code
compileQuantIn bool q tCont fn cont = do
  (quant, qualifier, dep) <- case tCont of
    (Builtin _ (BuiltinType ListType)) -> case (boolLevel, q) of
      (TypeLevel, Forall) -> return ("All", listQualifier, DataListAll)
      (TypeLevel, Exists) -> return ("Any", listQualifier, DataListAny)
      (BoolLevel, Forall) -> return ("all", listQualifier, DataList)
      (BoolLevel, Exists) -> return ("any", listQualifier, DataList)
    _ -> case (boolLevel, q) of
      (TypeLevel, Forall) -> return ("All", tensorQualifier, DataTensorAll)
      (TypeLevel, Exists) -> return ("Any", tensorQualifier, DataTensorAny)
      (BoolLevel, Forall) -> return ("all", tensorQualifier, DataTensor)
      (BoolLevel, Exists) -> return ("any", tensorQualifier, DataTensor)

  annotateApp [dep] (qualifier <> "." <> quant) <$> traverse compileExpr [fn, cont]

compileIndexLiteral :: Integer -> Code
compileIndexLiteral i = annotateInfixApp [DataFin] 10 Nothing "#_" [pretty i]

compileNatLiteral :: Integer -> Code
compileNatLiteral = pretty

compileIntLiteral :: Integer -> Code
compileIntLiteral i
  | i >= 0 = annotateInfixApp [DataInteger] 8 (Just intQualifier) "+_" [pretty i]
  | otherwise = annotateInfixApp [DataInteger] 6 (Just intQualifier) "-_" [compileIntLiteral (-i)]

compileRatLiteral :: Rational -> Code
compileRatLiteral r = annotateInfixApp [DataRat] 7 (Just ratQualifier) "_/_" [num, denom]
  where
    num = compileIntLiteral (numerator r)
    denom = compileNatLiteral (denominator r)

compileTensorLiteral :: (a -> Code) -> Tensor a -> Code
compileTensorLiteral compileElement =
  foldMapTensor compileElement compileTensorLayer
  where
    -- \| Compiling vector literals. No literals in Agda so have to go via cons.
    compileTensorLayer :: TensorShape -> [Code] -> Code
    compileTensorLayer _shape = _ -- foldr (\x xs -> annotateInfixApp [] 5 Nothing "_∷ᵥ_" [x, xs]) "[]ᵥ"

compileBoolLiteral :: Bool -> Code
compileBoolLiteral = \case
  True -> annotateConstant [DataUnit] "⊤"
  False -> annotateConstant [DataEmpty] "⊥"

compileDecBoolLiteral :: Bool -> Code
compileDecBoolLiteral = \case
  True -> annotateConstant [DataBool] "true"
  False -> annotateConstant [DataBool] "false"

compileAdd :: AddDomain -> [Arg DecidabilityBuiltin] -> Code
compileAdd dom args = do
  let (qualifier, dependency) = case dom of
        AddNat -> (natQualifier, DataNat)
        -- AddRat -> (ratQualifier, DataRat)
        AddRatTensor -> (tensorQualifier, DataTensor)

  annotateInfixApp [dependency] 6 (Just qualifier) "_+_" args

compileComparison :: Bool -> ComparisonOp -> ComparisonDomain -> [Arg DecidabilityBuiltin] -> Code
compileComparison decidable order dom args = do
  (qualifier, elemDep) <- return $ case dom of
    CompareIndex -> (finQualifier, DataFin)
    CompareNat -> (natQualifier, DataNat)
    CompareRatTensor -> (tensorQualifier, DataTensor)

  let orderDoc = case order of
        Le -> "≤"
        Lt -> "<"
        Ge -> "≥"
        Gt -> ">"
        Eq -> "≡"
        Ne -> "≢"
  let opDoc = "_" <> orderDoc <> (if decidable then "ᵇ" else "") <> "_"

  annotateInfixApp [elemDep] 4 (Just qualifier) opDoc args

compileFunDef :: Code -> Code -> [Code] -> Code -> Code
compileFunDef n t ns e =
  n
    <+> ":"
    <+> align t
    <> line
    <> n
    <+> (if null ns then mempty else hsep ns <> " ")
    <> "="
    <+> e

-- | Compile a `network` declaration
compilePostulate :: Code -> Code -> Code
compilePostulate name t = "postulate" <+> name <+> ":" <+> align t

compileProperty :: (MonadAgdaCompile m) => AgdaOptions -> Code -> Code -> m Code
compileProperty options propertyName propertyBody = do
  let maybeVerificationCache = verificationCache options
  return $
    case maybeVerificationCache of
      Nothing ->
        "postulate" <+> propertyName <+> ":" <+> align propertyBody
      Just verificationCache ->
        scopeCode "abstract" $
          propertyName
            <+> ":"
            <+> align propertyBody
            <> line
            <> propertyName
            <+> "= checkSpecification record"
            <> line
            <> indentCode
              ( "{ cache ="
                  <+> dquotes (pretty verificationCache)
                  <> line
                  <> "}"
              )

currentPhase :: Doc ()
currentPhase = "compilation to Agda"
