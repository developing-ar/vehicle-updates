module Vehicle.Compile.Type.System where

import Data.Hashable (Hashable)
import Vehicle.Compile.Context.Free (MonadFreeContext, getFreeEnv)
import Vehicle.Compile.Error
import Vehicle.Compile.Normalise.Builtin (NormalisableBuiltin)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (PrintableBuiltin, prettyVerbose)
import Vehicle.Compile.Type.Builtin (TypableBuiltin)
import Vehicle.Compile.Type.Constraint.IndexSolver (solveDefaultIndexConstraints, solveIndexConstraint)
import Vehicle.Compile.Type.Constraint.InstanceDefaultSolver (getDefaultableConstraints)
import Vehicle.Compile.Type.Constraint.LinearitySolver
import Vehicle.Compile.Type.Constraint.PolaritySolver
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Monad (createFreshInstanceConstraint, createFreshUnificationConstraint, freshMetaExpr)
import Vehicle.Compile.Type.Monad.Class (MonadTypeChecker, getActiveAuxiliaryInstanceConstraints)
import Vehicle.Compile.Type.Subsystem.InputOutputInsertion (addFunctionAuxiliaryInputOutputConstraints)
import Vehicle.Data.Builtin.Linearity
import Vehicle.Data.Builtin.Polarity
import Vehicle.Data.Builtin.Standard (Builtin (..), BuiltinConstructor (..), BuiltinFunction (StackTensor), BuiltinType (..), TypeClass (..))
import Vehicle.Data.Code.Value

-- | The type-checking monad.
type TCM builtin m =
  ( MonadTypeChecker builtin m,
    HasTypeSystem builtin
  )

-- | A class that provides an abstract interface for a set of builtins.
class (Eq builtin, Hashable builtin, NormalisableBuiltin builtin, TypableBuiltin builtin) => HasTypeSystem builtin where
  convertFromStandardBuiltins ::
    (MonadTypeChecker builtin m) =>
    BuiltinUpdate m Builtin builtin

  restrictDeclType ::
    (MonadTypeChecker builtin m) =>
    RestrictedDecl ->
    DeclProvenance ->
    Type builtin ->
    m (Type builtin)

  addAuxiliaryInputOutputConstraints ::
    (MonadTypeChecker builtin m) => Decl builtin -> m (Decl builtin)

  generateDefaultAuxiliaryConstraint ::
    (MonadTypeChecker builtin m) =>
    Maybe (Decl builtin) ->
    m Bool

  isAuxiliaryConstraint ::
    Expr builtin -> Bool

  -- | Solves an auxiliary instance constraint (i.e. a constraint that is
  -- not solvable by the default instance mechanism)
  solveAuxiliaryInstanceConstraint ::
    (MonadTypeChecker builtin m, MonadFreeContext builtin m) =>
    WithContext (InstanceConstraint builtin) ->
    m ()

-----------------------------------------------------------------------------
-- Standard builtins
-----------------------------------------------------------------------------

instance HasTypeSystem Builtin where
  convertFromStandardBuiltins = convertToTypingBuiltins
  restrictDeclType = restrictStandardDeclType
  isAuxiliaryConstraint e = case e of
    App (Builtin _ NatInDomainConstraint) _ -> True
    _ -> False
  solveAuxiliaryInstanceConstraint = solveIndexConstraint
  addAuxiliaryInputOutputConstraints = return
  generateDefaultAuxiliaryConstraint = addNewStandardAuxiliaryConstraintUsingDefaults

convertToTypingBuiltins :: (MonadCompile m) => BuiltinUpdate m Builtin Builtin
convertToTypingBuiltins p t args = return $ normAppList (Builtin p t) args

restrictStandardDeclType ::
  forall m.
  (MonadTypeChecker Builtin m) =>
  RestrictedDecl ->
  DeclProvenance ->
  Type Builtin ->
  m (Type Builtin)
restrictStandardDeclType declSort (ident, p) typ = do
  env <- getFreeEnv
  let tc = case declSort of
        RestrictedProperty -> ValidPropertyType
        RestrictedParameter s -> ValidParameterType s
        RestrictedDataset -> ValidDatasetType
        RestrictedNetwork -> ValidNetworkType

  let expr = BuiltinExpr p (TypeClass tc) [explicit typ]
  let origin = InstanceTypeRestrictionOrigin $ TypeRestrictionOrigin env (ident, provenanceOf typ) declSort typ
  _ <- createFreshInstanceConstraint False mempty p origin Irrelevant expr
  return typ

-- | Tries to add new unification constraints using default values.
addNewStandardAuxiliaryConstraintUsingDefaults ::
  (MonadTypeChecker Builtin m) =>
  Maybe (Decl Builtin) ->
  m Bool
addNewStandardAuxiliaryConstraintUsingDefaults maybeDecl = do
  -- Calculate the set of candidate constraints
  auxiliaryConstraints <- getActiveAuxiliaryInstanceConstraints
  defaultableConstraints <- getDefaultableConstraints maybeDecl auxiliaryConstraints
  solveDefaultIndexConstraints defaultableConstraints

extractElementType :: (PrintableBuiltin builtin1, PrintableBuiltin builtin2) => builtin1 -> [Arg builtin2] -> Expr builtin2
extractElementType b args = case args of
  [tElem] -> argExpr tElem
  _ -> monomorphisationError b args

monomorphisationError :: (PrintableBuiltin builtin1, PrintableBuiltin builtin2) => builtin1 -> [Arg builtin2] -> a
monomorphisationError b args = do
  let exprDoc = prettyVerbose args
  developerError $
    "Monomorphisation should have got rid of" <+> quotePretty (show b) <> "s but found applied to args" <+> squotes exprDoc

-------------------------------------------------------------------------------
-- Linearity

instance HasTypeSystem LinearityBuiltin where
  convertFromStandardBuiltins = convertToLinearityTypes
  restrictDeclType = restrictLinearityDeclType
  isAuxiliaryConstraint _ = True
  solveAuxiliaryInstanceConstraint = solveLinearityConstraint
  addAuxiliaryInputOutputConstraints = addFunctionAuxiliaryInputOutputConstraints (LinearityRelation . FunctionLinearity)
  generateDefaultAuxiliaryConstraint _ = return False

pattern LinearityExpr :: Provenance -> Linearity -> Expr LinearityBuiltin
pattern LinearityExpr p lin = Builtin p (Linearity lin)

freshLinearityMeta :: (MonadTypeChecker LinearityBuiltin m) => Provenance -> m (Expr LinearityBuiltin)
freshLinearityMeta p = unnormalised <$> freshMetaExpr p (TypeUniverse p 0) mempty

convertToLinearityTypes ::
  forall m.
  (MonadTypeChecker LinearityBuiltin m) =>
  BuiltinUpdate m Builtin LinearityBuiltin
convertToLinearityTypes p b args = case b of
  BuiltinFunction f -> do
    let args' = case f of
          StackTensor -> implicit (Builtin p (LinearityConstructor (NatLiteral (length args)))) : args
          _ -> args
    return $ normAppList (Builtin p (LinearityFunction f)) args'
  BuiltinConstructor c -> return $ normAppList (Builtin p (LinearityConstructor c)) args
  BuiltinType s -> case s of
    UnitType -> return $ Builtin p $ Linearity Constant
    BoolType {} -> freshLinearityMeta p
    RatType {} -> freshLinearityMeta p
    IndexType -> freshLinearityMeta p
    NatType -> freshLinearityMeta p
    ListType -> return $ extractElementType b args
    TensorType -> return $ extractElementType b args
  TypeClass {} -> monomorphisationError b args
  TypeClassOp {} -> monomorphisationError b args
  NatInDomainConstraint -> monomorphisationError b args

restrictLinearityDeclType ::
  forall m.
  (MonadTypeChecker LinearityBuiltin m) =>
  RestrictedDecl ->
  DeclProvenance ->
  Type LinearityBuiltin ->
  m (Type LinearityBuiltin)
restrictLinearityDeclType rDecl declProv declType = do
  freeEnv <- getFreeEnv
  let origin = InstanceTypeRestrictionOrigin $ TypeRestrictionOrigin freeEnv declProv rDecl declType
  case rDecl of
    RestrictedNetwork -> restrictLinearityNetworkType origin declProv declType
    RestrictedDataset -> assertConstantLinearity origin declProv declType
    RestrictedParameter {} -> assertConstantLinearity origin declProv declType
    RestrictedProperty {} -> return declType

restrictLinearityNetworkType ::
  forall m.
  (MonadTypeChecker LinearityBuiltin m) =>
  InstanceConstraintOrigin LinearityBuiltin ->
  DeclProvenance ->
  Type LinearityBuiltin ->
  m (Type LinearityBuiltin)
restrictLinearityNetworkType origin (ident, p) networkType = do
  inputLin <- freshLinearityMeta p
  outputLin <- freshLinearityMeta p

  let inputLinBinder = Binder p (BinderDisplayForm OnlyType False) Explicit Relevant inputLin
  let functionNetworkType = Pi p inputLinBinder outputLin
  createFreshUnificationConstraint p mempty (CheckingInstanceType origin) networkType functionNetworkType

  -- The linearity of the output of a network is the max of 1) Linear (as outputs
  -- are also variables) and 2) the linearity of its input. So prepend this
  -- constraint to the front of the type.
  logDebug MaxDetail "Appending `MaxLinearity` constraint to network type"
  let outputLinProvenance = Linear $ NetworkOutputProvenance p (nameOf ident)
  let linConstraintArgs = [LinearityExpr p outputLinProvenance, inputLin, outputLin]
  let linConstraint = App (Builtin p (LinearityRelation MaxLinearity)) (Arg p Explicit Relevant <$> linConstraintArgs)
  let linConstraintBinder = Binder p (BinderDisplayForm OnlyType False) (Instance True) Irrelevant linConstraint

  return $ Pi p linConstraintBinder functionNetworkType

assertConstantLinearity ::
  (MonadTypeChecker LinearityBuiltin m) =>
  InstanceConstraintOrigin LinearityBuiltin ->
  DeclProvenance ->
  Type LinearityBuiltin ->
  m (Type LinearityBuiltin)
assertConstantLinearity origin (_, p) t = do
  createFreshUnificationConstraint p mempty (CheckingInstanceType origin) (LinearityExpr p Constant) t
  return t

-------------------------------------------------------------------------------
-- Polarity

instance HasTypeSystem PolarityBuiltin where
  convertFromStandardBuiltins = convertToPolarityTypes
  restrictDeclType = restrictDeclPolarityType
  isAuxiliaryConstraint _ = True
  solveAuxiliaryInstanceConstraint = solvePolarityConstraint
  addAuxiliaryInputOutputConstraints = addFunctionAuxiliaryInputOutputConstraints (PolarityRelation . FunctionPolarity)
  generateDefaultAuxiliaryConstraint _ = return False

pattern PolarityExpr :: Provenance -> Polarity -> Expr PolarityBuiltin
pattern PolarityExpr p pol = Builtin p (Polarity pol)

freshPolarityMeta :: (MonadTypeChecker PolarityBuiltin m) => Provenance -> m (Expr PolarityBuiltin)
freshPolarityMeta p = unnormalised <$> freshMetaExpr p (TypeUniverse p 0) mempty

convertToPolarityTypes ::
  forall m.
  (MonadTypeChecker PolarityBuiltin m) =>
  BuiltinUpdate m Builtin PolarityBuiltin
convertToPolarityTypes p b args = case b of
  BuiltinFunction f -> do
    let args' = case f of
          StackTensor -> implicit (Builtin p (PolarityConstructor (NatLiteral (length args)))) : args
          _ -> args
    return $ normAppList (Builtin p (PolarityFunction f)) args'
  BuiltinConstructor c -> return $ normAppList (Builtin p (PolarityConstructor c)) args
  BuiltinType s -> case s of
    UnitType -> return $ PolarityExpr p Unquantified
    RatType {} -> freshPolarityMeta p
    BoolType {} -> freshPolarityMeta p
    IndexType -> return $ PolarityExpr p Unquantified
    NatType -> return $ PolarityExpr p Unquantified
    ListType -> return $ extractElementType b args
    TensorType -> return $ extractElementType b args
  TypeClass {} -> monomorphisationError b args
  TypeClassOp {} -> monomorphisationError b args
  NatInDomainConstraint -> monomorphisationError b args

restrictDeclPolarityType ::
  forall m.
  (MonadTypeChecker PolarityBuiltin m) =>
  RestrictedDecl ->
  DeclProvenance ->
  Type PolarityBuiltin ->
  m (Type PolarityBuiltin)
restrictDeclPolarityType rDecl declProv declType = do
  freeEnv <- getFreeEnv
  let origin = InstanceTypeRestrictionOrigin $ TypeRestrictionOrigin freeEnv declProv rDecl declType

  case rDecl of
    RestrictedNetwork -> restrictPolarityNetworkType origin declProv declType
    RestrictedDataset -> assertUnquantifiedPolarity origin declProv declType
    RestrictedParameter {} -> assertUnquantifiedPolarity origin declProv declType
    RestrictedProperty -> return declType

restrictPolarityNetworkType ::
  forall m.
  (MonadTypeChecker PolarityBuiltin m) =>
  InstanceConstraintOrigin PolarityBuiltin ->
  DeclProvenance ->
  Type PolarityBuiltin ->
  m (Type PolarityBuiltin)
restrictPolarityNetworkType origin (_, p) networkType = do
  let inputPol = PolarityExpr p Unquantified
  let outputPol = PolarityExpr p Unquantified

  let inputPolBinder = Binder p (BinderDisplayForm OnlyType False) Explicit Relevant inputPol
  let functionNetworkType = Pi p inputPolBinder outputPol
  createFreshUnificationConstraint p mempty (CheckingInstanceType origin) networkType functionNetworkType
  return networkType

assertUnquantifiedPolarity ::
  (MonadTypeChecker PolarityBuiltin m) =>
  InstanceConstraintOrigin PolarityBuiltin ->
  DeclProvenance ->
  Type PolarityBuiltin ->
  m (Type PolarityBuiltin)
assertUnquantifiedPolarity origin (_, p) t = do
  createFreshUnificationConstraint p mempty (CheckingInstanceType origin) (PolarityExpr p Unquantified) t
  return t
