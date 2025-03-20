{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Data.Builtin.Decidability.Type
  ( typeDecidabilityBuiltin,
  )
where

import Data.Proxy (Proxy (..))
import Vehicle.Compile.Context.Free (getDeclType, getFreeEnv)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Type.Bidirectional (createFreshUnificationConstraint)
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.System
import Vehicle.Data.Builtin.Decidability
import Vehicle.Data.Builtin.Interface.Type
import Vehicle.Data.Builtin.Standard (BuiltinConstructor (..), BuiltinFunction (..), BuiltinType (..))
import Vehicle.Data.Code.DSL
import Vehicle.Data.DSL
import Vehicle.Syntax.Builtin (Builtin (..))
import Prelude hiding (iterate, pi)

--------------------------------------------------------------------------------
-- Typing
--------------------------------------------------------------------------------

instance TypableBuiltin DecidabilityBuiltin where
  typeBuiltin = typeDecidabilityBuiltin
  useDependentMetas _ = True
  isConstructor = isDecidabilityConstructor

  isCastConstraint e = case e of
    DecidabilityBuiltinTypeClass HasBoolTensorLiterals -> True
    _ -> False

isDecidabilityConstructor :: DecidabilityBuiltin -> Bool
isDecidabilityConstructor = \case
  StandardBuiltinType {} -> False
  StandardBuiltinFunction {} -> False
  StandardBuiltinConstructor {} -> True
  DecidabilityBuiltinTypeClass {} -> False
  DecidabilityBuiltinTypeClassOp {} -> False
  DecidabilityBuiltinFunction {} -> False

typeDecidabilityBuiltin :: DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin
typeDecidabilityBuiltin = \case
  StandardBuiltinType t -> typeOfBuiltinType t
  StandardBuiltinConstructor c -> typeOfBuiltinConstructor c
  StandardBuiltinFunction f -> case f of
    QuantifyRatTensor {} -> forAllDims $ \_dims -> forAllTypes $ \t -> (t ~> type0) ~> type0
    _ -> typeOfBuiltinFunction f
  DecidabilityBuiltinTypeClass t -> typeDecidableTypeClass t
  DecidabilityBuiltinTypeClassOp t -> typeDecidableTypeClassOp t
  DecidabilityBuiltinFunction f -> typeDecidableFunction f

typeDecidableTypeClass :: DecidabilityBuiltinTypeClass -> DSLExpr DecidabilityBuiltin
typeDecidableTypeClass = \case
  IsBoolType -> type0 ~> type0
  IsTensorType -> type0 ~> type0
  HasBoolTensorLiterals -> type0 ~> type0
  HasNot -> (tDims ~> type0) ~> tDims ~> type0
  HasAnd -> (tDims ~> type0) ~> tDims ~> type0
  HasOr -> (tDims ~> type0) ~> tDims ~> type0
  HasImplies -> (tDims ~> type0) ~> tDims ~> type0
  HasCompare CompareNat _ -> type0 ~> type0
  HasCompare CompareIndex _ -> type0 ~> type0
  HasCompare CompareRatTensor _ -> (tDims ~> type0) ~> tDims ~> type0
  HasReduceAndTensor -> type0 ~> type0
  HasReduceOrTensor -> type0 ~> type0

typeDecidableTypeClassOp :: DecidabilityBuiltinTypeClassOp -> DSLExpr DecidabilityBuiltin
typeDecidableTypeClassOp = \case
  BoolTypeTC -> constraint IsBoolType (const type0)
  TensorTypeTC ->
    forAllExpl "t" type0 $ \t ->
      isTensorType t
        ~~~> tDims
        .~> type0
  NotTC -> tensorOpConstraint HasNot (\t dims -> typeOp1 (t .@@ [dims]))
  AndTC -> tensorOpConstraint HasAnd (\t dims -> typeOp2 (t .@@ [dims]))
  OrTC -> tensorOpConstraint HasOr (\t dims -> typeOp2 (t .@@ [dims]))
  ImpliesTC -> tensorOpConstraint HasImplies (\t dims -> typeOp2 (t .@@ [dims]))
  FromBoolTensorLitTC ->
    forAll "t" (tDims ~> type0) $ \t ->
      builtin (DecidabilityBuiltinTypeClass HasBoolTensorLiterals) @@ [t] ~~~> typeOfCast t
  CompareTC CompareIndex op -> constraint (HasCompare CompareIndex op) typeOfCompareIndex
  CompareTC CompareNat op -> constraint (HasCompare CompareNat op) typeOfCompareNat
  CompareTC CompareRatTensor op -> tensorOpConstraint (HasCompare CompareRatTensor op) typeOfCompareRatTensor
  ReduceAndTensorTC -> constraint HasReduceAndTensor typeOfTensorReduceOp
  ReduceOrTensorTC -> constraint HasReduceAndTensor typeOfTensorReduceOp

constraint :: DecidabilityBuiltinTypeClass -> (DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin) -> DSLExpr DecidabilityBuiltin
constraint c f =
  forAllTypes $ \t ->
    builtin (DecidabilityBuiltinTypeClass c) @@ [t] ~~~> f t

tensorOpConstraint :: DecidabilityBuiltinTypeClass -> (DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin) -> DSLExpr DecidabilityBuiltin
tensorOpConstraint c f =
  forAllDims $ \dims ->
    forAll "t" (tDims ~> type0) $ \t ->
      builtin (DecidabilityBuiltinTypeClass c) @@ [t, dims] ~~~> f t dims

typeDecidableFunction :: DecidabilityBuiltinFunction -> DSLExpr DecidabilityBuiltin
typeDecidableFunction = \case
  TypeTrue -> type0
  TypeFalse -> type0
  TypeNot -> typeOp1 type0
  TypeAnd -> typeOp2 type0
  TypeOr -> typeOp2 type0
  TypeImplies -> typeOp2 type0
  TypeCompare CompareIndex _op -> typeOfCompareIndex type0
  TypeCompare CompareNat _op -> typeOfCompareNat type0
  TypeCompare CompareRatTensor _op -> typeOfCompareRatTensor type0IgnoreDims type0
  -- TypeReduceAndTensor -> typeOfTensorReduceOp tDecBool
  -- TypeReduceOrTensor -> typeOfTensorReduceOp tDecBool
  BoolTensorToType -> typeOfCast type0

typeOfCompareIndex :: DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin
typeOfCompareIndex tRes =
  forAllIrrelevantNat "n1" $ \n1 ->
    forAllIrrelevantNat "n2" $ \n2 ->
      tIndex n1 ~> tIndex n2 ~> tRes

typeOfCompareNat :: DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin
typeOfCompareNat tRes = tNat ~> tNat ~> tRes

typeOfCompareRatTensor :: DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin
typeOfCompareRatTensor tRes dims = tTensor tRat dims ~> tTensor tRat dims ~> tRes .@@ [dims]

typeOfCast :: DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin
typeOfCast t = forAllDims $ \dims -> tBoolTensor dims ~> t .@@ [dims]

typeOp1 :: DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin
typeOp1 t = t ~> t

typeOp2 :: DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin
typeOp2 t = t ~> t ~> t

--------------------------------------------------------------------------------
-- TypeSystem
--------------------------------------------------------------------------------

instance HasTypeSystem DecidabilityBuiltin where
  convertFromStandardBuiltins x = traverseFreeVarsM (const id) convertToDecidabilityFreeVars =<< traverseBuiltinsM convertToDecidabilityBuiltins x
  restrictDeclType = restrictDecidabilityDeclType
  isAuxiliaryConstraint _ = False

  solveAuxiliaryInstanceConstraint _ = return ()
  addAuxiliaryInputOutputConstraints = return
  generateDefaultAuxiliaryConstraint _ = return False

convertToDecidabilityFreeVars ::
  forall m.
  (MonadTypeChecker DecidabilityBuiltin m) =>
  FreeVarUpdate m DecidabilityBuiltin
convertToDecidabilityFreeVars f p ident args = do
  declType <- getDeclType (Proxy @DecidabilityBuiltin) ident
  args' <- traverseArgs f args
  finalArgs <- insertNewArgs args' declType
  return $ normAppList (FreeVar p ident) finalArgs
  where
    insertNewArgs :: [Arg DecidabilityBuiltin] -> Type DecidabilityBuiltin -> m [Arg DecidabilityBuiltin]
    insertNewArgs as = \case
      Pi _ binder result -> do
        if wasInsertedByCompiler binder && isImplicit binder
          then (argFromBinder binder (Hole p "_") :) <$> insertNewArgs as result
          else return as
      _ -> return as

convertToDecidabilityBuiltins ::
  forall m.
  (MonadTypeChecker DecidabilityBuiltin m) =>
  BuiltinUpdate m Builtin DecidabilityBuiltin
convertToDecidabilityBuiltins p b args =
  case b of
    BuiltinFunction f -> do
      case f of
        -- Convert to type-classes for resolution
        Not -> convertTo NotTC
        And -> convertTo AndTC
        Or -> convertTo OrTC
        Implies -> convertTo ImpliesTC
        Compare dom op -> case dom of
          CompareIndex -> convertToWith (CompareTC dom op) [implicit (Hole p "_")]
          _ -> convertTo $ CompareTC dom op
        ReduceAndTensor -> convertTo ReduceAndTensorTC
        ReduceOrTensor -> convertTo ReduceOrTensorTC
        -- Standard conversion
        QuantifyRatTensor q -> sameFunction $ QuantifyRatTensor q
        If -> sameFunction If
        Neg dom -> sameFunction $ Neg dom
        Add dom -> sameFunction $ Add dom
        Sub dom -> sameFunction $ Sub dom
        Mul dom -> sameFunction $ Mul dom
        Div dom -> sameFunction $ Div dom
        Min dom -> sameFunction $ Min dom
        Max dom -> sameFunction $ Max dom
        PowRat -> sameFunction PowRat
        ReduceAddRatTensor -> sameFunction ReduceAddRatTensor
        ReduceMulRatTensor -> sameFunction ReduceMulRatTensor
        ReduceMinRatTensor -> sameFunction ReduceMinRatTensor
        ReduceMaxRatTensor -> sameFunction ReduceMaxRatTensor
        FoldList -> sameFunction FoldList
        MapList -> sameFunction MapList
        Foreach -> sameFunction Foreach
        Iterate -> sameFunction Iterate
        At -> sameFunction At
        StackTensor -> sameFunction StackTensor
        ConstTensor -> sameFunction ConstTensor
    BuiltinConstructor c -> case c of
      BoolTensorLiteral {} -> do
        let original = Builtin p (StandardBuiltinConstructor c)
        return $ normAppList (Builtin p $ DecidabilityBuiltinTypeClassOp FromBoolTensorLitTC) [explicit original]
      _ -> sameConstructor c
    BuiltinType s -> do
      let b' = case s of
            BoolType -> DecidabilityBuiltinTypeClassOp BoolTypeTC
            TensorType -> DecidabilityBuiltinTypeClassOp TensorTypeTC
            _ -> StandardBuiltinType s
      return $ normAppList (Builtin p b') args
    _ -> monomorphisationError b args
  where
    sameFunction f = return $ normAppList (Builtin p (StandardBuiltinFunction f)) args
    sameConstructor c = return $ normAppList (Builtin p (StandardBuiltinConstructor c)) args
    convertToWith t extraArgs = return $ normAppList (Builtin p (DecidabilityBuiltinTypeClassOp t)) (extraArgs <> args)
    convertTo t = convertToWith t []

restrictDecidabilityDeclType ::
  forall m.
  (MonadTypeChecker DecidabilityBuiltin m) =>
  RestrictedDecl ->
  DeclProvenance ->
  Type DecidabilityBuiltin ->
  m (Type DecidabilityBuiltin)
restrictDecidabilityDeclType rDecl declProv@(_, p) declType = do
  freeEnv <- getFreeEnv
  let origin = InstanceTypeRestrictionOrigin $ TypeRestrictionOrigin freeEnv declProv rDecl declType
  case rDecl of
    RestrictedProperty -> do
      let desiredType = Universe mempty 0
      createFreshUnificationConstraint p mempty (CheckingInstanceType origin) desiredType declType
      return declType
    _ -> return declType
