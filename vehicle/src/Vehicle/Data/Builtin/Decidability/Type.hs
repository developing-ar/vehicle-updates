{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Data.Builtin.Decidability.Type
  ( typeDecidabilityBuiltin,
  )
where

import Vehicle.Compile.Prelude
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
  DecidabilityBuiltinType {} -> False
  DecidabilityBuiltinTypeClass {} -> False
  DecidabilityBuiltinTypeClassOp {} -> False
  DecidabilityBuiltinFunction {} -> False
  DecidabilityBuiltinConstructor {} -> True

typeDecidabilityBuiltin :: DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin
typeDecidabilityBuiltin = \case
  StandardBuiltinType t -> typeOfBuiltinType t
  StandardBuiltinConstructor c -> typeOfBuiltinConstructor c
  StandardBuiltinFunction f -> case f of
    -- We change `If` to require decidable booleans
    If -> forAllTypes $ \t -> tDecBool ~> t ~> t ~> t
    _ -> typeOfBuiltinFunction f
  DecidabilityBuiltinType t -> typeDecidableType t
  DecidabilityBuiltinTypeClass t -> typeDecidableTypeClass t
  DecidabilityBuiltinTypeClassOp t -> typeDecidableTypeClassOp t
  DecidabilityBuiltinConstructor c -> typeDecidableConstructor c
  DecidabilityBuiltinFunction f -> typeDecidableFunction f

typeDecidableType :: DecidabilityBuiltinType -> DSLExpr DecidabilityBuiltin
typeDecidableType = \case
  DecBoolType -> type0

typeDecidableTypeClass :: DecidabilityBuiltinTypeClass -> DSLExpr DecidabilityBuiltin
typeDecidableTypeClass = \case
  IsBool -> type0 ~> type0
  HasBoolTensorLiterals -> type0 ~> type0
  HasNot -> type0 ~> type0
  HasAnd -> type0 ~> type0
  HasOr -> type0 ~> type0
  HasImplies -> type0 ~> type0
  HasCompare {} -> type0 ~> type0
  HasReduceAndTensor -> type0 ~> type0
  HasReduceOrTensor -> type0 ~> type0

typeDecidableTypeClassOp :: DecidabilityBuiltinTypeClassOp -> DSLExpr DecidabilityBuiltin
typeDecidableTypeClassOp = \case
  BoolTypeTC -> constraint IsBool id
  FromBoolTensorLitTC -> constraint HasBoolTensorLiterals typeOfCast
  NotTC -> constraint HasNot typeOfTensorOp1
  AndTC -> constraint HasAnd typeOfTensorOp2
  OrTC -> constraint HasOr typeOfTensorOp2
  ImpliesTC -> constraint HasImplies typeOfTensorOp2
  CompareTC dom op -> constraint (HasCompare dom op) (typeOfComparisonOp dom)
  ReduceAndTensorTC -> constraint HasReduceAndTensor typeOfTensorReduceOp
  ReduceOrTensorTC -> constraint HasReduceAndTensor typeOfTensorReduceOp

constraint :: DecidabilityBuiltinTypeClass -> (DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin) -> DSLExpr DecidabilityBuiltin
constraint c f =
  forAllTypes $ \t ->
    builtin (DecidabilityBuiltinTypeClass c) @@ [t] ~~~> f t

typeDecidableConstructor :: DecidabilityBuiltinConstructor -> DSLExpr DecidabilityBuiltin
typeDecidableConstructor = \case
  DecBoolTensor bs -> tTensor tDecBool (shapeOf bs)

typeDecidableFunction :: DecidabilityBuiltinFunction -> DSLExpr DecidabilityBuiltin
typeDecidableFunction = \case
  DecNot -> typeOfTensorOp1 tDecBool
  DecAnd -> typeOfTensorOp2 tDecBool
  DecOr -> typeOfTensorOp2 tDecBool
  DecImplies -> typeOfTensorOp2 tDecBool
  DecCompare dom _op -> typeOfComparisonOp dom tDecBool
  DecReduceAndTensor -> typeOfTensorReduceOp tDecBool
  DecReduceOrTensor -> typeOfTensorReduceOp tDecBool
  BoolTensorToDecBoolTensor -> typeOfCast tDecBool

typeOfCast :: DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin
typeOfCast t = forAllDims $ \dims -> tBoolTensor dims ~> tTensor t dims

--------------------------------------------------------------------------------
-- TypeSystem
--------------------------------------------------------------------------------

instance HasTypeSystem DecidabilityBuiltin where
  convertFromStandardBuiltins = convertToDecidabilityBuiltins
  restrictDeclType _ _ = return
  isAuxiliaryConstraint _ = False

  solveAuxiliaryInstanceConstraint = decidableAuxError
  addAuxiliaryInputOutputConstraints = decidableAuxError
  generateDefaultAuxiliaryConstraint = decidableAuxError

convertToDecidabilityBuiltins ::
  forall m.
  (MonadTypeChecker DecidabilityBuiltin m) =>
  BuiltinUpdate m Builtin DecidabilityBuiltin
convertToDecidabilityBuiltins p b args = return $
  case b of
    BuiltinFunction f -> do
      let b' = case f of
            -- Convert to type-classes for resolution
            Not -> DecidabilityBuiltinTypeClassOp NotTC
            And -> DecidabilityBuiltinTypeClassOp AndTC
            Or -> DecidabilityBuiltinTypeClassOp OrTC
            Implies -> DecidabilityBuiltinTypeClassOp ImpliesTC
            Compare dom op -> DecidabilityBuiltinTypeClassOp $ CompareTC dom op
            -- Standard conversion
            QuantifyRatTensor q -> StandardBuiltinFunction $ QuantifyRatTensor q
            If -> StandardBuiltinFunction If
            ReduceAndTensor -> StandardBuiltinFunction ReduceAndTensor
            ReduceOrTensor -> StandardBuiltinFunction ReduceOrTensor
            Neg dom -> StandardBuiltinFunction $ Neg dom
            Add dom -> StandardBuiltinFunction $ Add dom
            Sub dom -> StandardBuiltinFunction $ Sub dom
            Mul dom -> StandardBuiltinFunction $ Mul dom
            Div dom -> StandardBuiltinFunction $ Div dom
            Min dom -> StandardBuiltinFunction $ Min dom
            Max dom -> StandardBuiltinFunction $ Max dom
            PowRat -> StandardBuiltinFunction PowRat
            ReduceAddRatTensor -> StandardBuiltinFunction ReduceAddRatTensor
            ReduceMulRatTensor -> StandardBuiltinFunction ReduceMulRatTensor
            ReduceMinRatTensor -> StandardBuiltinFunction ReduceMinRatTensor
            ReduceMaxRatTensor -> StandardBuiltinFunction ReduceMaxRatTensor
            FoldList -> StandardBuiltinFunction FoldList
            MapList -> StandardBuiltinFunction MapList
            Foreach -> StandardBuiltinFunction Foreach
            Iterate -> StandardBuiltinFunction Iterate
            At -> StandardBuiltinFunction At
            StackTensor -> StandardBuiltinFunction StackTensor
            ConstTensor -> StandardBuiltinFunction ConstTensor
      normAppList (Builtin p b') args
    BuiltinConstructor c -> case c of
      BoolTensorLiteral {} -> do
        let original = Builtin p (StandardBuiltinConstructor c)
        normAppList (Builtin p $ DecidabilityBuiltinTypeClassOp FromBoolTensorLitTC) [explicit original]
      _ -> normAppList (Builtin p (StandardBuiltinConstructor c)) args
    BuiltinType s -> do
      let b' = case s of
            BoolType {} -> DecidabilityBuiltinTypeClassOp BoolTypeTC
            _ -> StandardBuiltinType s
      normAppList (Builtin p b') args
    _ -> monomorphisationError b args

decidableAuxError :: b
decidableAuxError = developerError "Auxiliary constraints for DecidabilityBuiltin should not exist"
