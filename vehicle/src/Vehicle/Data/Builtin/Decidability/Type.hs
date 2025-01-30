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
import Vehicle.Data.Builtin.Standard (BuiltinFunction (If), BuiltinType (..))
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
  couldBeEqual = _

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
  HasNot -> type0 ~> type0
  HasAnd -> type0 ~> type0
  HasOr -> type0 ~> type0
  HasImplies -> type0 ~> type0
  HasCompare {} -> type0 ~> type0
  HasReduceAndTensor -> type0 ~> type0
  HasReduceOrTensor -> type0 ~> type0

typeDecidableTypeClassOp :: DecidabilityBuiltinTypeClassOp -> DSLExpr DecidabilityBuiltin
typeDecidableTypeClassOp = \case
  BoolTC -> constraint IsBool id
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

--------------------------------------------------------------------------------
-- TypeSystem
--------------------------------------------------------------------------------

instance HasTypeSystem DecidabilityBuiltin where
  convertFromStandardBuiltins = convertToDecidabilityBuiltins
  restrictDeclType _ _ = return
  isAuxiliaryConstraint _ = False
  isCastConstraint _ = False

  solveAuxiliaryInstanceConstraint = decidableAuxError
  addAuxiliaryInputOutputConstraints = decidableAuxError
  generateDefaultAuxiliaryConstraint = decidableAuxError

convertToDecidabilityBuiltins ::
  forall m.
  (MonadTypeChecker DecidabilityBuiltin m) =>
  BuiltinUpdate m Builtin DecidabilityBuiltin
convertToDecidabilityBuiltins p b args = do
  let b' = case b of
        BuiltinFunction f -> case f of
          _ -> _
        BuiltinConstructor c -> _
        BuiltinType s -> case s of
          BoolType {} -> DecidabilityBuiltinType DecBoolType
          _ -> StandardBuiltinType s
        _ -> monomorphisationError b args

  return $ normAppList (Builtin p b') args

decidableAuxError :: b
decidableAuxError = developerError "Auxiliary constraints for DecidabilityBuiltin should not exist"
