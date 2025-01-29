module Vehicle.Data.Builtin.Decidable.Type
  ( typeDecidableBuiltin,
  )
where

import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Decidable
import Vehicle.Data.Builtin.Interface.Type
import Vehicle.Data.Builtin.Standard (BuiltinFunction (If))
import Vehicle.Data.Builtin.Standard.Type (typeOfBuiltinConstructor, typeOfBuiltinFunction, typeOfBuiltinType)
import Vehicle.Data.Code.DSL
import Vehicle.Data.DSL
import Prelude hiding (iterate, pi)

typeDecidableBuiltin :: Provenance -> DecidableBuiltin -> Type DecidableBuiltin
typeDecidableBuiltin p b = fromDSL p $ case b of
  StandardBuiltinType t -> typeOfBuiltinType t
  StandardBuiltinConstructor c -> typeOfBuiltinConstructor c
  StandardBuiltinFunction f -> case f of
    If -> forAllTypes $ \t -> tDecBool ~> t ~> t ~> t
    _ -> typeOfBuiltinFunction f
  DecidableBuiltinType t -> typeDecidableType t
  DecidableBuiltinConstructor c -> typeDecidableConstructor c
  DecidableBuiltinFunction f -> typeDecidableFunction f

tDecBool :: DSLExpr DecidableBuiltin
tDecBool = builtin (DecidableBuiltinType DecBool)

typeDecidableType :: DecidableBuiltinType -> DSLExpr DecidableBuiltin
typeDecidableType = \case
  DecBool -> type0
  HasNot -> type0 ~> type0
  HasAnd -> type0 ~> type0
  HasOr -> type0 ~> type0
  HasImplies -> type0 ~> type0
  HasCompare {} -> type0 ~> type0
  HasReduceAndTensor -> type0 ~> type0
  HasReduceOrTensor -> type0 ~> type0

typeDecidableConstructor :: DecidableBuiltinConstructor -> DSLExpr DecidableBuiltin
typeDecidableConstructor = \case
  DecBoolTensor bs -> tTensor tDecBool (shapeOf bs)

typeDecidableFunction :: DecidableBuiltinFunction -> DSLExpr DecidableBuiltin
typeDecidableFunction = \case
  DecNot -> typeOfTensorOp1 tDecBool
  DecAnd -> typeOfTensorOp2 tDecBool
  DecOr -> typeOfTensorOp2 tDecBool
  DecImplies -> typeOfTensorOp2 tDecBool
  DecCompare dom op -> _
  DecReduceAndTensor -> _
  DecReduceOrTensor -> _
