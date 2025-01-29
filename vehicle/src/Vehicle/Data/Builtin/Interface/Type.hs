module Vehicle.Data.Builtin.Interface.Type where

import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Code.DSL
import Vehicle.Data.DSL

typeOfTCOp1 :: (DSLExpr builtin -> DSLExpr builtin -> DSLExpr builtin) -> DSLExpr builtin
typeOfTCOp1 constraint =
  forAll "A" type0 $ \t1 ->
    forAll "B" type0 $ \t2 ->
      constraint t1 t2 ~~~> t1 ~> t2

typeOfTCOp2 :: (DSLExpr builtin -> DSLExpr builtin -> DSLExpr builtin -> DSLExpr builtin) -> DSLExpr builtin
typeOfTCOp2 constraint =
  forAll "A" type0 $ \t1 ->
    forAll "B" type0 $ \t2 ->
      forAll "C" type0 $ \t3 ->
        constraint t1 t2 t3 ~~~> t1 ~> t2 ~> t3

typeOfTensorOp1 :: (BuiltinHasStandardTypes builtin) => DSLExpr builtin -> DSLExpr builtin
typeOfTensorOp1 tElem = forAllDims $ \dims -> tTensor tElem dims ~> tTensor tElem dims

typeOfTensorOp2 :: (BuiltinHasStandardTypes builtin) => DSLExpr builtin -> DSLExpr builtin
typeOfTensorOp2 tElem = forAllDims $ \dims -> tTensor tElem dims ~> tTensor tElem dims ~> tTensor tElem dims
