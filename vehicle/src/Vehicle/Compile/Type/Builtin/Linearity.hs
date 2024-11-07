{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Compile.Type.Builtin.Linearity
  ( typeLinearityBuiltin,
    isLinearityBuiltinConstructor,
  )
where

import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Core hiding (Builtin (..))
import Vehicle.Data.Builtin.Linearity
import Vehicle.Data.Code.DSL (iterate)
import Vehicle.Data.DSL
import Prelude hiding (iterate)

isLinearityBuiltinConstructor :: LinearityBuiltin -> Bool
isLinearityBuiltinConstructor = \case
  LinearityConstructor {} -> True
  LinearityFunction {} -> False
  Linearity {} -> True
  LinearityRelation {} -> True

-- | Return the type of the provided builtin.
typeLinearityBuiltin :: Provenance -> LinearityBuiltin -> Type LinearityBuiltin
typeLinearityBuiltin p b = fromDSL p $ case b of
  LinearityConstructor c -> typeOfConstructor c
  LinearityFunction f -> typeOfBuiltinFunction f
  Linearity {} -> tLin
  LinearityRelation r -> typeOfLinearityRelation r

typeOfBuiltinFunction :: BuiltinFunction -> LinearityDSLExpr
typeOfBuiltinFunction = \case
  -- Boolean operations
  Not {} -> typeOfOp1
  Implies -> typeOfOp2 maxLinearity
  And {} -> typeOfOp2 maxLinearity
  Or {} -> typeOfOp2 maxLinearity
  QuantifyRatTensor q -> typeOfQuantifier q
  If -> typeOfIf
  ReduceAndTensor -> typeOfOp1
  ReduceOrTensor -> typeOfOp1
  -- Arithmetic operations
  Add {} -> typeOfOp2 maxLinearity
  Mul {} -> typeOfOp2 mulLinearity
  Neg {} -> typeOfOp1
  Sub {} -> typeOfOp2 maxLinearity
  Div {} -> typeOfOp2 divLinearity
  Min {} -> typeOfOp2 maxLinearity
  Max {} -> typeOfOp2 maxLinearity
  PowRat {} -> typeOfOp2 powLinearity
  ReduceAddRatTensor -> typeOfOp1
  ReduceMulRatTensor ->
    forAllLinearities $ \l1 ->
      forAllLinearities $ \l2 ->
        mulLinearity l1 l1 l2 .~~~> l1 ~> l2
  ReduceMinRatTensor -> typeOfOp1
  ReduceMaxRatTensor -> typeOfOp1
  -- Comparisons
  Equals {} -> typeOfOp2 maxLinearity
  Order {} -> typeOfOp2 maxLinearity
  -- Conversion functions
  FromNat {} -> constant ~> constant
  FromRat {} -> constant ~> constant
  FromVectorToList -> typeOfVectorToList
  -- Container functions
  FoldList -> typeOfFold
  MapList -> typeOfMap
  At -> typeOfAt
  StackTensor -> typeOfStack
  ConstTensor -> forAllLinearities $ \l -> l ~> constant ~> l
  Foreach -> forAllLinearities $ \l -> l ~> l
  Iterate -> typeOfIterate
  FlattenTensorType -> type0 ~> type0

typeOfConstructor :: BuiltinConstructor -> LinearityDSLExpr
typeOfConstructor = \case
  Nil -> typeOfNil
  Cons -> typeOfCons
  UnitLiteral {} -> constant
  IndexLiteral {} -> constant
  NatLiteral {} -> constant
  NatTensorLiteral {} -> constant
  BoolTensorLiteral {} -> constant
  IndexTensorLiteral {} -> constant
  RatTensorLiteral {} -> constant

typeOfLinearityRelation :: LinearityRelation -> LinearityDSLExpr
typeOfLinearityRelation = \case
  MaxLinearity -> tLin ~> tLin ~> tLin ~> type0
  MulLinearity -> tLin ~> tLin ~> tLin ~> type0
  DivLinearity -> tLin ~> tLin ~> tLin ~> type0
  PowLinearity -> tLin ~> tLin ~> tLin ~> type0
  FunctionLinearity {} -> tLin ~> tLin ~> type0
  QuantifierLinearity {} -> (tLin ~> tLin) ~> tLin ~> type0

typeOfOp1 :: LinearityDSLExpr
typeOfOp1 = forAllLinearities $ \l -> l ~> l

typeOfOp2 ::
  (LinearityDSLExpr -> LinearityDSLExpr -> LinearityDSLExpr -> LinearityDSLExpr) ->
  LinearityDSLExpr
typeOfOp2 constraint =
  forAllLinearityTriples $ \l1 l2 l3 ->
    constraint l1 l2 l3 .~~~> l1 ~> l2 ~> l3

typeOfIf :: LinearityDSLExpr
typeOfIf =
  forAllLinearityTriples $ \lCond lArg1 lArg2 ->
    forAllLinearities $ \lArgs ->
      forAllLinearities $ \lRes ->
        maxLinearity lCond lArgs lRes
          .~~~> maxLinearity lArg1 lArg2 lArgs
          .~~~> lCond
          ~> lArg1
          ~> lArg2
          ~> lRes

typeOfNil :: LinearityDSLExpr
typeOfNil = constant

typeOfCons :: LinearityDSLExpr
typeOfCons = typeOfOp2 maxLinearity

typeOfAt :: LinearityDSLExpr
typeOfAt = forAllLinearities $ \l -> l ~> constant ~> l

typeOfFold :: LinearityDSLExpr
typeOfFold =
  forAllLinearityTriples $ \l1 l2 l3 ->
    maxLinearity l1 l2 l3 .~~~> (l1 ~> l2 ~> l3) ~> l2 ~> l1 ~> l3

typeOfMap :: LinearityDSLExpr
typeOfMap =
  forAllLinearities $ \l1 ->
    forAllLinearities $ \l2 ->
      (l1 ~> l2) ~> l1 ~> l2

typeOfQuantifier :: Quantifier -> LinearityDSLExpr
typeOfQuantifier q =
  forAll "f" type0 $ \tLam ->
    forAll "A" type0 $ \tRes ->
      quantLinearity q tLam tRes .~~~> tLam ~> tRes

typeOfIterate :: LinearityDSLExpr
typeOfIterate = ((type0 ~> type0) ~> type0 ~> type0) ~> constant ~> type0

typeOfVectorLiteral :: LinearityDSLExpr
typeOfVectorLiteral =
  forAll "n" constant $ \n ->
    iterate
      type0
      ( \fn maxSoFar ->
          forAll "l" tLin $ \li ->
            forAll "l_max" tLin $ \newMax ->
              maxLinearity maxSoFar li newMax .~~~> li ~> fn @@ [newMax]
      )
      n
      constant

typeOfStack :: LinearityDSLExpr
typeOfStack = typeOfVectorLiteral

typeOfVectorToList :: LinearityDSLExpr
typeOfVectorToList = typeOfVectorLiteral
