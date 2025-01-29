module Vehicle.Compile.Type.Builtin.Standard
  ( isStandardConstructor,
    typeStandardBuiltin,
    typeOfBuiltinConstructor,
    typeOfBuiltinFunction,
    typeOfBuiltinType,
    typeOfNatInDomainConstraint,
  )
where

import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.DSL
import Vehicle.Data.DSL
import Vehicle.Data.Tensor (tensorToList)
import Prelude hiding (iterate, pi)

-- See https://github.com/joelberkeley/spidr/blob/master/spidr/src/Tensor.idr for a dependent tensor type-system

-- | Return the type of the provided builtin.
isStandardConstructor :: Builtin -> Bool
isStandardConstructor = \case
  BuiltinConstructor {} -> True
  BuiltinFunction {} -> False
  TypeClassOp {} -> False
  TypeClass {} -> True
  BuiltinType {} -> True
  NatInDomainConstraint {} -> True

-- | Return the type of the provided builtin.
typeStandardBuiltin :: Provenance -> Builtin -> Type Builtin
typeStandardBuiltin p b = fromDSL p $ case b of
  BuiltinConstructor c -> typeOfBuiltinConstructor c
  BuiltinFunction f -> typeOfBuiltinFunction f
  TypeClassOp tcOp -> typeOfTypeClassOp tcOp
  TypeClass tc -> typeOfTypeClass tc
  BuiltinType s -> typeOfBuiltinType s
  NatInDomainConstraint {} -> typeOfNatInDomainConstraint

--------------------------------------------------------------------------------
-- Type classes

typeOfTypeClass :: (HasStandardBuiltins builtin) => TypeClass -> DSLExpr builtin
typeOfTypeClass tc = case tc of
  HasCompare {} -> type0 ~> type0 ~> type0
  HasQuantifier {} -> type0 ~> type0 ~> type0
  HasAdd -> type0 ~> type0 ~> type0 ~> type0
  HasSub -> type0 ~> type0 ~> type0 ~> type0
  HasMul -> type0 ~> type0 ~> type0 ~> type0
  HasDiv -> type0 ~> type0 ~> type0 ~> type0
  HasNeg -> type0 ~> type0 ~> type0
  HasMap -> (type0 ~> type0) ~> type0
  HasFold -> (type0 ~> type0) ~> type0
  HasQuantifierIn {} -> type0 ~> type0 ~> type0
  HasNatLits {} -> type0 ~> type0
  HasRatLits -> type0 ~> type0
  HasVecLits {} -> tNat ~> (type0 ~> type0) ~> type0
  ValidPropertyType -> type0 ~> type0
  ValidParameterType {} -> type0 ~> type0
  ValidNetworkType -> type0 ~> type0
  ValidNetworkTensorType -> type0 ~> type0
  ValidDatasetType -> type0 ~> type0
  ValidDatasetListElementType -> type0 ~> type0
  ValidDatasetTensorElementType -> type0 ~> type0
  IsTensorType {} -> typeOfBuiltinType TensorType

typeOfTypeClassOp :: (HasStandardBuiltins builtin, BuiltinHasStandardTypeClasses builtin) => TypeClassOp -> DSLExpr builtin
typeOfTypeClassOp b = case b of
  TensorTypeTC ->
    forAllExpl "t" type0 $ \t ->
      pi (Just "ds") Explicit Irrelevant tDims $ \ds ->
        isTensorType t ds ~~~> type0
  FromNatTC -> forAllTypes $ \t -> hasNatLits t ~~~> typeOfFromNat t
  FromRatTC -> forAllTypes $ \t -> hasRatLits t ~~~> typeOfFromRat t
  VecLiteralTC -> typeOfVectorLiteral
  NegTC -> typeOfTCOp1 hasNeg
  AddTC -> typeOfTCOp2 hasAdd
  SubTC -> typeOfTCOp2 hasSub
  MulTC -> typeOfTCOp2 hasMul
  DivTC -> typeOfTCOp2 hasDiv
  CompareTC op -> typeOfTCComparisonOp $ hasCompare op
  MapTC -> forAll "f" (type0 ~> type0) $ \f -> hasMap f ~~~> typeOfMap f
  FoldTC -> forAll "f" (type0 ~> type0) $ \f -> hasFold f ~~~> typeOfFold f
  QuantifierTC q ->
    forAll "A" (type0 ~> type0) $ \t ->
      hasQuantifier q t ~~~> typeOfQuantifier t

--------------------------------------------------------------------------------
-- Generic

typeOfBuiltinFunction :: (HasStandardBuiltins builtin) => BuiltinFunction -> DSLExpr builtin
typeOfBuiltinFunction = \case
  -- Boolean operations
  Not -> typeOfTensorBoolOp1
  And -> typeOfTensorBoolOp2
  Or -> typeOfTensorBoolOp2
  Implies -> typeOfTensorBoolOp2
  QuantifyRatTensor _ -> forAllExpl "A" type0 $ \a -> typeOfQuantifier a
  If -> typeOfIf
  ReduceAndTensor -> typeOfTensorBoolReduceOp
  ReduceOrTensor -> typeOfTensorBoolReduceOp
  -- Arithmetic operations
  Neg dom -> case dom of
    NegRatTensor -> typeOfTensorRatOp1
  Add dom -> case dom of
    AddNat -> tNat ~> tNat ~> tNat
    AddRatTensor -> typeOfTensorRatOp2
  Sub dom -> case dom of
    SubRatTensor -> typeOfTensorRatOp2
  Mul dom -> case dom of
    MulNat -> tNat ~> tNat ~> tNat
    MulRatTensor -> typeOfTensorRatOp2
  Div dom -> case dom of
    DivRatTensor -> typeOfTensorRatOp2
  Min dom -> case dom of
    MinRatTensor -> typeOfTensorRatOp2
  Max dom -> case dom of
    MaxRatTensor -> typeOfTensorRatOp2
  PowRat -> forAllDims $ \dims -> tRatTensor dims ~> tNat ~> tRatTensor dims
  ReduceAddRatTensor -> typeOfTensorRatReduceOp
  ReduceMulRatTensor -> typeOfTensorRatReduceOp
  ReduceMinRatTensor -> typeOfTensorRatReduceOp
  ReduceMaxRatTensor -> typeOfTensorRatReduceOp
  -- Comparisons
  Compare dom _op -> case dom of
    CompareIndex {} ->
      forAllIrrelevantNat "n1" $ \n1 ->
        forAllIrrelevantNat "n2" $ \n2 ->
          tIndex n1 ~> tIndex n2 ~> tBoolTensor dimNil
    CompareNat {} ->
      tNat ~> tNat ~> tBoolTensor dimNil
    CompareRatTensor {} ->
      forAllDims $ \dims ->
        tRatTensor dims ~> tRatTensor dims ~> tBoolTensor dimNil
  -- Conversion functions
  FromNat dom -> case dom of
    FromNatToNat -> typeOfFromNat tNat
    FromNatToIndex -> forAllIrrelevantNat "n" $ \s -> typeOfFromNat (tIndex s)
    FromNatToRat -> typeOfFromNat (tRatTensor dimNil)
  FromRat dom -> case dom of
    FromRatToRat -> typeOfFromRat (tRatTensor dimNil)
  FromVectorToList -> typeOfFromVectorToList
  -- Container functions
  FoldList -> typeOfFold tListRaw
  MapList -> typeOfMap tListRaw
  At -> typeOfAt
  StackTensor -> typeOfStackTensor
  ConstTensor -> typeOfConstTensor
  Foreach -> typeOfForeach
  Iterate -> forAllTypes $ \t -> ((t ~> t) ~> t ~> t) ~> tNat ~> t

typeOfBuiltinType :: (HasStandardBuiltins builtin) => BuiltinType -> DSLExpr builtin
typeOfBuiltinType = \case
  UnitType -> type0
  BoolType -> type0
  NatType -> type0
  RatType -> type0
  ListType -> type0 ~> type0
  TensorType -> type0 ~> tList tNat .~> type0
  IndexType -> tNat .~> type0

typeOfConstTensor :: (HasStandardBuiltins builtin) => DSLExpr builtin
typeOfConstTensor =
  forAll "A" type0 $ \tElem ->
    tElem ~> tDims ~> tTensor tElem tDims

typeOfBuiltinConstructor :: (HasStandardBuiltins builtin) => BuiltinConstructor -> DSLExpr builtin
typeOfBuiltinConstructor = \case
  Nil -> typeOfNil
  Cons -> typeOfCons
  UnitLiteral -> tUnit
  IndexLiteral x -> forAllIrrelevantNat "n" $ \n -> natInDomainConstraint (natLit x) n .~~~> tIndex n
  NatLiteral {} -> tNat
  NatTensorLiteral t -> tNatTensor (shapeOf t)
  BoolTensorLiteral t -> tBoolTensor (shapeOf t)
  IndexTensorLiteral t -> forAllIrrelevantNat "n" $ \n -> foldr (\x r -> natInDomainConstraint (natLit x) n .~~~> r) (tTensor (tIndex n) (shapeOf t)) (tensorToList t)
  RatTensorLiteral t -> tRatTensor (shapeOf t)

typeOfTensorRatOp1 :: (BuiltinHasStandardTypes builtin) => DSLExpr builtin
typeOfTensorRatOp1 = forAllDims $ \dims -> tRatTensor dims ~> tRatTensor dims

typeOfTensorRatOp2 :: (BuiltinHasStandardTypes builtin) => DSLExpr builtin
typeOfTensorRatOp2 = forAllDims $ \dims -> tRatTensor dims ~> tRatTensor dims ~> tRatTensor dims

typeOfTensorBoolOp1 :: (BuiltinHasStandardTypes builtin) => DSLExpr builtin
typeOfTensorBoolOp1 = forAllDims $ \dims -> tBoolTensor dims ~> tBoolTensor dims

typeOfTensorBoolOp2 :: (BuiltinHasStandardTypes builtin) => DSLExpr builtin
typeOfTensorBoolOp2 = forAllDims $ \dims -> tBoolTensor dims ~> tBoolTensor dims ~> tBoolTensor dims

typeOfTensorReduceOp ::
  (BuiltinHasStandardTypes builtin, BuiltinHasStandardData builtin) =>
  DSLExpr builtin ->
  DSLExpr builtin
typeOfTensorReduceOp tElem = forAllDims $ \dims -> tTensor tElem dimNil ~> tTensor tElem dims ~> tTensor tElem dimNil

typeOfTensorRatReduceOp :: (BuiltinHasStandardTypes builtin, BuiltinHasStandardData builtin) => DSLExpr builtin
typeOfTensorRatReduceOp = typeOfTensorReduceOp tRat

typeOfTensorBoolReduceOp :: (BuiltinHasStandardTypes builtin, BuiltinHasStandardData builtin) => DSLExpr builtin
typeOfTensorBoolReduceOp = typeOfTensorReduceOp tBool

typeOfIf :: (BuiltinHasStandardTypes builtin, BuiltinHasStandardData builtin) => DSLExpr builtin
typeOfIf =
  forAll "A" type0 $ \t ->
    tBoolTensor dimNil ~> t ~> t ~> t

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

typeOfTCComparisonOp ::
  (BuiltinHasStandardTypes builtin) =>
  (DSLExpr builtin -> DSLExpr builtin -> DSLExpr builtin -> DSLExpr builtin) ->
  DSLExpr builtin
typeOfTCComparisonOp constraint =
  forAllTypeTriples $ \t1 t2 t3 ->
    constraint t1 t2 t3
      ~~~> typeOfComparisonOp t1 t2 t3

typeOfComparisonOp :: (BuiltinHasStandardTypes builtin) => DSLExpr builtin -> DSLExpr builtin -> DSLExpr builtin -> DSLExpr builtin
typeOfComparisonOp t1 t2 t3 = t1 ~> t2 ~> t3

typeOfNil :: (HasStandardBuiltins builtin) => DSLExpr builtin
typeOfNil =
  forAll "A" type0 $ \tElem ->
    tList tElem

typeOfCons :: (HasStandardBuiltins builtin) => DSLExpr builtin
typeOfCons =
  forAll "A" type0 $ \tElem ->
    tElem ~> tList tElem ~> tList tElem

typeOfAt :: (HasStandardBuiltins builtin) => DSLExpr builtin
typeOfAt =
  forAll "A" type0 $ \tElem ->
    forAllDim Irrelevant $ \d ->
      forAllDims $ \ds ->
        tTensor tElem (dimCons d ds) ~> tIndex d ~> tTensor tElem ds

typeOfMap :: (HasStandardBuiltins builtin) => DSLExpr builtin -> DSLExpr builtin
typeOfMap f =
  forAll "A" type0 $ \a ->
    forAll "B" type0 $ \b ->
      (a ~> b) ~> f @@ [a] ~> f @@ [b]

typeOfFold :: (HasStandardBuiltins builtin) => DSLExpr builtin -> DSLExpr builtin
typeOfFold f =
  forAll "A" type0 $ \a ->
    forAll "B" type0 $ \b ->
      (a ~> b ~> b) ~> b ~> f @@ [a] ~> b

typeOfQuantifier :: (HasStandardBuiltins builtin) => DSLExpr builtin -> DSLExpr builtin
typeOfQuantifier t = (t ~> tBoolTensor dimNil) ~> tBoolTensor dimNil

typeOfFromNat :: (HasStandardBuiltins builtin) => DSLExpr builtin -> DSLExpr builtin
typeOfFromNat t = forAllExpl "n" tNat $ \n -> natInDomainConstraint n t .~~~> t

typeOfFromRat :: (HasStandardBuiltins builtin) => DSLExpr builtin -> DSLExpr builtin
typeOfFromRat t = tRatTensor dimNil ~> t

typeOfVecLiteralCast :: (HasStandardBuiltins builtin) => DSLExpr builtin -> DSLExpr builtin -> DSLExpr builtin -> DSLExpr builtin
typeOfVecLiteralCast tCont tElem d =
  iterate type0 (\fn t -> tElem ~> fn @@ [t]) d tCont

typeOfVectorLiteral :: (BuiltinHasStandardTypeClasses builtin, HasStandardBuiltins builtin) => DSLExpr builtin
typeOfVectorLiteral =
  forAll "tCont" type0 $ \tCont ->
    forAll "tElem" type0 $ \tElem ->
      forAllDim Relevant $ \d ->
        hasVecLits tCont tElem d
          ~~~> typeOfVecLiteralCast tCont tElem d

typeOfStackTensor :: (HasStandardBuiltins builtin) => DSLExpr builtin
typeOfStackTensor =
  forAllTypes $ \t ->
    forAllDim Relevant $ \d ->
      forAllDims $ \ds ->
        typeOfVecLiteralCast (tTensor t (dimCons d ds)) (tTensor t ds) d

typeOfFromVectorToList :: (HasStandardBuiltins builtin) => DSLExpr builtin
typeOfFromVectorToList =
  forAllTypes $ \t ->
    forAllDim Relevant $ \d ->
      typeOfVecLiteralCast (tList t) t d

typeOfNatInDomainConstraint :: (HasStandardBuiltins builtin) => DSLExpr builtin
typeOfNatInDomainConstraint = forAll "A" type0 $ \t -> tNat ~> t ~> type0

typeOfForeach :: (HasStandardBuiltins builtin) => DSLExpr builtin
typeOfForeach =
  forAll "A" type0 $ \tElem ->
    forAll "d" tDim $ \d ->
      forAllDims $ \ds ->
        (tIndex d ~> tTensor tElem ds) ~> tTensor tElem (dimCons d ds)
