module Vehicle.Data.Code.TypedView where

import GHC.Stack (HasCallStack)
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.Value
import Vehicle.Data.DeBruijn
import Vehicle.Data.Tensor (Tensor)
import Vehicle.Prelude

-------------------------------------------------------------------------------
-- Types

-- Private type synonyms. These should only be used in this file.
-- Use `toValueType` instead outside of this file.

pattern INullaryTypeExpr :: BuiltinType -> Value Builtin
pattern INullaryTypeExpr t <- VBuiltin (BuiltinType t) []
  where
    INullaryTypeExpr t = VBuiltin (BuiltinType t) []

pattern IRatType :: Value Builtin
pattern IRatType = INullaryTypeExpr RatType

pattern IBoolType :: Value Builtin
pattern IBoolType = INullaryTypeExpr BoolType

pattern IIndexType :: Value Builtin -> Value Builtin
pattern IIndexType size <- VBuiltin (BuiltinType IndexType) [argExpr -> size]

pattern INatType :: Value Builtin
pattern INatType = INullaryTypeExpr NatType

pattern ITensorType :: Value Builtin -> Value Builtin -> Value Builtin
pattern ITensorType t dims <- VBuiltin (BuiltinType TensorType) [argExpr -> t, argExpr -> dims]
  where
    ITensorType t dims = VBuiltin (BuiltinType TensorType) [explicit t, Arg mempty Explicit Irrelevant dims]

pattern IBoolTensorType :: Value Builtin -> Value Builtin
pattern IBoolTensorType dims = ITensorType IBoolType dims

pattern IRatTensorType :: Value Builtin -> Value Builtin
pattern IRatTensorType dims = ITensorType IRatType dims

-- | A view on all possible expressions that can have type `List Int`.
data TypeValue
  = VUnitType
  | VBoolType
  | VIndexType (Value Builtin)
  | VNatType
  | VRatType
  | VBoolTensorType (Value Builtin)
  | VNatTensorType (Value Builtin)
  | VRatTensorType (Value Builtin)
  | VIndexTensorType (Value Builtin) (Value Builtin)
  | VListType (Value Builtin)
  | VPiType (VBinder Builtin) (Closure Builtin)
  | VBoundTypeVar Lv (Spine Builtin)

toTypeValue :: (HasCallStack) => Value Builtin -> TypeValue
toTypeValue t = case t of
  VPi binder value -> VPiType binder value
  VBoundVar lv spine -> VBoundTypeVar lv spine
  VBuiltin (BuiltinType typ) spine -> case (typ, spine) of
    (UnitType, []) -> VUnitType
    (BoolType, []) -> VBoolType
    (RatType, []) -> VRatType
    (IndexType, [n]) -> VIndexType (argExpr n)
    (NatType, []) -> VNatType
    (ListType, [tElem]) -> VListType (argExpr tElem)
    (TensorType, [toTypeValue . argExpr -> VBoolType, ds]) -> VBoolTensorType (argExpr ds)
    (TensorType, [toTypeValue . argExpr -> VRatType, ds]) -> VRatTensorType (argExpr ds)
    (TensorType, [toTypeValue . argExpr -> VNatType, ds]) -> VNatTensorType (argExpr ds)
    (TensorType, [toTypeValue . argExpr -> VIndexType n, ds]) -> VIndexTensorType n (argExpr ds)
    _ -> err
  _ -> err
  where
    err = developerError $ "ill-typed type" <+> prettyVerbose t

-------------------------------------------------------------------------------
-- Index

-- | A view on all possible expressions that can have type `Index n`.
data IndexValue
  = VIndexLiteral Int
  | VIndexBoundVar Lv (Spine Builtin)
  | VIndexIf (Value Builtin) (Value Builtin) (Value Builtin)

toIndexValue :: (HasCallStack) => Value Builtin -> IndexValue
toIndexValue = \case
  IIndexLiteral i -> VIndexLiteral i
  VBoundVar v spine -> VIndexBoundVar v spine
  VBuiltin (BuiltinFunction If) [argExpr -> IIndexType {}, c, x, y] -> VIndexIf (argExpr c) (argExpr x) (argExpr y)
  _ -> developerError "ill-typed Dimensions expression"

-------------------------------------------------------------------------------
-- Nat

-- | A view on all possible expressions that can have type `Nat`.
data NatValue
  = VNatLiteral Int
  | VNatBoundVar Lv (Spine Builtin)
  | VNatIf (Value Builtin) (Value Builtin) (Value Builtin)
  | VNatAdd (Value Builtin) (Value Builtin)
  | VNatMul (Value Builtin) (Value Builtin)
  | VNatParameter Identifier

toNatValue :: (HasCallStack) => Value Builtin -> NatValue
toNatValue = \case
  INatLiteral i -> VNatLiteral i
  VBoundVar v spine -> VNatBoundVar v spine
  VFreeVar ident [] -> VNatParameter ident
  VBuiltin (BuiltinFunction If) [argExpr -> INatType {}, c, x, y] -> VNatIf (argExpr c) (argExpr x) (argExpr y)
  VBuiltin (BuiltinFunction (Add AddNat)) [x, y] -> VNatAdd (argExpr x) (argExpr y)
  VBuiltin (BuiltinFunction (Mul MulNat)) [x, y] -> VNatMul (argExpr x) (argExpr y)
  _ -> developerError "ill-typed Dimensions expression"

fromNatValue :: NatValue -> Value Builtin
fromNatValue = \case
  VNatLiteral i -> INatLiteral i
  VNatBoundVar v spine -> VBoundVar v spine
  VNatParameter ident -> VFreeVar ident []
  VNatIf c x y -> VBuiltin (BuiltinFunction If) [implicit INatType, explicit c, explicit x, explicit y]
  VNatAdd x y -> VBuiltin (BuiltinFunction (Add AddNat)) [explicit x, explicit y]
  VNatMul x y -> VBuiltin (BuiltinFunction (Mul MulNat)) [explicit x, explicit y]

-------------------------------------------------------------------------------
-- Bool

-- | A view on all possible expressions that can have type `Tensor Bool`.
data BooleanTensorValue
  = VConstBoolTensor (Value Builtin) (Value Builtin)
  | VAnd (VArg Builtin) (Value Builtin) (Value Builtin)
  | VOr (VArg Builtin) (Value Builtin) (Value Builtin)
  | VNot (VArg Builtin) (Value Builtin)
  | VOrderIndex OrderOp (VArg Builtin) (VArg Builtin) (Value Builtin) (Value Builtin)
  | VOrderNat OrderOp (Value Builtin) (Value Builtin)
  | VOrderRatTensor OrderOp (VArg Builtin) (Value Builtin) (Value Builtin)
  | VEqualsIndex EqualityOp (VArg Builtin) (VArg Builtin) (Value Builtin) (Value Builtin)
  | VEqualsNat EqualityOp (Value Builtin) (Value Builtin)
  | VEqualsRatTensor EqualityOp (VArg Builtin) (Value Builtin) (Value Builtin)
  | VQuantifyRatTensor Quantifier (VArg Builtin) (VBinder Builtin) (Closure Builtin)
  | VReduceAndTensor (VArg Builtin) (Value Builtin)
  | VReduceOrTensor (VArg Builtin) (Value Builtin)
  | VBoolIf (Value Builtin) (Value Builtin) (Value Builtin) (Value Builtin)
  | VBoolAt (VArg Builtin) (VArg Builtin) (Value Builtin) (Value Builtin)
  | VBoolTensorLiteral (Tensor Bool)
  | VBoolStackTensor (VArg Builtin) (VArg Builtin) (Spine Builtin)
  | VBoolForeach (VArg Builtin) (VArg Builtin) (Value Builtin)

toBoolValue :: (HasCallStack) => Value Builtin -> BooleanTensorValue
toBoolValue (VBuiltin b args) = case b of
  BuiltinConstructor c -> case (c, args) of
    (BoolTensorLiteral t, []) -> VBoolTensorLiteral t
    _ -> developerError "ill-typed BoolTensor expression"
  BuiltinFunction f -> case (f, args) of
    (And, [dims, x, y]) -> VAnd dims (argExpr x) (argExpr y)
    (Or, [dims, x, y]) -> VOr dims (argExpr x) (argExpr y)
    (Not, [dims, x]) -> VNot dims (argExpr x)
    (Order OrderRatTensor op, [dims, x, y]) -> VOrderRatTensor op dims (argExpr x) (argExpr y)
    (Order OrderNat op, [x, y]) -> VOrderNat op (argExpr x) (argExpr y)
    (Order OrderIndex op, [n1, n2, x, y]) -> VOrderIndex op n1 n2 (argExpr x) (argExpr y)
    (Equals EqRatTensor op, [dims, x, y]) -> VEqualsRatTensor op dims (argExpr x) (argExpr y)
    (Equals EqNat op, [x, y]) -> VEqualsNat op (argExpr x) (argExpr y)
    (Equals EqIndex op, [n1, n2, x, y]) -> VEqualsIndex op n1 n2 (argExpr x) (argExpr y)
    (QuantifyRatTensor op, [dims, argExpr -> VLam binder closure]) -> VQuantifyRatTensor op dims binder closure
    (ReduceAndTensor, [dims, x]) -> VReduceAndTensor dims (argExpr x)
    (ReduceOrTensor, [dims, x]) -> VReduceOrTensor dims (argExpr x)
    (ConstTensor, [argExpr -> IBoolType, x, dims]) -> VConstBoolTensor (argExpr x) (argExpr dims)
    (StackTensor, d : ds : (argExpr -> IBoolType) : xs) -> VBoolStackTensor d ds xs
    (At, [argExpr -> IBoolType, d, ds, argExpr -> xs, argExpr -> i]) -> VBoolAt d ds xs i
    (Foreach, [argExpr -> IBoolType, d, ds, argExpr -> fn]) -> VBoolForeach d ds fn
    (If, [argExpr -> IBoolTensorType dims, c, x, y]) -> VBoolIf dims (argExpr c) (argExpr x) (argExpr y)
    _ -> developerError "ill-typed BoolTensor expression"
  _ -> developerError "ill-typed BoolTensor expression"
toBoolValue _ = developerError "ill-typed BoolTensor expression"

fromBoolValue :: BooleanTensorValue -> Value Builtin
fromBoolValue = \case
  VBoolTensorLiteral y -> VBuiltin (BuiltinConstructor $ BoolTensorLiteral y) []
  VAnd dims x y -> VBuiltin (BuiltinFunction And) [dims, explicit x, explicit y]
  VOr dims x y -> VBuiltin (BuiltinFunction Or) [dims, explicit x, explicit y]
  VNot dims x -> VBuiltin (BuiltinFunction Not) [dims, explicit x]
  VOrderNat op x y -> VBuiltin (BuiltinFunction $ Order OrderNat op) [explicit x, explicit y]
  VOrderIndex op n1 n2 x y -> VBuiltin (BuiltinFunction $ Order OrderIndex op) [n1, n2, explicit x, explicit y]
  VOrderRatTensor op dims x y -> VBuiltin (BuiltinFunction $ Order OrderRatTensor op) [dims, explicit x, explicit y]
  VEqualsNat op x y -> VBuiltin (BuiltinFunction $ Equals EqNat op) [explicit x, explicit y]
  VEqualsIndex op n1 n2 x y -> VBuiltin (BuiltinFunction $ Equals EqIndex op) [n1, n2, explicit x, explicit y]
  VEqualsRatTensor op dims x y -> VBuiltin (BuiltinFunction $ Equals EqRatTensor op) [dims, explicit x, explicit y]
  VQuantifyRatTensor q dims binder closure -> VBuiltin (BuiltinFunction $ QuantifyRatTensor q) [dims, explicit (VLam binder closure)]
  VReduceAndTensor dims x -> VBuiltin (BuiltinFunction ReduceAndTensor) [dims, explicit x]
  VReduceOrTensor dims x -> VBuiltin (BuiltinFunction ReduceOrTensor) [dims, explicit x]
  VBoolIf dims c x y -> VBuiltin (BuiltinFunction If) [boolTensorType dims, explicit c, explicit x, explicit y]
  VConstBoolTensor x dims -> VBuiltin (BuiltinFunction ConstTensor) [boolType, explicit x, explicit dims]
  VBoolStackTensor d ds xs -> VBuiltin (BuiltinFunction StackTensor) (d : ds : boolType : xs)
  VBoolAt d ds xs i -> VBuiltin (BuiltinFunction At) [boolType, d, ds, explicit xs, explicit i]
  VBoolForeach d ds fn -> VBuiltin (BuiltinFunction Foreach) [boolType, d, ds, explicit fn]
  where
    boolTensorType ds = implicit (IBoolTensorType ds)
    boolType = implicit IBoolType

-------------------------------------------------------------------------------
-- Tensor Rat

-- | A view on all possible expressions that can have type `Tensor Rat`.
data RatTensorValue
  = VRatTensorLiteral (Tensor Rational)
  | VNegRatTensor (VArg Builtin) (Value Builtin)
  | VAddRatTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VSubRatTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VMulRatTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VDivRatTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VMinRatTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VMaxRatTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VReduceAddRatTensor (VArg Builtin) (Value Builtin)
  | VReduceMulRatTensor (VArg Builtin) (Value Builtin)
  | VReduceMinRatTensor (VArg Builtin) (Value Builtin)
  | VReduceMaxRatTensor (VArg Builtin) (Value Builtin)
  | VIfRatTensor (Value Builtin) (Value Builtin) (Value Builtin) (Value Builtin)
  | VRatTensorVar Lv
  | VNetworkApp Identifier (Spine Builtin)
  | VRatConstTensor (Value Builtin) (Value Builtin)
  | VRatStackTensor (VArg Builtin) (VArg Builtin) (Spine Builtin)
  | VRatAt (VArg Builtin) (VArg Builtin) (Value Builtin) (Value Builtin)
  | VRatForeach (VArg Builtin) (VArg Builtin) (Value Builtin)

toRatTensorValue :: (HasCallStack) => Value Builtin -> RatTensorValue
toRatTensorValue expr = case expr of
  VBoundVar lv [] -> VRatTensorVar lv
  VFreeVar n spine -> VNetworkApp n spine
  VBuiltin b args -> case b of
    BuiltinConstructor c -> case (c, args) of
      (RatTensorLiteral t, []) -> VRatTensorLiteral t
      _ -> illTyped
    BuiltinFunction f -> case (f, args) of
      (Neg NegRatTensor, [dims, x]) -> VNegRatTensor dims (argExpr x)
      (Add AddRatTensor, [dims, x, y]) -> VAddRatTensor dims (argExpr x) (argExpr y)
      (Sub SubRatTensor, [dims, x, y]) -> VSubRatTensor dims (argExpr x) (argExpr y)
      (Mul MulRatTensor, [dims, x, y]) -> VMulRatTensor dims (argExpr x) (argExpr y)
      (Div DivRatTensor, [dims, x, y]) -> VDivRatTensor dims (argExpr x) (argExpr y)
      (Min MinRatTensor, [dims, x, y]) -> VMinRatTensor dims (argExpr x) (argExpr y)
      (Max MaxRatTensor, [dims, x, y]) -> VMaxRatTensor dims (argExpr x) (argExpr y)
      (ReduceAddRatTensor, [dims, x]) -> VReduceAddRatTensor dims (argExpr x)
      (ReduceMulRatTensor, [dims, x]) -> VReduceMulRatTensor dims (argExpr x)
      (ReduceMinRatTensor, [dims, x]) -> VReduceMinRatTensor dims (argExpr x)
      (ReduceMaxRatTensor, [dims, x]) -> VReduceMaxRatTensor dims (argExpr x)
      (If, [argExpr -> IRatTensorType dims, c, x, y]) -> VIfRatTensor dims (argExpr c) (argExpr x) (argExpr y)
      (ConstTensor, [argExpr -> IRatType, x, dims]) -> VRatConstTensor (argExpr x) (argExpr dims)
      (StackTensor, d : ds : (argExpr -> IRatType) : xs) -> VRatStackTensor d ds xs
      (At, [argExpr -> IRatType, d, ds, argExpr -> xs, argExpr -> i]) -> VRatAt d ds xs i
      (Foreach, [argExpr -> IRatType, d, ds, argExpr -> fn]) -> VRatForeach d ds fn
      _ -> illTyped
    _ -> illTyped
  _ -> illTyped
  where
    illTyped = developerError $ "ill-typed RatTensor expression:" <+> prettyVerbose expr

fromRatTensorValue :: RatTensorValue -> Value Builtin
fromRatTensorValue = \case
  VRatTensorLiteral t -> VBuiltin (BuiltinConstructor $ RatTensorLiteral t) []
  VNegRatTensor dims x -> VBuiltin (BuiltinFunction $ Neg NegRatTensor) [dims, explicit x]
  VAddRatTensor dims x y -> VBuiltin (BuiltinFunction $ Add AddRatTensor) [dims, explicit x, explicit y]
  VSubRatTensor dims x y -> VBuiltin (BuiltinFunction $ Sub SubRatTensor) [dims, explicit x, explicit y]
  VMulRatTensor dims x y -> VBuiltin (BuiltinFunction $ Mul MulRatTensor) [dims, explicit x, explicit y]
  VDivRatTensor dims x y -> VBuiltin (BuiltinFunction $ Div DivRatTensor) [dims, explicit x, explicit y]
  VMinRatTensor dims x y -> VBuiltin (BuiltinFunction $ Min MinRatTensor) [dims, explicit x, explicit y]
  VMaxRatTensor dims x y -> VBuiltin (BuiltinFunction $ Max MaxRatTensor) [dims, explicit x, explicit y]
  VReduceAddRatTensor dims x -> VBuiltin (BuiltinFunction ReduceAddRatTensor) [dims, explicit x]
  VReduceMulRatTensor dims x -> VBuiltin (BuiltinFunction ReduceMulRatTensor) [dims, explicit x]
  VReduceMinRatTensor dims x -> VBuiltin (BuiltinFunction ReduceMinRatTensor) [dims, explicit x]
  VReduceMaxRatTensor dims x -> VBuiltin (BuiltinFunction ReduceMaxRatTensor) [dims, explicit x]
  VRatTensorVar v -> VBoundVar v []
  VIfRatTensor dims c x y -> VBuiltin (BuiltinFunction If) [ratTensorType dims, explicit c, explicit x, explicit y]
  VNetworkApp n xs -> VFreeVar n xs
  VRatConstTensor x dims -> VBuiltin (BuiltinFunction ConstTensor) [ratElementType, explicit x, explicit dims]
  VRatStackTensor d ds xs -> VBuiltin (BuiltinFunction StackTensor) (d : ds : ratElementType : xs)
  VRatAt d ds xs i -> VBuiltin (BuiltinFunction At) [ratElementType, d, ds, explicit xs, explicit i]
  VRatForeach d ds fn -> VBuiltin (BuiltinFunction Foreach) [ratElementType, d, ds, explicit fn]
  where
    ratTensorType ds = implicit (IRatTensorType ds)
    ratElementType = implicit IRatType

-------------------------------------------------------------------------------
-- Dim

-- | A view on all possible expressions that can have type `List Int`.
data DimensionsValue
  = VDimsNil
  | VDimsCons (Value Builtin) (Value Builtin)
  | VDimsBoundVar Lv (Spine Builtin)
  | VDimsIf (Value Builtin) (Value Builtin) (Value Builtin)

toDimensionsValue :: Value Builtin -> DimensionsValue
toDimensionsValue = \case
  INil (argExpr -> INatType) -> VDimsNil
  ICons (argExpr -> INatType) x xs -> VDimsCons (argExpr x) (argExpr xs)
  VBoundVar lv spine -> VDimsBoundVar lv spine
  VBuiltin (BuiltinFunction If) [_, c, x, y] -> VDimsIf (argExpr c) (argExpr x) (argExpr y)
  _ -> developerError "ill-typed Dimensions expression"
