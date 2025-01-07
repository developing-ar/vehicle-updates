module Vehicle.Data.Code.TypedView
  ( TypeValue (..),
    toTypeValue,
    IndexValue (..),
    toIndexValue,
    NatValue (..),
    toNatValue,
    fromNatValue,
    BoolTensorValue (..),
    toBoolValue,
    fromBoolValue,
    RatTensorValue (..),
    toRatTensorValue,
    fromRatTensorValue,
    DimensionsValue (..),
    toDimensionsValue,
  )
where

import GHC.Stack (HasCallStack)
import Vehicle.Compile.Print (prettyVerbose)
import Vehicle.Data.Builtin.Interface (Accessor (..))
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
  where
    IIndexType size = VBuiltin (BuiltinType IndexType) [Arg mempty Explicit Irrelevant size]

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
  VBoundVar v spine -> VIndexBoundVar v spine
  (getExpr accessIndexLiteral -> Just i) -> VIndexLiteral i
  (getExpr accessIf -> Just (argExpr -> IIndexType {}, c, x, y)) -> VIndexIf c x y
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
  VBoundVar v spine -> VNatBoundVar v spine
  VFreeVar ident [] -> VNatParameter ident
  (getExpr accessNatLiteral -> Just i) -> VNatLiteral i
  (getExpr accessIf -> Just (argExpr -> INatType {}, c, x, y)) -> VNatIf c x y
  (getExpr accessAddNat -> Just (x, y)) -> VNatAdd x y
  (getExpr accessMulNat -> Just (x, y)) -> VNatMul x y
  _ -> developerError "ill-typed Dimensions expression"

fromNatValue :: NatValue -> Value Builtin
fromNatValue = \case
  VNatBoundVar v spine -> VBoundVar v spine
  VNatParameter ident -> VFreeVar ident []
  VNatLiteral i -> mkExpr accessNatLiteral i
  VNatIf c x y -> mkExpr accessIf (implicit INatType, c, x, y)
  VNatAdd x y -> mkExpr accessAddNat (x, y)
  VNatMul x y -> mkExpr accessMulNat (x, y)

-------------------------------------------------------------------------------
-- Bool

-- | A view on all possible expressions that can have type `Tensor Bool`.
data BoolTensorValue
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
  | VReduceAndTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VReduceOrTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VBoolIf (Value Builtin) (Value Builtin) (Value Builtin) (Value Builtin)
  | VBoolAt (VArg Builtin) (VArg Builtin) (Value Builtin) (Value Builtin)
  | VBoolTensorLiteral (Tensor Bool)
  | VBoolStackTensor (VArg Builtin) (VArg Builtin) (Spine Builtin)
  | VBoolForeach (VArg Builtin) (VArg Builtin) (Value Builtin)

toBoolValue :: (HasCallStack) => Value Builtin -> BoolTensorValue
toBoolValue expr = case expr of
  (getExpr accessBoolTensorLiteral -> Just t) -> VBoolTensorLiteral t
  (getExpr accessAndTensor -> Just (dims, x, y)) -> VAnd dims x y
  (getExpr accessOrTensor -> Just (dims, x, y)) -> VOr dims x y
  (getExpr accessNotTensor -> Just (dims, x)) -> VNot dims x
  (getExpr accessOrderRatTensor -> Just (op, dims, x, y)) -> VOrderRatTensor op dims x y
  (getExpr accessOrderNat -> Just (op, x, y)) -> VOrderNat op x y
  (getExpr accessOrderIndex -> Just (op, n1, n2, x, y)) -> VOrderIndex op n1 n2 x y
  (getExpr accessEqRatTensor -> Just (op, dims, x, y)) -> VEqualsRatTensor op dims x y
  (getExpr accessEqNat -> Just (op, x, y)) -> VEqualsNat op x y
  (getExpr accessEqIndex -> Just (op, n1, n2, x, y)) -> VEqualsIndex op n1 n2 x y
  (getExpr accessQuantifyRatTensor -> Just (op, dims, argExpr -> VLam binder closure)) -> VQuantifyRatTensor op dims binder closure
  (getExpr accessReduceAnd -> Just (dims, e, x)) -> VReduceAndTensor dims e x
  (getExpr accessReduceOr -> Just (dims, e, x)) -> VReduceOrTensor dims e x
  (getExpr accessConstTensor -> Just (argExpr -> IBoolType, x, dims)) -> VConstBoolTensor x dims
  (getExpr accessStackTensor -> Just (d, ds, argExpr -> IBoolType, xs)) -> VBoolStackTensor d ds xs
  (getExpr accessAtTensor -> Just (argExpr -> IBoolType, d, ds, xs, i)) -> VBoolAt d ds xs i
  (getExpr accessForeachTensor -> Just (argExpr -> IBoolType, d, ds, fn)) -> VBoolForeach d ds fn
  (getExpr accessIf -> Just (argExpr -> IBoolTensorType dims, c, x, y)) -> VBoolIf dims c x y
  _ -> developerError $ "ill-typed RatTensor expression:" <+> prettyVerbose expr

fromBoolValue :: BoolTensorValue -> Value Builtin
fromBoolValue = \case
  VBoolTensorLiteral y -> mkExpr accessBoolTensorLiteral y
  VAnd dims x y -> mkExpr accessAndTensor (dims, x, y)
  VOr dims x y -> mkExpr accessOrTensor (dims, x, y)
  VNot dims x -> mkExpr accessNotTensor (dims, x)
  VOrderNat op x y -> mkExpr accessOrderNat (op, x, y)
  VOrderIndex op n1 n2 x y -> mkExpr accessOrderIndex (op, n1, n2, x, y)
  VOrderRatTensor op dims x y -> mkExpr accessOrderRatTensor (op, dims, x, y)
  VEqualsNat op x y -> mkExpr accessEqNat (op, x, y)
  VEqualsIndex op n1 n2 x y -> mkExpr accessEqIndex (op, n1, n2, x, y)
  VEqualsRatTensor op dims x y -> mkExpr accessEqRatTensor (op, dims, x, y)
  VQuantifyRatTensor q dims binder closure -> mkExpr accessQuantifyRatTensor (q, dims, VLam binder closure)
  VReduceAndTensor dims e x -> mkExpr accessReduceAnd (dims, e, x)
  VReduceOrTensor dims e x -> mkExpr accessReduceOr (dims, e, x)
  VBoolIf dims c x y -> mkExpr accessIf (boolTensorType dims, c, x, y)
  VConstBoolTensor x dims -> mkExpr accessConstTensor (boolType, x, dims)
  VBoolStackTensor d ds xs -> mkExpr accessStackTensor (d, ds, boolType, xs)
  VBoolAt d ds xs i -> mkExpr accessAtTensor (boolType, d, ds, xs, i)
  VBoolForeach d ds fn -> mkExpr accessForeachTensor (boolType, d, ds, fn)
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
  | VReduceAddRatTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VReduceMulRatTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VReduceMinRatTensor (VArg Builtin) (Value Builtin) (Value Builtin)
  | VReduceMaxRatTensor (VArg Builtin) (Value Builtin) (Value Builtin)
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
  (getExpr accessRatTensorLiteral -> Just t) -> VRatTensorLiteral t
  (getExpr accessNegRatTensor -> Just (dims, x)) -> VNegRatTensor dims x
  (getExpr accessAddRatTensor -> Just (dims, x, y)) -> VAddRatTensor dims x y
  (getExpr accessSubRatTensor -> Just (dims, x, y)) -> VSubRatTensor dims x y
  (getExpr accessMulRatTensor -> Just (dims, x, y)) -> VMulRatTensor dims x y
  (getExpr accessDivRatTensor -> Just (dims, x, y)) -> VDivRatTensor dims x y
  (getExpr accessMinRatTensor -> Just (dims, x, y)) -> VMinRatTensor dims x y
  (getExpr accessMaxRatTensor -> Just (dims, x, y)) -> VMaxRatTensor dims x y
  (getExpr accessReduceAddRat -> Just (dims, e, x)) -> VReduceAddRatTensor dims e x
  (getExpr accessReduceMulRat -> Just (dims, e, x)) -> VReduceMulRatTensor dims e x
  (getExpr accessReduceMinRat -> Just (dims, e, x)) -> VReduceMinRatTensor dims e x
  (getExpr accessReduceMaxRat -> Just (dims, e, x)) -> VReduceMaxRatTensor dims e x
  (getExpr accessIf -> Just (argExpr -> IRatTensorType dims, c, x, y)) -> VIfRatTensor dims c x y
  (getExpr accessConstTensor -> Just (argExpr -> IRatType, x, dims)) -> VRatConstTensor x dims
  (getExpr accessStackTensor -> Just (d, ds, argExpr -> IRatType, xs)) -> VRatStackTensor d ds xs
  (getExpr accessAtTensor -> Just (argExpr -> IRatType, d, ds, xs, i)) -> VRatAt d ds xs i
  (getExpr accessForeachTensor -> Just (argExpr -> IRatType, d, ds, fn)) -> VRatForeach d ds fn
  _ -> illTyped
  where
    illTyped = developerError $ "ill-typed RatTensor expression:" <+> prettyVerbose expr

fromRatTensorValue :: RatTensorValue -> Value Builtin
fromRatTensorValue = \case
  VRatTensorVar v -> VBoundVar v []
  VNetworkApp n xs -> VFreeVar n xs
  VRatTensorLiteral t -> mkExpr accessRatTensorLiteral t
  VNegRatTensor dims x -> mkExpr accessNegRatTensor (dims, x)
  VAddRatTensor dims x y -> mkExpr accessAddRatTensor (dims, x, y)
  VSubRatTensor dims x y -> mkExpr accessSubRatTensor (dims, x, y)
  VMulRatTensor dims x y -> mkExpr accessMulRatTensor (dims, x, y)
  VDivRatTensor dims x y -> mkExpr accessDivRatTensor (dims, x, y)
  VMinRatTensor dims x y -> mkExpr accessMinRatTensor (dims, x, y)
  VMaxRatTensor dims x y -> mkExpr accessMaxRatTensor (dims, x, y)
  VReduceAddRatTensor dims e x -> mkExpr accessReduceAddRat (dims, e, x)
  VReduceMulRatTensor dims e x -> mkExpr accessReduceMulRat (dims, e, x)
  VReduceMinRatTensor dims e x -> mkExpr accessReduceMinRat (dims, e, x)
  VReduceMaxRatTensor dims e x -> mkExpr accessReduceMaxRat (dims, e, x)
  VIfRatTensor dims c x y -> mkExpr accessIf (ratTensorType dims, c, x, y)
  VRatConstTensor x dims -> mkExpr accessConstTensor (ratElementType, x, dims)
  VRatStackTensor d ds xs -> mkExpr accessStackTensor (d, ds, ratElementType, xs)
  VRatAt d ds xs i -> mkExpr accessAtTensor (ratElementType, d, ds, xs, i)
  VRatForeach d ds fn -> mkExpr accessForeachTensor (ratElementType, d, ds, fn)
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
  VBoundVar lv spine -> VDimsBoundVar lv spine
  (getExpr accessNil -> Just (argExpr -> INatType)) -> VDimsNil
  (getExpr accessCons -> Just (argExpr -> INatType, x, xs)) -> VDimsCons (argExpr x) (argExpr xs)
  (getExpr accessIf -> Just (argExpr -> INatType, c, x, y)) -> VDimsIf c x y
  _ -> developerError "ill-typed Dimensions expression"
