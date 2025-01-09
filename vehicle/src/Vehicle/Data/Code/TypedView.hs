module Vehicle.Data.Code.TypedView
  ( TypeValue (..),
    toTypeValue,
    fromTypeValue,
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

fromTypeValue :: (HasCallStack) => TypeValue -> Value Builtin
fromTypeValue t = case t of
  VPiType binder value -> VPi binder value
  VBoundTypeVar lv spine -> VBoundVar lv spine
  VUnitType -> VBuiltin (BuiltinType UnitType) []
  VBoolType -> VBuiltin (BuiltinType BoolType) []
  VRatType -> VBuiltin (BuiltinType RatType) []
  VIndexType n -> VBuiltin (BuiltinType IndexType) [explicitIrrelevant n]
  VNatType -> VBuiltin (BuiltinType NatType) []
  VListType tElem -> VBuiltin (BuiltinType ListType) [explicit tElem]
  VBoolTensorType ds -> VBuiltin (BuiltinType TensorType) [explicit (fromTypeValue VBoolType), explicitIrrelevant ds]
  VRatTensorType ds -> VBuiltin (BuiltinType TensorType) [explicit (fromTypeValue VRatType), explicitIrrelevant ds]
  VNatTensorType ds -> VBuiltin (BuiltinType TensorType) [explicit (fromTypeValue VNatType), explicitIrrelevant ds]
  VIndexTensorType n ds -> VBuiltin (BuiltinType TensorType) [explicit (fromTypeValue (VIndexType n)), explicitIrrelevant ds]

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
toNatValue expr = case expr of
  VBoundVar v spine -> VNatBoundVar v spine
  VFreeVar ident [] -> VNatParameter ident
  (getExpr accessNatLiteral -> Just i) -> VNatLiteral i
  (getExpr accessIf -> Just (argExpr -> INatType {}, c, x, y)) -> VNatIf c x y
  (getExpr accessAddNat -> Just (x, y)) -> VNatAdd x y
  (getExpr accessMulNat -> Just (x, y)) -> VNatMul x y
  _ -> developerError $ "ill-typed Nat expression:" <+> prettyVerbose expr

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
  | VNot (TensorOp1Args (Value Builtin))
  | VAnd (TensorOp2Args (Value Builtin))
  | VOr (TensorOp2Args (Value Builtin))
  | VOrderIndex (OrderOp, IndexComparisonArgs (Value Builtin))
  | VOrderNat (OrderOp, NatOp2Args (Value Builtin))
  | VOrderRatTensor (OrderOp, TensorOp2Args (Value Builtin))
  | VEqualsIndex (EqualityOp, IndexComparisonArgs (Value Builtin))
  | VEqualsNat (EqualityOp, NatOp2Args (Value Builtin))
  | VEqualsRatTensor (EqualityOp, TensorOp2Args (Value Builtin))
  | VReduceAndTensor (TensorOp2Args (Value Builtin))
  | VReduceOrTensor (TensorOp2Args (Value Builtin))
  | VQuantifyRatTensor Quantifier (VArg Builtin) (VBinder Builtin) (Closure Builtin)
  | VBoolIf (Value Builtin) (Value Builtin) (Value Builtin) (Value Builtin)
  | VBoolAt (VArg Builtin) (VArg Builtin) (Value Builtin) (Value Builtin)
  | VBoolTensorLiteral (Tensor Bool)
  | VBoolStackTensor (VArg Builtin) (VArg Builtin) (Spine Builtin)
  | VBoolForeach (VArg Builtin) (VArg Builtin) (Value Builtin)

toBoolValue :: (HasCallStack) => Value Builtin -> BoolTensorValue
toBoolValue expr = case expr of
  (getExpr accessBoolTensorLiteral -> Just t) -> VBoolTensorLiteral t
  (getExpr accessAndTensor -> Just args) -> VAnd args
  (getExpr accessOrTensor -> Just args) -> VOr args
  (getExpr accessNotTensor -> Just args) -> VNot args
  (getExpr accessOrderRatTensor -> Just args) -> VOrderRatTensor args
  (getExpr accessOrderNat -> Just args) -> VOrderNat args
  (getExpr accessOrderIndex -> Just args) -> VOrderIndex args
  (getExpr accessEqRatTensor -> Just args) -> VEqualsRatTensor args
  (getExpr accessEqNat -> Just args) -> VEqualsNat args
  (getExpr accessEqIndex -> Just args) -> VEqualsIndex args
  (getExpr accessQuantifyRatTensor -> Just (op, dims, VLam binder closure)) -> VQuantifyRatTensor op dims binder closure
  (getExpr accessReduceAnd -> Just args) -> VReduceAndTensor args
  (getExpr accessReduceOr -> Just args) -> VReduceOrTensor args
  (getExpr accessConstTensor -> Just (argExpr -> IBoolType, x, dims)) -> VConstBoolTensor x dims
  (getExpr accessStackTensor -> Just (d, ds, argExpr -> IBoolType, xs)) -> VBoolStackTensor d ds xs
  (getExpr accessAtTensor -> Just (argExpr -> IBoolType, d, ds, xs, i)) -> VBoolAt d ds xs i
  (getExpr accessForeachTensor -> Just (argExpr -> IBoolType, d, ds, fn)) -> VBoolForeach d ds fn
  (getExpr accessIf -> Just (argExpr -> IBoolTensorType dims, c, x, y)) -> VBoolIf dims c x y
  _ -> developerError $ "ill-typed RatTensor expression:" <+> prettyVerbose expr

fromBoolValue :: BoolTensorValue -> Value Builtin
fromBoolValue = \case
  VBoolTensorLiteral y -> mkExpr accessBoolTensorLiteral y
  VAnd args -> mkExpr accessAndTensor args
  VOr args -> mkExpr accessOrTensor args
  VNot args -> mkExpr accessNotTensor args
  VOrderNat args -> mkExpr accessOrderNat args
  VOrderIndex args -> mkExpr accessOrderIndex args
  VOrderRatTensor args -> mkExpr accessOrderRatTensor args
  VEqualsNat args -> mkExpr accessEqNat args
  VEqualsIndex args -> mkExpr accessEqIndex args
  VEqualsRatTensor args -> mkExpr accessEqRatTensor args
  VQuantifyRatTensor q dims binder closure -> mkExpr accessQuantifyRatTensor (q, dims, VLam binder closure)
  VReduceAndTensor args -> mkExpr accessReduceAnd args
  VReduceOrTensor args -> mkExpr accessReduceOr args
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
  | VNegRatTensor (TensorOp1Args (Value Builtin))
  | VAddRatTensor (TensorOp2Args (Value Builtin))
  | VSubRatTensor (TensorOp2Args (Value Builtin))
  | VMulRatTensor (TensorOp2Args (Value Builtin))
  | VDivRatTensor (TensorOp2Args (Value Builtin))
  | VMinRatTensor (TensorOp2Args (Value Builtin))
  | VMaxRatTensor (TensorOp2Args (Value Builtin))
  | VReduceAddRatTensor (TensorOp2Args (Value Builtin))
  | VReduceMulRatTensor (TensorOp2Args (Value Builtin))
  | VReduceMinRatTensor (TensorOp2Args (Value Builtin))
  | VReduceMaxRatTensor (TensorOp2Args (Value Builtin))
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
  (getExpr accessNegRatTensor -> Just args) -> VNegRatTensor args
  (getExpr accessAddRatTensor -> Just args) -> VAddRatTensor args
  (getExpr accessSubRatTensor -> Just args) -> VSubRatTensor args
  (getExpr accessMulRatTensor -> Just args) -> VMulRatTensor args
  (getExpr accessDivRatTensor -> Just args) -> VDivRatTensor args
  (getExpr accessMinRatTensor -> Just args) -> VMinRatTensor args
  (getExpr accessMaxRatTensor -> Just args) -> VMaxRatTensor args
  (getExpr accessReduceAddRat -> Just args) -> VReduceAddRatTensor args
  (getExpr accessReduceMulRat -> Just args) -> VReduceMulRatTensor args
  (getExpr accessReduceMinRat -> Just args) -> VReduceMinRatTensor args
  (getExpr accessReduceMaxRat -> Just args) -> VReduceMaxRatTensor args
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
  VNegRatTensor args -> mkExpr accessNegRatTensor args
  VAddRatTensor args -> mkExpr accessAddRatTensor args
  VSubRatTensor args -> mkExpr accessSubRatTensor args
  VMulRatTensor args -> mkExpr accessMulRatTensor args
  VDivRatTensor args -> mkExpr accessDivRatTensor args
  VMinRatTensor args -> mkExpr accessMinRatTensor args
  VMaxRatTensor args -> mkExpr accessMaxRatTensor args
  VReduceAddRatTensor args -> mkExpr accessReduceAddRat args
  VReduceMulRatTensor args -> mkExpr accessReduceMulRat args
  VReduceMinRatTensor args -> mkExpr accessReduceMinRat args
  VReduceMaxRatTensor args -> mkExpr accessReduceMaxRat args
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
  (getExpr accessCons -> Just (argExpr -> INatType, x, xs)) -> VDimsCons x xs
  (getExpr accessIf -> Just (argExpr -> INatType, c, x, y)) -> VDimsIf c x y
  _ -> developerError "ill-typed Dimensions expression"
