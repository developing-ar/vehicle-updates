module Vehicle.Compile.Print.Builtin where

import Data.Maybe (isJust)
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Linearity (LinearityBuiltin (..))
import Vehicle.Data.Builtin.Loss (LossBuiltin (..), LossBuiltinConstructor, LossBuiltinFunction, LossBuiltinType)
import Vehicle.Data.Builtin.Loss qualified as L
import Vehicle.Data.Builtin.Polarity (PolarityBuiltin (..))
import Vehicle.Data.Code.Expr
  ( Arg,
    Expr (..),
    mapBuiltins,
    normAppList,
    pattern App,
  )
import Vehicle.Prelude

--------------------------------------------------------------------------------
-- Type classes

class ConvertableBuiltin builtin1 builtin2 where
  convertBuiltin :: Provenance -> builtin1 -> Expr builtin2

instance ConvertableBuiltin builtin builtin where
  convertBuiltin = Builtin

instance ConvertableBuiltin BuiltinType Builtin where
  convertBuiltin p = Builtin p . BuiltinType

instance ConvertableBuiltin TypeClassOp Builtin where
  convertBuiltin p = Builtin p . TypeClassOp

instance ConvertableBuiltin BuiltinConstructor Builtin where
  convertBuiltin p = Builtin p . BuiltinConstructor

instance ConvertableBuiltin BuiltinFunction Builtin where
  convertBuiltin p = Builtin p . BuiltinFunction

instance ConvertableBuiltin ComparisonOp Builtin where
  convertBuiltin p = convertBuiltin p . CompareTC

instance ConvertableBuiltin LossBuiltinType Builtin where
  convertBuiltin p =
    convertBuiltin p . \case
      L.UnitType -> UnitType
      L.IndexType -> IndexType
      L.NatType -> NatType
      L.RatType -> RatType
      L.ListType -> ListType
      L.TensorType -> TensorType

instance ConvertableBuiltin LossBuiltinConstructor Builtin where
  convertBuiltin p =
    convertBuiltin p . \case
      L.Nil -> Nil
      L.Cons -> Cons
      L.UnitLiteral -> UnitLiteral
      L.IndexLiteral x -> IndexLiteral x
      L.IndexTensorLiteral x -> IndexTensorLiteral x
      L.NatLiteral x -> NatLiteral x
      L.NatTensorLiteral x -> NatTensorLiteral x
      L.RatTensorLiteral x -> RatTensorLiteral x

instance ConvertableBuiltin LossBuiltinFunction Builtin where
  convertBuiltin p b = case b of
    L.Neg dom -> convertBuiltin p (L.Neg dom)
    L.Sub dom -> convertBuiltin p (L.Sub dom)
    L.Div dom -> convertBuiltin p (L.Div dom)
    L.Min dom -> convertBuiltin p (L.Min dom)
    L.Max dom -> convertBuiltin p (L.Max dom)
    L.Add dom -> convertBuiltin p (L.Add dom)
    L.Mul dom -> convertBuiltin p (L.Mul dom)
    L.PowRat -> convertBuiltin p PowRat
    L.ReduceAddRatTensor -> convertBuiltin p ReduceAddRatTensor
    L.ReduceMulRatTensor -> convertBuiltin p ReduceMulRatTensor
    L.ReduceMinRatTensor -> convertBuiltin p ReduceMinRatTensor
    L.ReduceMaxRatTensor -> convertBuiltin p ReduceMaxRatTensor
    L.At -> convertBuiltin p At
    L.StackTensor -> convertBuiltin p StackTensor
    L.ConstTensor -> convertBuiltin p ConstTensor
    L.SearchRatTensor -> cheatConvertBuiltin p $ pretty b
    L.MapList -> convertBuiltin p MapList
    L.FoldList -> convertBuiltin p FoldList

instance ConvertableBuiltin PolarityBuiltin Builtin where
  convertBuiltin p = \case
    PolarityConstructor c -> convertBuiltin p c
    PolarityFunction f -> convertBuiltin p f
    b -> cheatConvertBuiltin p $ pretty b

instance ConvertableBuiltin LinearityBuiltin Builtin where
  convertBuiltin p = \case
    LinearityConstructor c -> convertBuiltin p c
    LinearityFunction f -> convertBuiltin p f
    b -> cheatConvertBuiltin p $ pretty b

instance ConvertableBuiltin LossBuiltin Builtin where
  convertBuiltin p b = case b of
    LossBuiltinType op -> convertBuiltin p op
    LossBuiltinConstructor op -> convertBuiltin p op
    LossBuiltinFunction op -> convertBuiltin p op

convertExprBuiltins ::
  forall builtin1 builtin2.
  (ConvertableBuiltin builtin1 builtin2) =>
  Expr builtin1 ->
  Expr builtin2
convertExprBuiltins = mapBuiltins $ \p b args ->
  normAppList (convertBuiltin p b) args

-- | Use to convert builtins for printing that have no representation in the
-- standard `Builtin` type.
cheatConvertBuiltin :: Provenance -> Doc a -> Expr builtin
cheatConvertBuiltin p b = FreeVar p $ stdlibIdentifier $ layoutAsText b

--------------------------------------------------------------------------------
-- Printable builtins

class (Show builtin, Pretty builtin, ConvertableBuiltin builtin Builtin) => PrintableBuiltin builtin where
  -- | Convert expressions with the builtin back to expressions with the standard
  -- builtin type. Used for printing.
  coercionArgs :: builtin -> Maybe ([Arg builtin] -> Expr builtin)

  getBuiltinTypeClassOp :: builtin -> Maybe TypeClassOp

  isTypeClassOp :: builtin -> Bool
  isTypeClassOp b = case getBuiltinTypeClassOp b of
    Just {} -> True
    Nothing -> False

instance PrintableBuiltin Builtin where
  coercionArgs b = case b of
    BuiltinFunction FromNat {} -> Just $ \args -> argExpr $ last args
    BuiltinFunction FromRat {} -> Just $ \args -> argExpr $ last args
    TypeClassOp FromNatTC {} -> Just $ \args -> argExpr $ last args
    TypeClassOp FromRatTC {} -> Just $ \args -> argExpr $ last args
    TypeClassOp VecLiteralTC {} -> Just $ \args -> normAppList (Builtin mempty b) args
    _ -> Nothing

  getBuiltinTypeClassOp = \case
    TypeClassOp op -> Just op
    _ -> Nothing

instance PrintableBuiltin PolarityBuiltin where
  coercionArgs _ = Nothing

  getBuiltinTypeClassOp = const Nothing

instance PrintableBuiltin LinearityBuiltin where
  coercionArgs _ = Nothing

  getBuiltinTypeClassOp = const Nothing

instance PrintableBuiltin LossBuiltin where
  coercionArgs _ = Nothing

  getBuiltinTypeClassOp = const Nothing

isCoercionExpr :: (PrintableBuiltin builtin) => Expr builtin -> Bool
isCoercionExpr = \case
  Builtin _ b -> isJust $ coercionArgs b
  App (Builtin _ b) _ -> isJust $ coercionArgs b
  _ -> False
