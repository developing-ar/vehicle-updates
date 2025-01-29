module Vehicle.Data.Builtin.Decidable
  ( module Vehicle.Data.Builtin.Decidable,
    module Vehicle.Syntax.Builtin.BasicOperations,
  )
where

import GHC.Generics (Generic)
import Vehicle.Data.Builtin.Standard (BuiltinConstructor, BuiltinFunction (..), BuiltinType)
import Vehicle.Data.Tensor (BoolTensor)
import Vehicle.Prelude (Pretty (..), (<+>))
import Vehicle.Syntax.Builtin.BasicOperations

--------------------------------------------------------------------------------
-- Data

data DecidableBuiltinType
  = DecBool
  | HasNot
  | HasAnd
  | HasOr
  | HasImplies
  | HasCompare ComparisonDomain ComparisonOp
  | HasReduceAndTensor
  | HasReduceOrTensor
  deriving (Eq, Ord, Show)

-- | Constructors for types in the language. The types and type-classes
-- are viewed as constructors for `Type`.
data DecidableBuiltinFunction
  = DecNot
  | DecAnd
  | DecOr
  | DecImplies
  | DecCompare ComparisonDomain ComparisonOp
  | DecReduceAndTensor
  | DecReduceOrTensor
  deriving (Eq, Ord, Show)

newtype DecidableBuiltinConstructor
  = DecBoolTensor BoolTensor
  deriving (Eq, Show, Ord)

-- | The builtin types after translation to loss functions (missing all builtins
-- that involve the Bool type).
data DecidableBuiltin
  = StandardBuiltinType BuiltinType
  | StandardBuiltinFunction BuiltinFunction
  | StandardBuiltinConstructor BuiltinConstructor
  | DecidableBuiltinFunction DecidableBuiltinFunction
  | DecidableBuiltinType DecidableBuiltinType
  | DecidableBuiltinConstructor DecidableBuiltinConstructor
  deriving (Show, Eq, Generic)

--------------------------------------------------------------------------------
-- Accessors

{-
typeAccessor :: LossBuiltinType -> Accessor LossBuiltin ()
typeAccessor b =
  Access
    { getExpr = \case
        LossBuiltinType b1 | b == b1 -> Just ()
        _ -> Nothing,
      mkExpr = \() -> LossBuiltinType b
    }

functionAccessor :: LossBuiltinFunction -> Accessor LossBuiltin ()
functionAccessor b =
  Access
    { getExpr = \case
        LossBuiltinFunction b1 | b == b1 -> Just ()
        _ -> Nothing,
      mkExpr = \() -> LossBuiltinFunction b
    }

instance BuiltinHasIndexLiterals LossBuiltin where
  accessIndexLitBuiltin =
    Access
      { getExpr = \case
          LossBuiltinConstructor (IndexLiteral n) -> Just n
          _ -> Nothing,
        mkExpr = LossBuiltinConstructor . IndexLiteral
      }

  accessIndexTensorLitBuiltin =
    Access
      { getExpr = \case
          LossBuiltinConstructor (IndexTensorLiteral b) -> Just b
          _ -> Nothing,
        mkExpr = LossBuiltinConstructor . IndexTensorLiteral
      }

instance BuiltinHasNatType LossBuiltin where
  accessNatTypeBuiltin = typeAccessor NatType

instance BuiltinHasNatLiterals LossBuiltin where
  accessNatLitBuiltin =
    Access
      { getExpr = \case
          LossBuiltinConstructor (NatLiteral n) -> Just n
          _ -> Nothing,
        mkExpr = LossBuiltinConstructor . NatLiteral
      }

  accessNatTensorLitBuiltin =
    Access
      { getExpr = \case
          LossBuiltinConstructor (NatTensorLiteral b) -> Just b
          _ -> Nothing,
        mkExpr = LossBuiltinConstructor . NatTensorLiteral
      }

  accessAddNatBuiltin = functionAccessor (Add AddNat)
  accessMulNatBuiltin = functionAccessor (Mul MulNat)

instance BuiltinHasListLiterals LossBuiltin where
  accessNilBuiltin =
    Access
      { getExpr = \case
          LossBuiltinConstructor Nil -> Just ()
          _ -> Nothing,
        mkExpr = \() -> LossBuiltinConstructor Nil
      }

  accessConsBuiltin =
    Access
      { getExpr = \case
          LossBuiltinConstructor Cons -> Just ()
          _ -> Nothing,
        mkExpr = \() -> LossBuiltinConstructor Cons
      }

  accessMapListBuiltin = functionAccessor MapList
  accessFoldListBuiltin = functionAccessor FoldList

instance BuiltinHasTensors LossBuiltin where
  accessConstTensorBuiltin = functionAccessor ConstTensor
  accessStackTensorBuiltin = functionAccessor StackTensor
  accessAtTensorBuiltin = functionAccessor At

instance BuiltinHasRatLiterals LossBuiltin where
  accessRatTensorLitBuiltin =
    Access
      { getExpr = \case
          LossBuiltinConstructor (RatTensorLiteral b) -> Just b
          _ -> Nothing,
        mkExpr = LossBuiltinConstructor . RatTensorLiteral
      }

  accessNegRatTensorBuiltin = functionAccessor $ Neg NegRatTensor
  accessAddRatTensorBuiltin = functionAccessor $ Add AddRatTensor
  accessMulRatTensorBuiltin = functionAccessor $ Mul MulRatTensor
  accessSubRatTensorBuiltin = functionAccessor $ Sub SubRatTensor
  accessDivRatTensorBuiltin = functionAccessor $ Div DivRatTensor
  accessMinRatTensorBuiltin = functionAccessor $ Min MinRatTensor
  accessMaxRatTensorBuiltin = functionAccessor $ Max MaxRatTensor
  accessPowRatTensorBuiltin = functionAccessor PowRat
  accessReduceAddRatBuiltin = functionAccessor ReduceAddRatTensor
  accessReduceMulRatBuiltin = functionAccessor ReduceMulRatTensor
  accessReduceMinRatBuiltin = functionAccessor ReduceMinRatTensor
  accessReduceMaxRatBuiltin = functionAccessor ReduceMaxRatTensor
-}
--------------------------------------------------------------------------------
-- Pretty printing

nonDecidableEquivalent :: DecidableBuiltinFunction -> BuiltinFunction
nonDecidableEquivalent = \case
  DecNot -> Not
  DecAnd -> And
  DecOr -> Or
  DecImplies -> Implies
  DecCompare dom op -> Compare dom op
  DecReduceAndTensor -> ReduceAndTensor
  DecReduceOrTensor -> ReduceOrTensor

instance Pretty DecidableBuiltinType where
  pretty t = case t of
    DecBool -> "Bool?"
    HasNot -> pretty $ show t
    HasAnd -> pretty $ show t
    HasOr -> pretty $ show t
    HasImplies -> pretty $ show t
    HasCompare dom op -> "Has" <+> pretty dom <+> pretty op
    HasReduceAndTensor -> pretty $ show t
    HasReduceOrTensor -> pretty $ show t

instance Pretty DecidableBuiltinFunction where
  pretty f = pretty (nonDecidableEquivalent f) <> "?"

instance Pretty DecidableBuiltinConstructor where
  pretty = \case
    DecBoolTensor t -> pretty t

instance Pretty DecidableBuiltin where
  pretty = \case
    StandardBuiltinType t -> pretty t
    StandardBuiltinFunction f -> pretty f
    StandardBuiltinConstructor c -> pretty c
    DecidableBuiltinFunction f -> pretty f
    DecidableBuiltinType t -> pretty t
    DecidableBuiltinConstructor c -> pretty c
