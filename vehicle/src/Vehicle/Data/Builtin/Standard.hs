{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Data.Builtin.Standard
  ( module Syntax,
  )
where

import Vehicle.Data.Builtin.Core as Syntax
import Vehicle.Data.Builtin.Interface

-----------------------------------------------------------------------------
-- Classes

typeAccessor :: BuiltinType -> Accessor Builtin ()
typeAccessor b =
  Access
    { getExpr = \case
        BuiltinType b1 | b == b1 -> Just ()
        _ -> Nothing,
      mkExpr = \() -> BuiltinType b
    }

functionAccessor :: BuiltinFunction -> Accessor Builtin ()
functionAccessor b =
  Access
    { getExpr = \case
        BuiltinFunction b1 | b == b1 -> Just ()
        _ -> Nothing,
      mkExpr = \() -> BuiltinFunction b
    }

orderAccessor :: OrderDomain -> Accessor Builtin OrderOp
orderAccessor dom =
  Access
    { getExpr = \case
        BuiltinFunction (Order d op) | d == dom -> Just op
        _ -> Nothing,
      mkExpr = \op -> BuiltinFunction (Order dom op)
    }

equalityAccessor :: EqualityDomain -> Accessor Builtin EqualityOp
equalityAccessor dom =
  Access
    { getExpr = \case
        BuiltinFunction (Equals d op) | d == dom -> Just op
        _ -> Nothing,
      mkExpr = \op -> BuiltinFunction (Equals dom op)
    }

instance BuiltinHasBoolLiterals Builtin where
  accessBoolTensorLitBuiltin =
    Access
      { getExpr = \case
          BuiltinConstructor (BoolTensorLiteral b) -> Just b
          _ -> Nothing,
        mkExpr = BuiltinConstructor . BoolTensorLiteral
      }

  accessNotBuiltin = functionAccessor Not
  accessAndBuiltin = functionAccessor And
  accessOrBuiltin = functionAccessor Or
  accessImpliesBuiltin = functionAccessor Implies
  accessReduceAndBuiltin = functionAccessor ReduceAndTensor
  accessReduceOrBuiltin = functionAccessor ReduceOrTensor
  accessIfBuiltin = functionAccessor If

  accessOrderIndexBuiltin = orderAccessor OrderIndex
  accessOrderNatBuiltin = orderAccessor OrderNat
  accessOrderRatTensorBuiltin = orderAccessor OrderRatTensor
  accessEqIndexBuiltin = equalityAccessor EqIndex
  accessEqNatBuiltin = equalityAccessor EqNat
  accessEqRatTensorBuiltin = equalityAccessor EqRatTensor

  accessQuantifyRatTensorBuiltin =
    Access
      { getExpr = \case
          BuiltinFunction (QuantifyRatTensor q) -> Just q
          _ -> Nothing,
        mkExpr = BuiltinFunction . QuantifyRatTensor
      }

instance BuiltinHasIndexLiterals Builtin where
  accessIndexLitBuiltin =
    Access
      { getExpr = \case
          BuiltinConstructor (IndexLiteral n) -> Just n
          _ -> Nothing,
        mkExpr = BuiltinConstructor . IndexLiteral
      }

  accessIndexTensorLitBuiltin =
    Access
      { getExpr = \case
          BuiltinConstructor (IndexTensorLiteral b) -> Just b
          _ -> Nothing,
        mkExpr = BuiltinConstructor . IndexTensorLiteral
      }

instance BuiltinHasNatLiterals Builtin where
  accessNatTypeBuiltin = typeAccessor NatType

  accessNatLitBuiltin =
    Access
      { getExpr = \case
          BuiltinConstructor (NatLiteral n) -> Just n
          _ -> Nothing,
        mkExpr = BuiltinConstructor . NatLiteral
      }

  accessNatTensorLitBuiltin =
    Access
      { getExpr = \case
          BuiltinConstructor (NatTensorLiteral b) -> Just b
          _ -> Nothing,
        mkExpr = BuiltinConstructor . NatTensorLiteral
      }

  accessAddNatBuiltin = functionAccessor (Add AddNat)
  accessMulNatBuiltin = functionAccessor (Mul MulNat)

instance BuiltinHasRatLiterals Builtin where
  accessRatTensorLitBuiltin =
    Access
      { getExpr = \case
          BuiltinConstructor (RatTensorLiteral b) -> Just b
          _ -> Nothing,
        mkExpr = BuiltinConstructor . RatTensorLiteral
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

instance BuiltinHasListLiterals Builtin where
  accessNilBuiltin =
    Access
      { getExpr = \case
          BuiltinConstructor Nil -> Just ()
          _ -> Nothing,
        mkExpr = \() -> BuiltinConstructor Nil
      }

  accessConsBuiltin =
    Access
      { getExpr = \case
          BuiltinConstructor Cons -> Just ()
          _ -> Nothing,
        mkExpr = \() -> BuiltinConstructor Cons
      }

  accessMapListBuiltin = functionAccessor MapList
  accessFoldListBuiltin = functionAccessor FoldList

instance BuiltinHasTensors Builtin where
  accessConstTensorBuiltin = functionAccessor ConstTensor
  accessStackTensorBuiltin = functionAccessor StackTensor
  accessAtTensorBuiltin = functionAccessor At

instance BuiltinHasForeach Builtin where
  accessForeachTensorBuiltin = functionAccessor Foreach

instance BuiltinHasStandardTypeClasses Builtin where
  mkBuiltinTypeClass = TypeClass

instance BuiltinHasStandardTypes Builtin where
  accessBuiltinType =
    Access
      { mkExpr = BuiltinType,
        getExpr = \case
          BuiltinType c -> Just c
          _ -> Nothing
      }

  mkNatInDomainConstraint = NatInDomainConstraint

instance BuiltinHasStandardData Builtin where
  accessBuiltinFunction =
    Access
      { mkExpr = BuiltinFunction,
        getExpr = \case
          BuiltinFunction c -> Just c
          _ -> Nothing
      }

  accessBuiltinConstructor =
    Access
      { mkExpr = BuiltinConstructor,
        getExpr = \case
          BuiltinConstructor c -> Just c
          _ -> Nothing
      }
