{-# OPTIONS_GHC -Wno-orphans #-}

module Vehicle.Data.Builtin.Standard
  ( module Syntax,
  )
where

import Vehicle.Data.Builtin.Core as Syntax
import Vehicle.Data.Builtin.Interface

-----------------------------------------------------------------------------
-- Classes

instance BuiltinHasBoolLiterals Builtin where
  mkBoolBuiltinTensorLit b = BuiltinConstructor (BoolTensorLiteral b)
  getBoolBuiltinTensorLit = \case
    BuiltinConstructor (BoolTensorLiteral b) -> Just b
    _ -> Nothing

instance BuiltinHasIndexLiterals Builtin where
  getIndexBuiltinLit e = case e of
    BuiltinConstructor (IndexLiteral n) -> Just n
    _ -> Nothing
  mkIndexBuiltinLit x = BuiltinConstructor (IndexLiteral x)

instance BuiltinHasIndexTensorLiterals Builtin where
  mkIndexBuiltinTensorLit b = BuiltinConstructor (IndexTensorLiteral b)
  getIndexBuiltinTensorLit = \case
    BuiltinConstructor (IndexTensorLiteral b) -> Just b
    _ -> Nothing

instance BuiltinHasNatLiterals Builtin where
  getNatBuiltinLit e = case e of
    BuiltinConstructor (NatLiteral b) -> Just b
    _ -> Nothing
  mkNatBuiltinLit x = BuiltinConstructor (NatLiteral x)

instance BuiltinHasNatTensorLiterals Builtin where
  mkNatBuiltinTensorLit b = BuiltinConstructor (NatTensorLiteral b)
  getNatBuiltinTensorLit = \case
    BuiltinConstructor (NatTensorLiteral b) -> Just b
    _ -> Nothing

instance BuiltinHasRatLiterals Builtin where
  mkRatBuiltinTensorLit b = BuiltinConstructor (RatTensorLiteral b)
  getRatBuiltinTensorLit = \case
    BuiltinConstructor (RatTensorLiteral b) -> Just b
    _ -> Nothing

instance BuiltinHasListLiterals Builtin where
  isBuiltinNil e = case e of
    BuiltinConstructor Nil -> True
    _ -> False
  mkBuiltinNil = BuiltinConstructor Nil

  isBuiltinCons e = case e of
    BuiltinConstructor Cons -> True
    _ -> False
  mkBuiltinCons = BuiltinConstructor Cons

instance BuiltinHasConstTensor Builtin where
  isConstTensorBuiltin e = case e of
    BuiltinFunction ConstTensor -> True
    _ -> False
  mkConstTensorBuiltin = BuiltinFunction ConstTensor

instance BuiltinHasStandardTypeClasses Builtin where
  mkBuiltinTypeClass = TypeClass

instance BuiltinHasStandardTypes Builtin where
  mkBuiltinType = BuiltinType
  getBuiltinType = \case
    BuiltinType c -> Just c
    _ -> Nothing

  mkNatInDomainConstraint = NatInDomainConstraint

instance BuiltinHasStandardData Builtin where
  mkBuiltinFunction = BuiltinFunction
  getBuiltinFunction = \case
    BuiltinFunction c -> Just c
    _ -> Nothing

  mkBuiltinConstructor = BuiltinConstructor
  getBuiltinConstructor = \case
    BuiltinConstructor c -> Just c
    _ -> Nothing
