module Vehicle.Data.Builtin.Decidability
  ( module Vehicle.Data.Builtin.Decidability,
    module Vehicle.Syntax.Builtin.BasicOperations,
  )
where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Vehicle.Compile.Normalise.NBE (NormalisableBuiltin)
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Normalise (NormalisableBuiltin (..))
import Vehicle.Data.Builtin.Standard (Builtin, BuiltinConstructor, BuiltinFunction (..), BuiltinType)
import Vehicle.Data.DSL (DSLExpr, builtin)
import Vehicle.Data.Tensor (BoolTensor)
import Vehicle.Prelude (Pretty (..), (<+>))
import Vehicle.Syntax.Builtin.BasicOperations

--------------------------------------------------------------------------------
-- Data

data DecidabilityBuiltinType
  = DecBoolType
  deriving (Eq, Ord, Show, Generic)

instance Hashable DecidabilityBuiltinType

data DecidabilityBuiltinTypeClass
  = IsBool
  | HasNot
  | HasAnd
  | HasOr
  | HasImplies
  | HasCompare ComparisonDomain ComparisonOp
  | HasReduceAndTensor
  | HasReduceOrTensor
  deriving (Eq, Ord, Show, Generic)

instance Hashable DecidabilityBuiltinTypeClass

data DecidabilityBuiltinTypeClassOp
  = BoolTC
  | NotTC
  | AndTC
  | OrTC
  | ImpliesTC
  | CompareTC ComparisonDomain ComparisonOp
  | ReduceAndTensorTC
  | ReduceOrTensorTC
  deriving (Eq, Ord, Show, Generic)

instance Hashable DecidabilityBuiltinTypeClassOp

-- | Constructors for types in the language. The types and type-classes
-- are viewed as constructors for `Type`.
data DecidabilityBuiltinFunction
  = DecNot
  | DecAnd
  | DecOr
  | DecImplies
  | DecCompare ComparisonDomain ComparisonOp
  | DecReduceAndTensor
  | DecReduceOrTensor
  deriving (Eq, Ord, Show, Generic)

instance Hashable DecidabilityBuiltinFunction

newtype DecidabilityBuiltinConstructor
  = DecBoolTensor BoolTensor
  deriving (Eq, Show, Ord, Generic)

instance Hashable DecidabilityBuiltinConstructor

-- | The builtin types after translation to loss functions (missing all builtins
-- that involve the Bool type).
data DecidabilityBuiltin
  = StandardBuiltinType BuiltinType
  | StandardBuiltinFunction BuiltinFunction
  | StandardBuiltinConstructor BuiltinConstructor
  | DecidabilityBuiltinType DecidabilityBuiltinType
  | DecidabilityBuiltinTypeClass DecidabilityBuiltinTypeClass
  | DecidabilityBuiltinTypeClassOp DecidabilityBuiltinTypeClassOp
  | DecidabilityBuiltinFunction DecidabilityBuiltinFunction
  | DecidabilityBuiltinConstructor DecidabilityBuiltinConstructor
  deriving (Show, Eq, Generic)

instance Hashable DecidabilityBuiltin

--------------------------------------------------------------------------------
-- Accessors

instance BuiltinHasStandardTypes DecidabilityBuiltin where
  accessBuiltinType =
    Access
      { mkExpr = StandardBuiltinType,
        getExpr = \case
          StandardBuiltinType c -> Just c
          _ -> Nothing
      }

instance BuiltinHasStandardData DecidabilityBuiltin where
  accessBuiltinFunction =
    Access
      { mkExpr = StandardBuiltinFunction,
        getExpr = \case
          StandardBuiltinFunction c -> Just c
          _ -> Nothing
      }

  accessBuiltinConstructor =
    Access
      { mkExpr = StandardBuiltinConstructor,
        getExpr = \case
          StandardBuiltinConstructor c -> Just c
          _ -> Nothing
      }

--------------------------------------------------------------------------------
-- Pretty printing

nonDecidableEquivalent :: DecidabilityBuiltinFunction -> BuiltinFunction
nonDecidableEquivalent = \case
  DecNot -> Not
  DecAnd -> And
  DecOr -> Or
  DecImplies -> Implies
  DecCompare dom op -> Compare dom op
  DecReduceAndTensor -> ReduceAndTensor
  DecReduceOrTensor -> ReduceOrTensor

instance Pretty DecidabilityBuiltinType where
  pretty t = case t of
    DecBoolType -> "Bool?"

instance Pretty DecidabilityBuiltinTypeClass where
  pretty t = case t of
    HasCompare dom op -> "Has" <+> pretty dom <+> pretty op
    IsBool -> pretty $ show t
    HasNot -> pretty $ show t
    HasAnd -> pretty $ show t
    HasOr -> pretty $ show t
    HasImplies -> pretty $ show t
    HasReduceAndTensor -> pretty $ show t
    HasReduceOrTensor -> pretty $ show t

instance Pretty DecidabilityBuiltinFunction where
  pretty f = pretty (nonDecidableEquivalent f) <> "?"

instance Pretty DecidabilityBuiltinConstructor where
  pretty = \case
    DecBoolTensor t -> pretty t

instance Pretty DecidabilityBuiltinTypeClassOp where
  pretty t = case t of
    BoolTC -> pretty $ show t
    NotTC -> pretty $ show t
    AndTC -> pretty $ show t
    OrTC -> pretty $ show t
    ImpliesTC -> pretty $ show t
    ReduceAndTensorTC -> pretty $ show t
    ReduceOrTensorTC -> pretty $ show t
    CompareTC dom op -> "CompareTC" <+> pretty dom <+> pretty op

instance Pretty DecidabilityBuiltin where
  pretty = \case
    StandardBuiltinType t -> pretty t
    StandardBuiltinFunction f -> pretty f
    StandardBuiltinConstructor c -> pretty c
    DecidabilityBuiltinType t -> pretty t
    DecidabilityBuiltinTypeClass t -> pretty t
    DecidabilityBuiltinTypeClassOp t -> pretty t
    DecidabilityBuiltinFunction f -> pretty f
    DecidabilityBuiltinConstructor c -> pretty c

instance ConvertableBuiltin DecidabilityBuiltin Builtin where
  convertBuiltin p b = case b of
    StandardBuiltinType t -> convertBuiltin p t
    StandardBuiltinFunction f -> convertBuiltin p f
    StandardBuiltinConstructor c -> convertBuiltin p c
    DecidabilityBuiltinType t -> cheatConvertBuiltin p (pretty t)
    DecidabilityBuiltinTypeClass t -> cheatConvertBuiltin p (pretty t)
    DecidabilityBuiltinTypeClassOp t -> cheatConvertBuiltin p (pretty t)
    DecidabilityBuiltinFunction f -> cheatConvertBuiltin p (pretty f)
    DecidabilityBuiltinConstructor c -> cheatConvertBuiltin p (pretty c)

instance PrintableBuiltin DecidabilityBuiltin where
  coercionArgs _ = Nothing

--------------------------------------------------------------------------------
-- Normalisation

instance NormalisableBuiltin DecidabilityBuiltin where
  evalScheme = _

  blockingArgs = _

  isTypeClassOp = \case
    DecidabilityBuiltinTypeClassOp {} -> True
    _ -> False

--------------------------------------------------------------------------------
-- DSL

tDecBool :: DSLExpr DecidabilityBuiltin
tDecBool = builtin (DecidabilityBuiltinType DecBoolType)
