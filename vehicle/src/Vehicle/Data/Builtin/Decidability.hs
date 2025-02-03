module Vehicle.Data.Builtin.Decidability
  ( module Vehicle.Data.Builtin.Decidability,
    module Vehicle.Syntax.Builtin.BasicOperations,
  )
where

import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Vehicle.Compile.Normalise.NBE (NormalisableBuiltin)
import Vehicle.Data.Builtin.Interface
import Vehicle.Data.Builtin.Interface.Normalise (BlockingArgs (..), EvalScheme (..), MonadNormBuiltin, NormalisableBuiltin (..), evalIterate, forceEvalSimpleBuiltin)
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Data.Builtin.Standard (Builtin, BuiltinConstructor (..), BuiltinFunction (..), BuiltinType)
import Vehicle.Data.Code.Interface
import Vehicle.Data.DSL (DSLExpr, builtin)
import Vehicle.Data.Tensor (BoolTensor)
import Vehicle.Prelude (Pretty (..), developerError, (<+>))
import Vehicle.Syntax.Builtin.BasicOperations
import Vehicle.Syntax.Sugar (BinderType (..))

--------------------------------------------------------------------------------
-- Data

data DecidabilityBuiltinType
  = DecBoolType
  deriving (Eq, Ord, Show, Generic)

instance Hashable DecidabilityBuiltinType

data DecidabilityBuiltinTypeClass
  = IsBool
  | HasBoolTensorLiterals
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
  = BoolTypeTC
  | FromBoolTensorLitTC
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
  | BoolTensorToDecBoolTensor
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

functionAccessor :: BuiltinFunction -> Accessor DecidabilityBuiltin ()
functionAccessor b =
  Access
    { getExpr = \case
        StandardBuiltinFunction b1 | b == b1 -> Just ()
        _ -> Nothing,
      mkExpr = \() -> StandardBuiltinFunction b
    }

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

instance BuiltinHasNatLiterals DecidabilityBuiltin where
  accessNatLitBuiltin =
    Access
      { getExpr = \case
          StandardBuiltinConstructor (NatLiteral n) -> Just n
          _ -> Nothing,
        mkExpr = StandardBuiltinConstructor . NatLiteral
      }

  accessNatTensorLitBuiltin =
    Access
      { getExpr = \case
          StandardBuiltinConstructor (NatTensorLiteral b) -> Just b
          _ -> Nothing,
        mkExpr = StandardBuiltinConstructor . NatTensorLiteral
      }

  accessAddNatBuiltin = functionAccessor (Add AddNat)
  accessMulNatBuiltin = functionAccessor (Mul MulNat)

instance BuiltinHasBinders DecidabilityBuiltin where
  getBuiltinBinder = \case
    StandardBuiltinFunction Foreach -> Just ForeachBinder
    StandardBuiltinFunction (QuantifyRatTensor q) -> Just $ QuantifierBinder q
    _ -> Nothing

instance BuiltinHasIterate DecidabilityBuiltin where
  accessIterateBuiltin = functionAccessor Iterate

--------------------------------------------------------------------------------
-- Pretty printing

instance Pretty DecidabilityBuiltinType where
  pretty t = case t of
    DecBoolType -> "Bool?"

instance Pretty DecidabilityBuiltinTypeClass where
  pretty t = case t of
    HasCompare dom op -> "Has" <+> pretty dom <+> pretty op
    HasBoolTensorLiterals -> pretty $ show t
    IsBool -> pretty $ show t
    HasNot -> pretty $ show t
    HasAnd -> pretty $ show t
    HasOr -> pretty $ show t
    HasImplies -> pretty $ show t
    HasReduceAndTensor -> pretty $ show t
    HasReduceOrTensor -> pretty $ show t

instance Pretty DecidabilityBuiltinFunction where
  pretty = \case
    DecNot -> pretty Not <> "?"
    DecAnd -> pretty And <> "?"
    DecOr -> pretty Or <> "?"
    DecImplies -> pretty Implies <> "?"
    DecCompare dom op -> pretty (Compare dom op) <> "?"
    DecReduceAndTensor -> pretty ReduceAndTensor <> "?"
    DecReduceOrTensor -> pretty ReduceOrTensor <> "?"
    BoolTensorToDecBoolTensor -> "boolTensorToDecBoolTensor"

instance Pretty DecidabilityBuiltinConstructor where
  pretty = \case
    DecBoolTensor t -> pretty t

instance Pretty DecidabilityBuiltinTypeClassOp where
  pretty t = case t of
    BoolTypeTC -> pretty $ show t
    FromBoolTensorLitTC -> pretty $ show t
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
  evalScheme = \case
    StandardBuiltinFunction Iterate -> NonSimple evalIterate
    _ -> None

  blockingArgs = \case
    StandardBuiltinFunction Iterate -> Known [2]
    _ -> Known []

  isTypeClassOp = \case
    DecidabilityBuiltinTypeClassOp {} -> True
    _ -> False

  isCast e = case e of
    DecidabilityBuiltinFunction BoolTensorToDecBoolTensor -> Just $ forceEvalSimpleBuiltin evalBoolTensorToDecBoolTensor
    _ -> Nothing

evalBoolTensorToDecBoolTensor ::
  (MonadNormBuiltin m, HasBuiltinConstructor expr) =>
  Op1Args (expr DecidabilityBuiltin) ->
  m (expr DecidabilityBuiltin)
evalBoolTensorToDecBoolTensor args = return $ case args of
  Op1Args (getExpr accessBuiltinC -> Just (StandardBuiltinConstructor (BoolTensorLiteral t), [])) -> mkExpr accessBuiltinC (DecidabilityBuiltinConstructor (DecBoolTensor t), [])
  _ -> developerError $ "Should not be possible to have non-literal" <+> pretty BoolTensorToDecBoolTensor <+> "args"

--------------------------------------------------------------------------------
-- DSL

tDecBool :: DSLExpr DecidabilityBuiltin
tDecBool = builtin (DecidabilityBuiltinType DecBoolType)
