{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use id" #-}

module Vehicle.Data.Builtin.Decidability.Instances
  ( decidabilityBuiltinInstances,
  )
where

import Data.List.NonEmpty (NonEmpty)
import Vehicle.Compile.Type.Constraint.Core
import Vehicle.Compile.Type.Core (InstanceCandidate (..), InstanceDatabase (..))
import Vehicle.Data.Builtin.Core (BuiltinFunction (..))
import Vehicle.Data.Builtin.Decidability
import Vehicle.Data.Code.DSL
import Vehicle.Data.DSL

decidabilityBuiltinInstances :: InstanceDatabase DecidabilityBuiltin
decidabilityBuiltinInstances = makeInstanceDatabase allInstances mempty

-- Manually declared here as we have no way of declaring them in the language
-- itself.

-- Also note that annoyingly because of a lack of first class records we have
-- to duplicate the context for both the candidate and the candidate's solution.

allInstances :: [InstanceCandidate DecidabilityBuiltin]
allInstances =
  mkCandidate
    <$> [ ( decTypeClass IsBoolType [tBool],
            tBool,
            False
          ),
          ( decTypeClass IsBoolType [type0],
            type0,
            False
          )
        ]
      <> [ ( decTypeClass HasBoolTensorLiterals [tBool],
             lamDims $ \ds ->
               explLam "bs" (tBoolTensor ds) $ \bs ->
                 bs,
             False
           ),
           ( decTypeClass HasBoolTensorLiterals [type0IgnoreDims],
             decFunction BoolTensorToType,
             False
           )
         ]
      <> decCandidate HasNot Not TypeNot
      <> decCandidate HasAnd And TypeAnd
      <> decCandidate HasOr Or TypeOr
      <> decCandidate HasImplies Implies TypeImplies
      <> decCandidate HasReduceAndTensor ReduceAndTensor TypeAnd
      <> decCandidate HasReduceOrTensor ReduceOrTensor TypeOr
      <> comparisonCandidates Le
      <> comparisonCandidates Lt
      <> comparisonCandidates Ge
      <> comparisonCandidates Gt
      <> comparisonCandidates Eq
      <> comparisonCandidates Ne
      <> [
           ------------------
           -- IsTensorType --
           ------------------
           ( forAllDims $ \ds ->
               isTensorType tBool ds,
             lamDims $ \ds ->
               tTensor tBool ds,
             False
           ),
           ( forAllDims $ \ds ->
               isTensorType type0 ds,
             lamDims $ \_ds ->
               type0,
             False
           ),
           ( forAllDims $ \ds ->
               isTensorType tNat ds,
             lamDims $ \ds ->
               tTensor tNat ds,
             False
           ),
           ( forAllDims $ \ds ->
               isTensorType tRat ds,
             lamDims $ \ds ->
               tTensor tRat ds,
             False
           )
         ]

type TempCandidate = (DSLExpr DecidabilityBuiltin, DSLExpr DecidabilityBuiltin, Bool)

decTypeClass :: DecidabilityBuiltinTypeClass -> NonEmpty (DSLExpr DecidabilityBuiltin) -> DSLExpr DecidabilityBuiltin
decTypeClass tc args = builtin (DecidabilityBuiltinTypeClass tc) @@ args

decFunction :: DecidabilityBuiltinFunction -> DSLExpr DecidabilityBuiltin
decFunction f = builtin (DecidabilityBuiltinFunction f)

decCandidate ::
  DecidabilityBuiltinTypeClass ->
  BuiltinFunction ->
  DecidabilityBuiltinFunction ->
  [TempCandidate]
decCandidate tc standardOp typeOp =
  [ ( forAllDims $ \dims ->
        decTypeClass tc [tTensorRaw @@ [tBool], dims],
      lamDims $ \dims ->
        builtinFunction standardOp .@@ [dims],
      False
    ),
    ( forAllDims $ \dims ->
        decTypeClass tc [type0IgnoreDims, dims],
      lamDims $ \_dims ->
        decFunction typeOp,
      False
    )
  ]

comparisonCandidates :: ComparisonOp -> [TempCandidate]
comparisonCandidates op =
  decCandidate (HasCompare CompareIndex op) (Compare CompareIndex op) (TypeCompare CompareIndex op)
    <> decCandidate (HasCompare CompareNat op) (Compare CompareNat op) (TypeCompare CompareNat op)
    <> decCandidate (HasCompare CompareRatTensor op) (Compare CompareRatTensor op) (TypeCompare CompareRatTensor op)
