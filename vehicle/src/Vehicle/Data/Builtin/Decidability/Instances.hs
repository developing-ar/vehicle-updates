{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use id" #-}

module Vehicle.Data.Builtin.Decidability.Instances
  ( decidabilityBuiltinInstances,
  )
where

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
    <$> [ ( decTypeClass IsBool tBool,
            tBool,
            False
          ),
          ( decTypeClass IsBool tDecBool,
            tDecBool,
            False
          )
        ]
      <> [ ( decTypeClass HasBoolTensorLiterals tBool,
             lamDims $ \ds ->
               explLam "bs" (tBoolTensor ds) $ \bs ->
                 bs,
             False
           ),
           ( decTypeClass HasBoolTensorLiterals tDecBool,
             decFunction BoolTensorToDecBoolTensor,
             False
           )
         ]
      <> decCandidate HasNot Not DecNot
      <> decCandidate HasAnd And DecAnd
      <> decCandidate HasOr Or DecOr
      <> decCandidate HasImplies Implies DecImplies
      <> comparisonCandidates Le
      <> comparisonCandidates Lt
      <> comparisonCandidates Ge
      <> comparisonCandidates Gt
      <> comparisonCandidates Eq
      <> comparisonCandidates Ne
      <> decCandidate HasReduceAndTensor ReduceAndTensor DecReduceAndTensor
      <> decCandidate HasReduceOrTensor ReduceOrTensor DecReduceOrTensor

type TempCandidate = (DSLExpr DecidabilityBuiltin, DSLExpr DecidabilityBuiltin, Bool)

decTypeClass :: DecidabilityBuiltinTypeClass -> DSLExpr DecidabilityBuiltin -> DSLExpr DecidabilityBuiltin
decTypeClass tc t = builtin (DecidabilityBuiltinTypeClass tc) @@ [t]

decFunction :: DecidabilityBuiltinFunction -> DSLExpr DecidabilityBuiltin
decFunction f = builtin (DecidabilityBuiltinFunction f)

decCandidate ::
  DecidabilityBuiltinTypeClass ->
  BuiltinFunction ->
  DecidabilityBuiltinFunction ->
  [TempCandidate]
decCandidate tc standardOp builtinOp =
  [ ( decTypeClass tc tBool,
      builtinFunction standardOp,
      False
    ),
    ( decTypeClass tc tDecBool,
      decFunction builtinOp,
      False
    )
  ]

comparisonCandidates :: ComparisonOp -> [TempCandidate]
comparisonCandidates op =
  decCandidate (HasCompare CompareIndex op) (Compare CompareIndex op) (DecCompare CompareIndex op)
    <> decCandidate (HasCompare CompareNat op) (Compare CompareNat op) (DecCompare CompareNat op)
    <> decCandidate (HasCompare CompareRatTensor op) (Compare CompareRatTensor op) (DecCompare CompareRatTensor op)
