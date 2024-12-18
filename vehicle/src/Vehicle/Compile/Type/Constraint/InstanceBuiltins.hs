{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use id" #-}

module Vehicle.Compile.Type.Constraint.InstanceBuiltins
  ( standardBuiltinInstances,
  )
where

import Data.Bifunctor (Bifunctor (..))
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as Map
import Vehicle.Compile.Type.Constraint.Core
import Vehicle.Compile.Type.Core (InstanceCandidate (..), InstanceDatabase (..), InstanceSearchDepth)
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.DSL
import Vehicle.Data.DSL
import Vehicle.Libraries.StandardLibrary.Definitions
import Vehicle.Prelude

standardBuiltinInstances :: InstanceDatabase Builtin
standardBuiltinInstances = do
  let tcAndCandidates = fmap (second (: []) . extractHeadFromInstanceCandidate) allInstances
  let instances = Map.fromListWith (<>) tcAndCandidates
  let defaults = Map.mapMaybeWithKey findDefault instances
  InstanceDatabase instances defaults searchDepth

--------------------------------------------------------------------------------
-- Builtin instances

searchDepth :: HashMap Builtin InstanceSearchDepth
searchDepth =
  [ (TypeClass HasVecLits, 1)
  ]

-- Manually declared here as we have no way of declaring them in the language
-- itself.

-- Also note that annoyingly because of a lack of first class records we have
-- to duplicate the context for both the candidate and the candidate's solution.

allInstances :: [InstanceCandidate Builtin]
allInstances =
  mkCandidate
    <$> [
          -----------------------
          -- ValidPropertyType --
          -----------------------
          ( forAllDims $ \ds ->
              validPropertyType (tBoolTensor ds),
            lamDims $ \_ds ->
              tUnit,
            False
          ),
          ------------------------------------
          -- ValidNonInferableParameterType --
          ------------------------------------
          ( validNonInferableParameterType (tBoolTensor dimNil),
            unitLit,
            False
          ),
          ( forAllIrrelevantNat "n" $ \n ->
              validNonInferableParameterType (tIndex n),
            irrelImplNatLam "n" $ \_n ->
              unitLit,
            False
          ),
          ( validNonInferableParameterType tNat,
            unitLit,
            False
          ),
          ( validNonInferableParameterType (tRatTensor dimNil),
            unitLit,
            False
          ),
          ---------------------------------
          -- ValidInferableParameterType --
          ---------------------------------
          ( validInferableParameterType tNat,
            unitLit,
            False
          ),
          ----------------------
          -- ValidDatasetType --
          ----------------------
          ( forAllTypes $ \t ->
              validDatasetListElementType t
                .~~~> validDatasetType (tList t),
            implLam "t" type0 $ \t ->
              instLam "r1" (validDatasetListElementType t) $ \_ ->
                tUnit,
            False
          ),
          ( forAllTypes $ \t ->
              forAllDims $ \ds ->
                validDatasetTensorElementType t
                  .~~~> validDatasetType (tTensor t ds),
            implLam "t" type0 $ \t ->
              lamDims $ \_ds ->
                instLam "r1" (validDatasetTensorElementType t) $ \_ ->
                  tUnit,
            False
          ),
          -- List element types
          ( forAllTypes $ \t ->
              validDatasetListElementType t
                .~~~> validDatasetListElementType (tList t),
            implLam "t" type0 $ \t ->
              instLam "r1" (validDatasetListElementType t) $ \_ ->
                tUnit,
            False
          ),
          ( forAllTypes $ \t ->
              forAllDims $ \ds ->
                validDatasetTensorElementType t
                  .~~~> validDatasetListElementType (tTensor t ds),
            implLam "t" type0 $ \t ->
              lamDims $ \_ds ->
                instLam "r1" (validDatasetTensorElementType t) $ \_ ->
                  tUnit,
            False
          ),
          ( forAllIrrelevantNat "n" $ \n ->
              validDatasetListElementType (tIndex n),
            irrelImplNatLam "n" $ \_n ->
              tUnit,
            False
          ),
          ( validDatasetListElementType tNat,
            tUnit,
            False
          ),
          -- Element typs
          ( forAllIrrelevantNat "n" $ \n ->
              validDatasetTensorElementType (tIndex n),
            irrelImplNatLam "n" $ \_n ->
              tUnit,
            False
          ),
          ( validDatasetTensorElementType tNat,
            tUnit,
            False
          ),
          ( validDatasetTensorElementType tRat,
            tUnit,
            False
          ),
          ----------------------
          -- ValidNetworkType --
          ----------------------
          ( forAllDims $ \ds1 ->
              forAllDims $ \ds2 ->
                validNetworkType (tRatTensor ds1 ~> tRatTensor ds2),
            lamDims $ \_ds1 ->
              lamDims $ \_ds2 ->
                tUnit,
            False
          ),
          ----------------
          -- HasRatLits --
          ----------------
          ( hasRatLits (tRatTensor dimNil),
            builtinFunction (FromRat FromRatToRat),
            False
          ),
          ----------------
          -- HasNatLits --
          ----------------
          ( forAllIrrelevantNat "n" $ \n ->
              hasNatLits (tIndex n),
            irrelImplNatLam "n" $ \n ->
              builtinFunction (FromNat FromNatToIndex) .@@@ [n],
            False
          ),
          ( hasNatLits tNat,
            builtinFunction (FromNat FromNatToNat),
            True
          ),
          ( hasNatLits (tRatTensor dimNil),
            builtinFunction (FromNat FromNatToRat),
            False
          ),
          ----------------
          -- HasVecLits --
          ----------------
          ( forAllDim Irrelevant $ \d ->
              forAllDims $ \ds ->
                hasVecLits (lamType $ \tElem -> builtin (TypeClassOp TensorTypeTC) @@ [tElem, dimCons d ds]) d,
            lamDim $ \d ->
              lamDims $ \ds ->
                builtinFunction StackTensor @@@ [d] .@@@ [ds],
            False
          ),
          ( forAllDim Irrelevant $ \d ->
              hasVecLits tListRaw d,
            lamDim $ \d ->
              builtinFunction FromVectorToList @@@ [d],
            False
          ),
          ------------------
          -- IsTensorType --
          ------------------
          ( forAllDims $ \ds ->
              isTensorType tBool ds,
            lamDims $ \ds ->
              tTensor tBool ds,
            False
          ),
          ( forAllDim Irrelevant $ \n ->
              forAllDims $ \ds ->
                isTensorType (tIndex n) ds,
            lamDim $ \n ->
              lamDims $ \ds ->
                tTensor (tIndex n) ds,
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
          ),
          ( forAllIrrelevant "ds1" tDims $ \ds1 ->
              forAllIrrelevant "ds2" tDims $ \ds2 ->
                forAllTypes $ \t ->
                  isTensorType (tTensor t ds1) ds2,
            lamDims $ \ds1 ->
              lamDims $ \ds2 ->
                implLam "t" type0 $ \t ->
                  tTensor t (free StdAppendList @@@ [tNat] @@ [ds2, ds1]),
            False
          ),
          ------------
          -- HasNeg --
          ------------
          ( forAllDims $ \dims -> hasNeg (tRatTensor dims) (tRatTensor dims),
            lamDims $ \dims -> builtinFunction (Neg NegRatTensor) .@@@ [dims],
            False
          ),
          ------------
          -- HasAdd --
          ------------
          ( hasAdd tNat tNat tNat,
            builtinFunction (Add AddNat),
            True
          ),
          ( forAllDims $ \dims -> hasAdd (tRatTensor dims) (tRatTensor dims) (tRatTensor dims),
            lamDims $ \dims -> builtinFunction (Add AddRatTensor) .@@@ [dims],
            False
          ),
          ------------
          -- HasSub --
          ------------
          ( forAllDims $ \dims -> hasSub (tRatTensor dims) (tRatTensor dims) (tRatTensor dims),
            lamDims $ \dims -> builtinFunction (Sub SubRatTensor) .@@@ [dims],
            False
          ),
          ------------
          -- HasMul --
          ------------
          ( hasMul tNat tNat tNat,
            builtinFunction (Mul MulNat),
            True
          ),
          ( forAllDims $ \dims -> hasMul (tRatTensor dims) (tRatTensor dims) (tRatTensor dims),
            lamDims $ \dims -> builtinFunction (Mul MulRatTensor) .@@@ [dims],
            False
          ),
          ------------
          -- HasDiv --
          ------------
          ( forAllDims $ \dims -> hasDiv (tRatTensor dims) (tRatTensor dims) (tRatTensor dims),
            lamDims $ \dims -> builtinFunction (Div DivRatTensor) .@@@ [dims],
            False
          ),
          ------------
          -- HasMap --
          ------------
          ( hasMap tListRaw,
            builtinFunction MapList,
            True
          ),
          ------------
          -- HasFold --
          ------------
          ( hasFold tListRaw,
            builtinFunction FoldList,
            False
          )
        ]
      <> orderCandidates Le
      <> orderCandidates Lt
      <> orderCandidates Ge
      <> orderCandidates Gt
      <> eqCandidates Eq
      <> eqCandidates Neq
      <> quantifierCandidates Forall StdForallIndex
      <> quantifierCandidates Exists StdExistsIndex
  where
    orderCandidates :: OrderOp -> [(StandardDSLExpr, StandardDSLExpr, Bool)]
    orderCandidates op =
      [ ( forAll "n1" tNat $ \n1 ->
            forAll "n2" tNat $ \n2 ->
              hasOrd op (tIndex n1) (tIndex n2) (tBoolTensor dimNil),
          implLam "n1" tNat $ \n1 ->
            implLam "n2" tNat $ \n2 ->
              builtinFunction (Order OrderIndex op) @@@ [n1, n2],
          False
        ),
        ( hasOrd op tNat tNat (tBoolTensor dimNil),
          builtinFunction (Order OrderNat op),
          True
        ),
        ( forAllDims $ \dims -> hasOrd op (tRatTensor dims) (tRatTensor dims) (tBoolTensor dims),
          lamDims $ \dims -> builtinFunction (Order OrderRatTensor op) .@@@ [dims],
          False
        )
      ]

    eqCandidates :: EqualityOp -> [(StandardDSLExpr, StandardDSLExpr, Bool)]
    eqCandidates op =
      [ ( forAll "n1" tNat $ \n1 ->
            forAll "n2" tNat $ \n2 ->
              hasEq op (tIndex n1) (tIndex n2) (tBoolTensor dimNil),
          implLam "n1" tNat $ \n1 ->
            implLam "n2" tNat $ \n2 ->
              builtinFunction (Equals EqIndex op) @@@ [n1, n2],
          False
        ),
        ( hasEq op tNat tNat (tBoolTensor dimNil),
          builtinFunction (Equals EqNat op),
          True
        ),
        ( forAllDims $ \dims -> hasEq op (tRatTensor dims) (tRatTensor dims) (tBoolTensor dims),
          lamDims $ \dims -> builtinFunction (Equals EqRatTensor op) .@@@ [dims],
          False
        )
      ]

    quantifierCandidates ::
      Quantifier ->
      StdLibFunction ->
      [(StandardDSLExpr, StandardDSLExpr, Bool)]
    quantifierCandidates q indexOp =
      [ ( forAllNat $ \n ->
            hasQuantifier q (tIndex n),
          lamDim $ \d ->
            free indexOp @@ [d],
          False
        ),
        ( forAllDims $ \ds ->
            hasQuantifier q (tRatTensor ds),
          lamDims $ \ds ->
            builtinFunction (QuantifyRatTensor q) @@@ [ds],
          False
        )
      ]

type StandardDSLExpr = DSLExpr Builtin

findDefault :: Builtin -> [InstanceCandidate builtin] -> Maybe (InstanceCandidate builtin)
findDefault b instances = do
  let defaultInstances = filter defaultInstance instances
  case defaultInstances of
    [] -> Nothing
    [inst] -> Just inst
    _ -> developerError $ "Multiple default instances found for" <+> quotePretty b
