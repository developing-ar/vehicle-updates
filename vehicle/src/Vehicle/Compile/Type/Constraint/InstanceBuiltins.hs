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
import Vehicle.Data.DSL hiding (builtin)
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
                validDatasetBaseElementType t
                  .~~~> validDatasetType (tFlattenTensor t ds),
            implLam "t" type0 $ \t ->
              lamDims $ \_ds ->
                instLam "r1" (validDatasetBaseElementType t) $ \_ ->
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
                validDatasetBaseElementType t
                  .~~~> validDatasetListElementType (tFlattenTensor t ds),
            implLam "t" type0 $ \t ->
              lamDims $ \_ds ->
                instLam "r1" (validDatasetBaseElementType t) $ \_ ->
                  tUnit,
            False
          ),
          ( forAllTypes $ \t ->
              validDatasetBaseElementType t
                .~~~> validDatasetListElementType t,
            implLam "t" type0 $ \t ->
              instLam "r1" (validDatasetBaseElementType t) $ \_ ->
                tUnit,
            False
          ),
          -- Element typs
          ( forAllIrrelevantNat "n" $ \n ->
              validDatasetBaseElementType (tIndex n),
            irrelImplNatLam "n" $ \_n ->
              tUnit,
            False
          ),
          ( validDatasetBaseElementType tNat,
            tUnit,
            False
          ),
          ( validDatasetBaseElementType (tRatTensor dimNil),
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
            builtin (FromRat FromRatToRat),
            False
          ),
          ----------------
          -- HasNatLits --
          ----------------
          ( forAllIrrelevantNat "n" $ \n ->
              hasNatLits (tIndex n),
            irrelImplNatLam "n" $ \n ->
              builtin (FromNat FromNatToIndex) .@@@ [n],
            False
          ),
          ( hasNatLits tNat,
            builtin (FromNat FromNatToNat),
            True
          ),
          ( hasNatLits (tRatTensor dimNil),
            builtin (FromNat FromNatToRat),
            False
          ),
          ----------------
          -- HasVecLits --
          ----------------
          ( forAllDim Irrelevant $ \d ->
              forAllDims $ \ds ->
                hasVecLits (lamType $ \tElem -> tFlattenTensor tElem (dimCons d ds)) d,
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
          ------------
          -- HasNeg --
          ------------
          ( forAllDims $ \dims -> hasNeg (tRatTensor dims) (tRatTensor dims),
            lamDims $ \dims -> builtin (Neg NegRatTensor) .@@@ [dims],
            False
          ),
          ------------
          -- HasAdd --
          ------------
          ( hasAdd tNat tNat tNat,
            builtin (Add AddNat),
            True
          ),
          ( forAllDims $ \dims -> hasAdd (tRatTensor dims) (tRatTensor dims) (tRatTensor dims),
            lamDims $ \dims -> builtin (Add AddRatTensor) .@@@ [dims],
            False
          ),
          ------------
          -- HasSub --
          ------------
          ( forAllDims $ \dims -> hasSub (tRatTensor dims) (tRatTensor dims) (tRatTensor dims),
            lamDims $ \dims -> builtin (Sub SubRatTensor) .@@@ [dims],
            False
          ),
          ------------
          -- HasMul --
          ------------
          ( hasMul tNat tNat tNat,
            builtin (Mul MulNat),
            True
          ),
          ( forAllDims $ \dims -> hasMul (tRatTensor dims) (tRatTensor dims) (tRatTensor dims),
            lamDims $ \dims -> builtin (Mul MulRatTensor) .@@@ [dims],
            False
          ),
          ------------
          -- HasDiv --
          ------------
          ( forAllDims $ \dims -> hasDiv (tRatTensor dims) (tRatTensor dims) (tRatTensor dims),
            lamDims $ \dims -> builtin (Div DivRatTensor) .@@@ [dims],
            False
          ),
          ------------
          -- HasMap --
          ------------
          ( hasMap tListRaw,
            builtin MapList,
            True
          ),
          ------------
          -- HasFold --
          ------------
          ( hasFold tListRaw,
            builtin FoldList,
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
              builtin (Order OrderIndex op) @@@ [n1, n2],
          False
        ),
        ( hasOrd op tNat tNat (tBoolTensor dimNil),
          builtin (Order OrderNat op),
          True
        ),
        ( forAllDims $ \dims -> hasOrd op (tRatTensor dims) (tRatTensor dims) (tBoolTensor dims),
          lamDims $ \dims -> builtin (Order OrderRatTensor op) .@@@ [dims],
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
              builtin (Equals EqIndex op) @@@ [n1, n2],
          False
        ),
        ( hasEq op tNat tNat (tBoolTensor dimNil),
          builtin (Equals EqNat op),
          True
        ),
        ( forAllDims $ \dims -> hasEq op (tRatTensor dims) (tRatTensor dims) (tBoolTensor dims),
          lamDims $ \dims -> builtin (Equals EqRatTensor op) .@@@ [dims],
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

builtin :: BuiltinFunction -> StandardDSLExpr
builtin = builtinFunction

findDefault :: Builtin -> [InstanceCandidate builtin] -> Maybe (InstanceCandidate builtin)
findDefault b instances = do
  let defaultInstances = filter defaultInstance instances
  case defaultInstances of
    [] -> Nothing
    [inst] -> Just inst
    _ -> developerError $ "Multiple default instances found for" <+> quotePretty b
