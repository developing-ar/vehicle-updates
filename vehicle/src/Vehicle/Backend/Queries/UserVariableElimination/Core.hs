{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Vehicle.Backend.Queries.UserVariableElimination.Core where

import Control.DeepSeq (NFData)
import Control.Monad.Reader (MonadReader (..))
import Control.Monad.State (MonadState (..), gets)
import Data.Aeson (FromJSON, ToJSON)
import Data.Bifunctor (Bifunctor (..))
import Data.LinkedHashMap (LinkedHashMap)
import Data.LinkedHashMap qualified as LinkedHashMap
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes)
import GHC.Generics
import Vehicle.Compile.Context.Free.Class (MonadFreeContext)
import Vehicle.Compile.Error
import Vehicle.Compile.ExpandResources.Core
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Resource (NetworkType (..), dimensions)
import Vehicle.Data.Assertion
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Code.BooleanExpr
import Vehicle.Data.Code.LinearExpr
import Vehicle.Data.Code.Value
import Vehicle.Data.Hashing ()
import Vehicle.Data.QuantifiedVariable
import Vehicle.Data.Tensor
import Vehicle.Verify.Core
import Vehicle.Verify.QueryFormat.Core (QueryVariable)
import Vehicle.Verify.QueryFormat.Interface

--------------------------------------------------------------------------------
-- Network applications

-- | A single application of a neural network to a set of arguments.
type NetworkApplication = (Name, Spine Builtin)

-- | Bookkeeping information associated with an application that describes
-- the variables and corresponding expressions that replace a given
-- NetworkApplication.
data NetworkApplicationReplacement = NetworkApplicationReplacement
  { networkApp :: NetworkApplication,
    networkInfo :: NetworkContextInfo,
    inputVariable :: TensorVariable,
    outputVarExpr :: Value Builtin,
    outputVariable :: TensorVariable
  }

--------------------------------------------------------------------------------
-- Reader state

data PropertyMetaData = PropertyMetaData
  { queryFormat :: QueryFormat,
    networkCtx :: NetworkContext,
    propertyProvenance :: DeclProvenance,
    propertyAddress :: PropertyAddress,
    outputLocation :: Maybe FilePath
  }

--------------------------------------------------------------------------------
-- Global state

data GlobalCtx = GlobalCtx
  { globalBoundVarCtx :: !(GenericBoundCtx Name),
    tensorVariableInfo :: !(Map TensorVariable TensorVariableInfo),
    networkApplications :: !(LinkedHashMap NetworkApplication NetworkApplicationReplacement)
  }

emptyGlobalCtx :: GlobalCtx
emptyGlobalCtx =
  GlobalCtx
    { globalBoundVarCtx = mempty,
      tensorVariableInfo = mempty,
      networkApplications = LinkedHashMap.empty
    }

addVectorVarToBoundVarCtx :: Name -> [Name] -> GenericBoundCtx Name -> GenericBoundCtx Name
addVectorVarToBoundVarCtx tensorVar elementVars ctx = reverse elementVars <> [tensorVar] <> ctx

addUserVarToGlobalContext ::
  Name ->
  TensorShape ->
  GlobalCtx ->
  (TensorVariable, GlobalCtx)
addUserVarToGlobalContext userVarName shape GlobalCtx {..} = do
  -- Create the unreduced and reduced versions of the user variables.
  let currentLevel = Lv $ length globalBoundVarCtx
  let (reducedVariableNames, reducedVariables, reducedVariablesExpr) = reduceTensorVariable (currentLevel + 1) userVarName shape
  let userVar = currentLevel
  let variableInfo =
        TensorVariableInfo
          { elementVariables = reducedVariables,
            reducedVarExpr = reducedVariablesExpr,
            tensorVariableType = Nothing
          }
  let newGlobalCtx =
        GlobalCtx
          { globalBoundVarCtx = addVectorVarToBoundVarCtx userVarName reducedVariableNames globalBoundVarCtx,
            tensorVariableInfo = Map.insert userVar variableInfo tensorVariableInfo,
            ..
          }
  (userVar, newGlobalCtx)

addNetworkApplicationToGlobalCtx ::
  (MonadLogger m) =>
  NetworkApplication ->
  NetworkContextInfo ->
  GlobalCtx ->
  m (Value Builtin, Value Builtin, GlobalCtx)
addNetworkApplicationToGlobalCtx app@(networkName, _) networkInfo GlobalCtx {..} = do
  let metaNetworkSoFar = LinkedHashMap.toList networkApplications
  let applicationNumber = length $ filter (\((name, _), _) -> name == networkName) metaNetworkSoFar

  -- Create a single variable for the input of the network to
  -- (avoiding prematurely normalising so that we can potentially solve
  -- user tensor variables in terms of it).
  let inputLv = Lv $ length globalBoundVarCtx
  let inputShape = dimensions (inputTensor (networkType networkInfo))
  let inputVarName = layoutAsText $ createNetworkVarName networkName applicationNumber Input
  let inputVar = makeTensorVariable inputLv
  let (reducedInputVarNames, reducedInputVars, reducedInputVarsExpr) = reduceTensorVariable (inputLv + 1) inputVarName inputShape
  let inputVarExpr = VBoundVar inputLv []
  let inputVarInfo =
        TensorVariableInfo
          { elementVariables = reducedInputVars,
            reducedVarExpr = reducedInputVarsExpr,
            tensorVariableType = Just Input
          }

  -- Create a tensor of variables for the output of the network.
  let outputLv = inputLv + 1 + Lv (length reducedInputVarNames)
  let outputShape = dimensions (outputTensor (networkType networkInfo))
  let outputVarName = layoutAsText $ createNetworkVarName networkName applicationNumber Output
  let outputVar = makeTensorVariable outputLv
  let (reducedOutputVarNames, reducedOutputVars, reducedOutputVarsExpr) = reduceTensorVariable (outputLv + 1) outputVarName outputShape
  let outputVarExpr = VBoundVar outputLv []
  let outputVarInfo =
        TensorVariableInfo
          { elementVariables = reducedOutputVars,
            reducedVarExpr = reducedOutputVarsExpr,
            tensorVariableType = Just Output
          }

  -- Create the context extension of the bound context.
  let newGlobalBoundVarCtx =
        addVectorVarToBoundVarCtx outputVarName reducedOutputVarNames $
          addVectorVarToBoundVarCtx inputVarName reducedInputVarNames globalBoundVarCtx

  -- Create the object to store information about the application
  let appInfo =
        NetworkApplicationReplacement
          { networkApp = app,
            networkInfo = networkInfo,
            inputVariable = inputVar,
            outputVarExpr = outputVarExpr,
            outputVariable = outputVar
          }

  let newTensorVariableInfo =
        Map.insert inputVar inputVarInfo $
          Map.insert outputVar outputVarInfo tensorVariableInfo

  let newGlobalCtx =
        GlobalCtx
          { globalBoundVarCtx = newGlobalBoundVarCtx,
            tensorVariableInfo = newTensorVariableInfo,
            networkApplications = LinkedHashMap.insert app appInfo networkApplications,
            ..
          }

  return (inputVarExpr, outputVarExpr, newGlobalCtx)

--------------------------------------------------------------------------------
-- Reconstructions

data VariableType = UserVariable | OtherVariable
  deriving (Eq, Ord, Show, Generic)

instance NFData VariableType

instance ToJSON VariableType

instance FromJSON VariableType

-- | One step in the process for transforming unreduced user variables into
-- reduced network input and output variables.
data UserVariableReconstructionStep
  = SolveEquality Bool Variable (LinearExpr RatTensor)
  | SolveInequalities Variable (Bounds RatTensor)
  | ReconstructTensor VariableType TensorVariable (Tensor Variable)
  deriving (Eq, Ord, Show, Generic)

instance NFData UserVariableReconstructionStep

instance ToJSON UserVariableReconstructionStep

instance FromJSON UserVariableReconstructionStep

instance Pretty UserVariableReconstructionStep where
  pretty = \case
    SolveEquality _ v s -> "Equation:" <+> pretty v <+> "=" <+> prettyVerbose s
    SolveInequalities v s -> "Inequalities:" <+> pretty v <+> "bounded" <+> prettyVerbose s
    ReconstructTensor _ v vs -> "Reconstruct:" <+> pretty v <+> "from" <+> pretty vs

-- Storing the Variable is unnessary and is just for readability. We can get
-- rid of it if we switch to a non-human readable format for the .vcl-plan files.
type VariableStore = GenericBoundCtx (Variable, Name, Maybe QueryVariable)

-- | The steps for transforming unreduced user variables into reduced network
-- input and output varibles.
-- These are used to recreate a satisfying assignment for the user variables
-- from the satisfying assignment for the network variables spat out by the
-- verifier.
-- The steps are stored in the same order they occured during compilation.
data UserVariableReconstruction = Reconstruction
  { variableStore :: VariableStore,
    reconstructionSteps :: [UserVariableReconstructionStep]
  }
  deriving (Generic)

instance NFData UserVariableReconstruction

instance ToJSON UserVariableReconstruction

instance FromJSON UserVariableReconstruction

getQueryVariableCtx :: UserVariableReconstruction -> GenericBoundCtx (Maybe QueryVariable)
getQueryVariableCtx d = fmap (\(_, _, c) -> c) (variableStore d)

getVehicleVariableCtx :: UserVariableReconstruction -> GenericBoundCtx Name
getVehicleVariableCtx d = fmap (\(_, b, _) -> b) (variableStore d)

getQueryVariables :: UserVariableReconstruction -> [QueryVariable]
getQueryVariables = catMaybes . getQueryVariableCtx

--------------------------------------------------------------------------------
-- Partitions

type AssertionTree = BooleanExpr Assertion

type Partition = ([UserVariableReconstructionStep], AssertionTree)

newtype Partitions = Partitions (Map [UserVariableReconstructionStep] AssertionTree)

partitionsToDisjuncts :: Partitions -> DisjunctAll Partition
partitionsToDisjuncts (Partitions ps) = DisjunctAll $ NonEmpty.fromList $ Map.toList ps

andPartitions :: Partitions -> Partitions -> Partitions
andPartitions (Partitions xs) (Partitions ys) = do
  let xs' = Map.toList xs
  let ys' = Map.toList ys
  let combine (s1, t1) (s2, t2) = (s1 <> s2, andBoolExpr t1 t2)
  Partitions $ Map.fromList $ cartesianProduct combine xs' ys'

orPartitions :: Partitions -> Partitions -> Partitions
orPartitions (Partitions p1) (Partitions p2) =
  Partitions $ Map.unionWith orBoolExpr p1 p2

mkSinglePartition :: ([UserVariableReconstructionStep], MaybeTrivial AssertionTree) -> MaybeTrivial Partitions
mkSinglePartition (solutions, maybeAssertion) =
  fmap (Partitions . Map.singleton solutions) maybeAssertion

mkTrivialPartition :: Assertion -> MaybeTrivial Partitions
mkTrivialPartition assertion = mkSinglePartition (mempty, NonTrivial $ Query assertion)

--------------------------------------------------------------------------------
-- Monads

type MonadPropertyStructure m =
  ( MonadFreeContext Builtin m,
    MonadReader PropertyMetaData m,
    MonadCompile m
  )

type MonadQueryStructure m =
  ( MonadPropertyStructure m,
    MonadState GlobalCtx m
  )

getGlobalNamedBoundCtx :: (MonadQueryStructure m) => m NamedBoundCtx
getGlobalNamedBoundCtx = gets (fmap Just . globalBoundVarCtx)

prettyFriendlyInCtx :: (MonadQueryStructure m) => Value Builtin -> m (Doc a)
prettyFriendlyInCtx e = prettyFriendly . WithContext e <$> getGlobalNamedBoundCtx

getTensorVariableShape :: (MonadState GlobalCtx m) => TensorVariable -> m TensorShape
getTensorVariableShape var = do
  globalCtx <- get
  let info = getTensorVariableInfo globalCtx var
  return (tensorShape $ elementVariables info)

getRationalVariable :: (MonadState GlobalCtx m) => Lv -> m Variable
getRationalVariable var = do
  ctx <- get
  case Map.lookup var (tensorVariableInfo ctx) of
    Nothing -> return var
    Just info -> do
      let rvs = elementVariables info
      case rvs of
        ZeroDimTensor rv -> return rv
        _ -> developerError "Mismatched tensor dimensions!"

getTensorVariableInfo :: GlobalCtx -> TensorVariable -> TensorVariableInfo
getTensorVariableInfo GlobalCtx {..} var = do
  case Map.lookup var tensorVariableInfo of
    Just info -> info
    Nothing ->
      developerError $
        "Network variable" <+> pretty var <+> "has no associated meta-information"

getReducedVariablesFor :: GlobalCtx -> TensorVariable -> Tensor Variable
getReducedVariablesFor globalCtx var = elementVariables $ getTensorVariableInfo globalCtx var

getReducedVariableExprFor :: (MonadState GlobalCtx m, MonadLogger m) => Lv -> m (Maybe (Value Builtin))
getReducedVariableExprFor var = do
  ctx <- get
  return $ reducedVarExpr <$> Map.lookup var (tensorVariableInfo ctx)

reduceTensorExpr ::
  GlobalCtx ->
  LinearExpr RatTensor ->
  [LinearExpr RatTensor]
reduceTensorExpr globalCtx (Sparse coeff constant) = do
  let constValues = tensorToList constant
  let numRatEqs = product (tensorShape constant)
  let coeffList = fmap (first (tensorToList . getReducedVariablesFor globalCtx)) (Map.toList coeff)
  let asserts = fmap (mkRatEquality coeffList constValues) [0 .. numRatEqs - 1]
  asserts
  where
    mkRatEquality ::
      [([Variable], Coefficient)] ->
      [Rational] ->
      Int ->
      LinearExpr RatTensor
    mkRatEquality coeffs consts i =
      Sparse (Map.fromList (fmap (first (!! i)) coeffs)) (ZeroDimTensor (consts !! i))

--------------------------------------------------------------------------------
-- Context operations

variableCtxToBoundCtx :: (Pretty variable) => [variable] -> BoundCtx (Type builtin)
variableCtxToBoundCtx ctx = zipWith variableCtxToBoundCtxEntry [0 .. Ix (length ctx - 1)] ctx
  where
    variableCtxToBoundCtxEntry ix var = mkExplicitBinder (BoundVar mempty ix) (Just (layoutAsText $ pretty var))
