module Vehicle.Data.QuantifiedVariable
  ( Variable,
    makeTensorVariable,
    reduceTensorVariable,
    TensorVariableInfo (..),
    TensorVariable,
    UserVariable,
    NetworkVariable,
    NetworkElementVariable,
    prettyRationalAsFloat,
    UserVariableAssignment (..),
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.Text qualified as Text
import GHC.Generics (Generic)
import Numeric (showFFloat)
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Standard ()
import Vehicle.Data.Code.Interface (mkDims)
import Vehicle.Data.Code.LinearExpr (Variable)
import Vehicle.Data.Code.TypedView (RatTensorValue (..), fromRatTensorValue, pattern INatType)
import Vehicle.Data.Code.Value
import Vehicle.Data.DeBruijn
import Vehicle.Data.Tensor
import Vehicle.Prelude

--------------------------------------------------------------------------------
-- Variables

makeTensorVariable :: Lv -> Variable
makeTensorVariable = id

reduceTensorVariable ::
  Lv ->
  Name ->
  TensorShape ->
  ([Name], Tensor Variable, Value Builtin)
reduceTensorVariable lv varName shape = runSupply (go shape []) [lv ..]
  where
    createRatVar :: TensorIndices -> Lv -> ([Name], Tensor Variable, Value Builtin)
    createRatVar indices currentLv = do
      let name = varName <> Text.pack (showTensorIndices indices)
      ([name], ZeroDimTensor currentLv, VBoundVar currentLv [])

    go ::
      TensorShape ->
      TensorIndices ->
      Supply Lv ([Name], Tensor Variable, Value Builtin)
    go dims indices = case dims of
      [] -> createRatVar (reverse indices) <$> demand
      d : ds -> do
        -- Use the list monad to create a nested list of all possible indices into the tensor
        let allIndices = [0 .. d - 1]

        -- Generate the corresponding names from the indices
        (elementVarNames, elementVars, elementExprs) <- unzip3 <$> traverse (\i -> go ds (i : indices)) allIndices
        let varsNames = concat elementVarNames
        let vars = stack ds elementVars
        let dimsExpr = mkDims INatType ds
        let varsExpr = fromRatTensorValue $ VRatStackTensor (implicit INatType) (implicit dimsExpr) (fmap explicit elementExprs)
        return (varsNames, vars, varsExpr)

type TensorVariable = Variable

-- | Variables entered by the user
type UserVariable = Variable

type NetworkVariable = Variable

type NetworkElementVariable = Variable

data TensorVariableInfo = TensorVariableInfo
  { -- | Variables for each of it's elements
    elementVariables :: Tensor Variable,
    -- | The tensor literal expression containing the element variables above.
    reducedVarExpr :: Value Builtin,
    -- | `Nothing` = user variable, `Input` = network input variable, `Output` = network output variable
    tensorVariableType :: Maybe InputOrOutput
  }

--------------------------------------------------------------------------------
-- Constants

prettyRationalAsFloat :: Rational -> Doc a
prettyRationalAsFloat p = do
  let f = realToFrac p :: Double
  pretty $ showFFloat Nothing f ""

--------------------------------------------------------------------------------
-- User variable assignments

-- | A (satisfying) assignment to a set of user-level variables.
newtype UserVariableAssignment
  = UserVariableAssignment [(Name, RatTensor)]
  deriving (Generic)

instance ToJSON UserVariableAssignment

instance FromJSON UserVariableAssignment

instance Pretty UserVariableAssignment where
  pretty (UserVariableAssignment assignment) =
    vsep (fmap pretty assignment)
