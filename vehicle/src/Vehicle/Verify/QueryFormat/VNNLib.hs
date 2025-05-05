module Vehicle.Verify.QueryFormat.VNNLib where

import Control.Monad (forM)
import Data.List.NonEmpty qualified as NonEmpty
import Vehicle.Compile.Prelude
import Vehicle.Compile.Resource (NetworkTensorType (dimensions), NetworkType (inputTensor, outputTensor))
import Vehicle.Data.Builtin.Core
import Vehicle.Data.QuantifiedVariable (prettyRationalAsFloat)
import Vehicle.Data.Tensor (PrettyTensorShape (PrettyTensorShape), TensorShape)
import Vehicle.Verify.Core
import Vehicle.Verify.QueryFormat.Core
import Vehicle.Verify.QueryFormat.Interface

--------------------------------------------------------------------------------
-- Marabou query format

-- | The query format accepted by the Marabou verifier.
vnnlibQueryFormat :: QueryFormat
vnnlibQueryFormat =
  QueryFormat
    { queryFormatID = VNNLibQueries,
      supportsStrictInequalities = True,
      compileVariable = compileVNNLibVar,
      compileQuery = compileVNNLibQuery,
      queryOutputFormat = outputFormat
    }

outputFormat :: ExternalOutputFormat
outputFormat =
  ExternalOutputFormat
    { formatName = pretty VNNLibQueries,
      formatVersion = Nothing,
      commentToken = ";",
      emptyLines = True
    }

-- | Compiles an individual variable
compileVNNLibVar :: CompileQueryVariable
compileVNNLibVar MetaNetworkEntry {..} inputOrOutput metaNetworkIndex ioIndex = do
  let name = if inputOrOutput == Input then "X" else "Y"
  layoutAsText $ pretty metaNetworkEntryName <> "@" <> pretty metaNetworkIndex <> name <> "_" <> pretty ioIndex

-- | Compiles a network input
compileNetworkInput :: Name -> TensorShape -> Doc a
compileNetworkInput name shape = parens ("declare-input" <+> pretty name <+> "Real" <+> pretty (PrettyTensorShape shape))

-- | Compile a network output
compileNetworkOutput :: Name -> TensorShape -> Doc a
compileNetworkOutput name shape = parens ("declare-output" <+> pretty name <+> "Real" <+> pretty (PrettyTensorShape shape))

-- | "Generates" the name and fetches the shape of the the input or output network tensor
networkTensor :: MetaNetworkEntry -> InputOrOutput -> Int -> (Name, TensorShape)
networkTensor MetaNetworkEntry {..} inputOrOutput metaNetworkIndex = do
  let networkTensors = networkType metaNetworkEntryInfo
  case inputOrOutput of
    Input -> (metaNetworkEntryName <> "@" <> layoutAsText (pretty metaNetworkIndex) <> "X", dimensions $ inputTensor networkTensors)
    Output -> (metaNetworkEntryName <> "@" <> layoutAsText (pretty metaNetworkIndex) <> "Y", dimensions $ outputTensor networkTensors)

-- | Compiles the declarations for a network query
compileNetworkEntry :: MetaNetworkEntry -> Int -> Doc a
compileNetworkEntry metaNetworkEntry@MetaNetworkEntry {..} metaNetworkIndex = do
  let networkInputDocs = indent 2 $ uncurry compileNetworkInput $ networkTensor metaNetworkEntry Input metaNetworkIndex
  let networkOutputDocs = indent 2 $ uncurry compileNetworkOutput $ networkTensor metaNetworkEntry Output metaNetworkIndex
  parens ("declare-network" <+> pretty metaNetworkEntryName <> "@" <> pretty metaNetworkIndex <> line <> networkInputDocs <> line <> networkOutputDocs)

-- | Compiles "all" (network) entries in the MetaNetwork
compileNetworks :: (MonadLogger m) => MetaNetwork -> m (Doc a)
compileNetworks metaNetwork = return $ vsep (zipWith compileNetworkEntry metaNetwork [0 ..])

-- | Compiles an expression representing a single VNNLib query.
compileVNNLibQuery :: CompileQuery
compileVNNLibQuery _address (QueryContents _variables assertions) metaNetwork = do
  networkDocs <- compileNetworks metaNetwork
  assertionDocs <- forM assertions compileAssertion
  let assertionsDoc = vsep assertionDocs <> line <> networkDocs
  return $ layoutAsText assertionsDoc

compileAssertion :: (MonadLogger m) => QueryAssertion QueryVariable -> m (Doc a)
compileAssertion QueryAssertion {..} = do
  let compiledRel = compileRel rel
  let compiledLHS = foldl compileCoefVar "" (NonEmpty.tail lhs)
  let compiledRHS = prettyRationalAsFloat rhs
  return $ parens ("assert" <+> parens (compiledRel <+> parens compiledLHS <+> compiledRHS))

compileRel :: QueryRelation -> Doc a
compileRel = \case
  EqualRel -> "=="
  OrderRel Le -> "<="
  OrderRel Ge -> ">="
  OrderRel Lt -> "<"
  OrderRel Gt -> ">"

compileCoefVar :: Doc a -> (Coefficient, QueryVariable) -> Doc a
compileCoefVar r (coef, var)
  | coef == 1 = "+" <+> parens r <+> pretty var
  | coef == -1 = "-" <+> parens r <+> pretty var
  | coef < 0 = "-" <+> parens r <+> parens ("*" <+> prettyRationalAsFloat (-coef) <+> pretty var)
  | otherwise = "+" <+> parens r <+> parens ("*" <+> prettyRationalAsFloat coef <+> pretty var)
