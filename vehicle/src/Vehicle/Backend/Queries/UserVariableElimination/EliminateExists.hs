module Vehicle.Backend.Queries.UserVariableElimination.EliminateExists
  ( solveExists,
  )
where

import Control.Monad.Reader (MonadReader (..))
import Control.Monad.State (MonadState (..))
import Data.Foldable (foldlM)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, isJust)
import Vehicle.Backend.Queries.ConstraintSearch
import Vehicle.Backend.Queries.UserVariableElimination.Core
import Vehicle.Compile.FourierMotzkinElimination
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print (prettyFriendly)
import Vehicle.Data.Assertion
import Vehicle.Data.Code.BooleanExpr
import Vehicle.Data.Code.LinearExpr (Constant (..), LinearExpr, eliminateVars, rearrangeExprToSolveFor, referencesVariable)
import Vehicle.Data.QuantifiedVariable
import Vehicle.Data.Tensor (RationalTensor, allTensor, tensorToList)
import Vehicle.Prelude.Warning (CompileWarning (..))
import Vehicle.Syntax.Builtin.BasicOperations (Strictness (..))

--------------------------------------------------------------------------------
-- Main function

-- | Eliminates the provided user variable from the assertion tree. This may
-- require partially converting the expression to disjunctive normal form so it
-- returns a set of disjuncted updated assertion trees and variable solutions.
solveExists ::
  (MonadSolveExists m) =>
  MaybeTrivial Partitions ->
  Variable ->
  m (MaybeTrivial Partitions)
solveExists maybePartitions userVar = case maybePartitions of
  Trivial b -> return $ Trivial b
  NonTrivial partitions -> do
    let solve (sol, tree) = do
          logDebugM MaxDetail $ do
            ctx <- getGlobalNamedBoundCtx
            let userVarName = lookupLvInBoundCtx userVar ctx
            return $ "Solving for" <+> quotePretty userVarName <+> "in:" <> line <> indent 2 (prettyFriendly (WithContext tree ctx)) <> line

          constraints <- findVariableConstraints checkAssertion userVar tree
          traverse (solveVariable tree userVar sol) constraints

    newPartitions <- traverse solve (partitionsToDisjuncts partitions)
    return $ foldr1 (orTrivial orPartitions) (disjunctDisjuncts newPartitions)

type MonadSolveExists m = MonadQueryStructure m

--------------------------------------------------------------------------------
-- Tensor equalities

checkAssertion :: ConstraintSearchCriteria
checkAssertion var = \case
  EqualityAssertion eq | equalityExpr eq `referencesVariable` var -> SingleEquality eq (Trivial True)
  InequalityAssertion ineq | inequalityExpr ineq `referencesVariable` var -> Inequalities [ineq] (Trivial True)
  constraint -> Inequalities [] $ NonTrivial $ Query constraint

solveVariable ::
  (MonadSolveExists m) =>
  AssertionTree ->
  TensorVariable ->
  [UserVariableReconstructionStep] ->
  ConstrainedAssertionTree ->
  m (MaybeTrivial Partitions)
solveVariable originalTree userVar solutions constrainedTree = do
  globalCtx <- get
  let maybeTensorVarInfo = Map.lookup userVar (tensorVariableInfo globalCtx)
  let isTensorVariable = isJust maybeTensorVarInfo

  case constrainedTree of
    SingleEquality (Equality tensorEq) remainingTree -> do
      let (_, rearrangedExpr) = rearrangeExprToSolveFor userVar tensorEq
      let elementEqs = case maybeTensorVarInfo of
            Nothing -> []
            Just info -> zip (tensorToList (elementVariables info)) $ reduceTensorExpr globalCtx rearrangedExpr
      let solutionMap = Map.fromList $ (userVar, rearrangedExpr) : elementEqs
      let updatedTree = solutionMap `substituteThrough` remainingTree
      -- Update tree
      logEqualitySolved userVar rearrangedExpr remainingTree updatedTree
      return $ mkSinglePartition (SolveEquality isTensorVariable userVar rearrangedExpr : solutions, updatedTree)
    Inequalities ineqs remainingTree -> case maybeTensorVarInfo of
      Just info -> do
        let userRationalVars = elementVariables info
        logDebug MaxDetail "No equality constraints on original tensor variable found"
        let step = ReconstructTensor UserVariable userVar userRationalVars
        let initial = mkSinglePartition (step : solutions, NonTrivial originalTree)
        foldlM solveExists initial (tensorToList userRationalVars)
      Nothing -> do
        (bounds, newInequalities) <- fourierMotzkinElimination userVar ineqs
        let addIneq ineq = andTrivial andBoolExpr (NonTrivial $ Query $ InequalityAssertion ineq)
        let updatedTree = foldr addIneq remainingTree newInequalities
        let step = SolveInequalities userVar bounds
        logInequalitiesSolved userVar step remainingTree
        return $ mkSinglePartition (step : solutions, updatedTree)

substituteThrough ::
  Map Variable (LinearExpr RationalTensor) ->
  MaybeTrivial AssertionTree ->
  MaybeTrivial AssertionTree
substituteThrough f =
  filterTrivialAtoms
    . fmap
      ( fmap
          ( \case
              EqualityAssertion (Equality expr) -> case eliminateVars f expr of
                Right newExpr -> NonTrivial $ EqualityAssertion $ Equality newExpr
                Left tensor -> Trivial (isZero tensor)
              InequalityAssertion (Inequality strictness expr) -> case eliminateVars f expr of
                Right newExpr -> NonTrivial $ InequalityAssertion $ Inequality strictness newExpr
                Left tensor -> do
                  let test = if strictness == Strict then (0 <) else (0 <=)
                  Trivial $ allTensor test tensor
          )
      )

--------------------------------------------------------------------------------
-- UserRationalVariables and equalities/constraints

logEqualitySolved ::
  (MonadSolveExists m) =>
  Variable ->
  LinearExpr RationalTensor ->
  MaybeTrivial AssertionTree ->
  MaybeTrivial AssertionTree ->
  m ()
logEqualitySolved var rearrangedEq remainingTree updatedTree =
  logDebugM MaxDetail $ do
    ctx <- getGlobalNamedBoundCtx
    let varName = lookupLvInBoundCtx var ctx
    return $
      "Solving"
        <> line
        <> indent 2 (pretty varName <+> "=" <+> prettyFriendly (WithContext rearrangedEq ctx))
        <> line
        <> "in context:"
        <> line
        <> indent 2 (prettyFriendly (WithContext remainingTree ctx))
        <> line
        <> "to get:"
        <> line
        <> indent 2 (prettyFriendly (WithContext updatedTree ctx))

logInequalitiesSolved ::
  (MonadSolveExists m) =>
  Variable ->
  UserVariableReconstructionStep ->
  MaybeTrivial AssertionTree ->
  m ()
logInequalitiesSolved var step remainingTree = do
  PropertyMetaData {..} <- ask
  ctx <- getGlobalNamedBoundCtx
  let varName = fromMaybe "<unknown-var>" $ lookupLvInBoundCtx var ctx

  logWarning $ UnderSpecifiedProblemSpaceVar propertyAddress varName
  logDebugM MaxDetail $ do
    return $
      "Solving"
        <> line
        <> indent 2 (pretty step)
        <> line
        <> "in context:"
        <> line
        <> indent 2 (prettyFriendly (WithContext remainingTree ctx))
