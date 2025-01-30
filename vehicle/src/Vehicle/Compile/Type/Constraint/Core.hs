module Vehicle.Compile.Type.Constraint.Core
  ( runConstraintSolver,
    trackIfConstraintProgressMade,
    blockOn,
    malformedConstraintError,
    extractHeadFromInstanceCandidate,
    findInstanceGoalHead,
    parseInstanceGoal,
    createInstanceUnification,
    mkCandidate,
    makeInstanceDatabase,
    AuxiliaryConstraintProgress (..),
  )
where

import Data.Bifunctor (Bifunctor (..))
import Data.Data (Proxy (..))
import Data.HashMap.Strict (HashMap, fromListWith, mapMaybeWithKey)
import Data.Hashable (Hashable)
import Data.IntSet qualified as IntSet
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Meta (MetaSet)
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet
import Vehicle.Compile.Type.Monad.Class (MonadTypeChecker, copyContext, getIsUnblockedFn)
import Vehicle.Data.Code.Value
import Vehicle.Data.DSL

-- | Attempts to solve as many constraints as possible. Takes in
-- the set of meta-variables solved since the solver was last run and outputs
-- the set of meta-variables solved during this run.
runConstraintSolver ::
  forall builtin m constraint.
  (MonadTypeChecker builtin m, PrettyExternal (Contextualised constraint (ConstraintContext builtin))) =>
  Proxy builtin ->
  m [Contextualised constraint (ConstraintContext builtin)] ->
  ([Contextualised constraint (ConstraintContext builtin)] -> m ()) ->
  (Contextualised constraint (ConstraintContext builtin) -> m ()) ->
  m ()
runConstraintSolver _ getConstraints setConstraints attemptToSolveConstraint = loop 0
  where
    loop :: Int -> m ()
    loop loopNumber = do
      unsolvedConstraints <- getConstraints
      if null unsolvedConstraints
        then return mempty
        else do
          isUnblocked <- getIsUnblockedFn

          case findFirstConstraint isUnblocked unsolvedConstraints of
            Nothing -> return mempty
            Just (unblockedConstraint, remainingConstraints) -> do
              -- We have made useful progress so start a new pass
              setConstraints remainingConstraints

              logCompilerSection MaxDetail ("trying:" <+> prettyExternal unblockedConstraint) $
                attemptToSolveConstraint unblockedConstraint

              loop (loopNumber + 1)

trackIfConstraintProgressMade ::
  forall builtin m constraint.
  (MonadTypeChecker builtin m, PrettyExternal (Contextualised constraint (ConstraintContext builtin))) =>
  m [Contextualised constraint (ConstraintContext builtin)] ->
  m () ->
  m Bool
trackIfConstraintProgressMade getConstraints action = do
  let getConstraintIDs = (\x -> IntSet.fromList $ fmap (constraintID . contextOf) x) <$> getConstraints
  oldConstraintIDS <- getConstraintIDs
  action
  newConstraintIDS <- getConstraintIDs
  return $ newConstraintIDS /= oldConstraintIDS

-- | Find the first constraint satisfying `p` appending all the constraints that don't satisfy it to
-- the end of the list, so we don't search through them again immediately next time.
findFirstConstraint :: forall a. (a -> Bool) -> [a] -> Maybe (a, [a])
findFirstConstraint p xs = (\(found, seen, unseen) -> (found, unseen <> seen)) <$> go xs
  where
    go :: [a] -> Maybe (a, [a], [a])
    go = \case
      [] -> Nothing
      c : cs
        | p c -> Just (c, [], cs)
        | otherwise -> fmap (\(found, seen, unseen) -> (found, c : seen, unseen)) (go cs)

data AuxiliaryConstraintProgress builtin
  = Stuck MetaSet
  | Progress [WithContext (UnificationConstraint builtin)] [WithContext (InstanceConstraint builtin)]
  deriving (Show)

instance Semigroup (AuxiliaryConstraintProgress builtin) where
  Stuck m1 <> Stuck m2 = Stuck (m1 <> m2)
  Stuck {} <> x@Progress {} = x
  x@Progress {} <> Stuck {} = x
  Progress u1 r1 <> Progress u2 r2 = Progress (u1 <> u2) (r1 <> r2)

blockOn :: (MonadCompile m) => [MetaID] -> Maybe (m (AuxiliaryConstraintProgress builtin))
blockOn metas = Just $ do
  logDebug MaxDetail $ "stuck-on metas" <+> pretty metas
  return $ Stuck $ MetaSet.fromList metas

malformedConstraintError ::
  (PrintableBuiltin builtin, MonadCompile m) =>
  WithContext (InstanceConstraint builtin) ->
  m a
malformedConstraintError c =
  compilerDeveloperError $ "Malformed auxiliary constraint:" <+> prettyVerbose c

-- | Create a new unification constraint as a subgoal of an existing instance constraint.
createInstanceUnification ::
  (MonadTypeChecker builtin m) =>
  (ConstraintContext builtin, InstanceConstraintOrigin builtin) ->
  Value builtin ->
  Value builtin ->
  m (WithContext (UnificationConstraint builtin))
createInstanceUnification (ctx, origin) e1 e2 = do
  let unifyOrigin = CheckingInstanceType origin
  WithContext (Unify unifyOrigin e1 e2) <$> copyContext ctx

extractHeadFromInstanceCandidate ::
  (PrintableBuiltin builtin) =>
  InstanceCandidate builtin ->
  (builtin, InstanceCandidate builtin)
extractHeadFromInstanceCandidate candidate@InstanceCandidate {..} = do
  case findInstanceGoalHead candidateExpr of
    Right b -> (b, candidate)
    Left subexpr -> do
      let candidateDoc = prettyVerbose subexpr
      let problemDoc = prettyVerbose subexpr
      developerError $
        "Invalid builtin instance candidate:"
          <+> candidateDoc
          <> line
          <> "Problematic subexpr:"
            <+> problemDoc

findInstanceGoalHead :: Expr builtin -> Either (Expr builtin) builtin
findInstanceGoalHead = \case
  Pi _ binder body
    | not (isExplicit binder) -> findInstanceGoalHead body
  App (Builtin _ b) _ -> Right b
  Builtin _ b -> Right b
  expr -> Left expr

parseInstanceGoal ::
  forall builtin.
  (PrintableBuiltin builtin) =>
  Value builtin ->
  InstanceGoal builtin
parseInstanceGoal originalValue = go [] originalValue
  where
    go :: Telescope builtin -> Value builtin -> InstanceGoal builtin
    go telescope = \case
      VPi binder _body
        | not (isExplicit binder) -> developerError "Instance goals with telescopes not yet supported"
      VBuiltin b spine -> InstanceGoal telescope b spine
      _ -> developerError $ "Malformed instance goal" <+> prettyVerbose originalValue

mkCandidate :: (DSLExpr builtin, DSLExpr builtin, Bool) -> InstanceCandidate builtin
mkCandidate (expr, solution, defaultInstance) = do
  let p = mempty
  let expr' = fromDSL p expr
  let solution' = fromDSL p solution
  InstanceCandidate expr' solution' defaultInstance

makeInstanceDatabase :: (PrintableBuiltin builtin, Hashable builtin) => [InstanceCandidate builtin] -> HashMap builtin InstanceSearchDepth -> InstanceDatabase builtin
makeInstanceDatabase allInstances searchDepth = do
  let tcAndCandidates = fmap (second (: []) . extractHeadFromInstanceCandidate) allInstances
  let instances = fromListWith (<>) tcAndCandidates
  let defaults = mapMaybeWithKey findDefault instances
  InstanceDatabase instances defaults searchDepth
  where
    findDefault :: (Pretty builtin) => builtin -> [InstanceCandidate builtin] -> Maybe (InstanceCandidate builtin)
    findDefault b instances = do
      let defaultInstances = filter defaultInstance instances
      case defaultInstances of
        [] -> Nothing
        [inst] -> Just inst
        _ -> developerError $ "Multiple default instances found for" <+> quotePretty b
