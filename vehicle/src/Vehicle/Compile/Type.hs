module Vehicle.Compile.Type
  ( typeCheckProg,
    typeCheckSolitaryExpr,
  )
where

import Control.Monad (forM, when)
import Control.Monad.Except (MonadError (..))
import Data.IntSet qualified as IntSet
import Data.List (partition, sortOn)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Proxy (Proxy (..))
import Vehicle.Compile.Context.Free
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Type.Bidirectional
import Vehicle.Compile.Type.Constraint.ApplicationSolver (runApplicationSolver)
import Vehicle.Compile.Type.Constraint.Core (runConstraintSolver)
import Vehicle.Compile.Type.Constraint.InstanceDefaultSolver (addNewInstanceConstraintUsingDefaults)
import Vehicle.Compile.Type.Constraint.InstanceSolver (runInstanceSolver)
import Vehicle.Compile.Type.Constraint.UnificationSolver
import Vehicle.Compile.Type.Core
import Vehicle.Compile.Type.Generalise
import Vehicle.Compile.Type.Meta.Set qualified as MetaSet
import Vehicle.Compile.Type.Meta.Substitution qualified as MetaSubstitution
import Vehicle.Compile.Type.Monad
import Vehicle.Compile.Type.Monad.Class
import Vehicle.Compile.Type.System (HasTypeSystem (..), TCM)
import Vehicle.Data.Builtin.Interface.Normalise (NormalisableBuiltin)
import Vehicle.Data.Builtin.Interface.Print
import Vehicle.Data.Builtin.Interface.Type (TypableBuiltin (..))
import Vehicle.Data.Builtin.Standard
import Vehicle.Data.Code.Value

-------------------------------------------------------------------------------
-- Algorithm

typeCheckProg ::
  forall builtin m.
  (HasTypeSystem builtin, NormalisableBuiltin builtin, MonadCompile m) =>
  InstanceDatabase builtin ->
  FreeCtx builtin ->
  Prog Builtin ->
  m (Prog builtin)
typeCheckProg instanceCandidates freeCtx (Main uncheckedProg) =
  logCompilerPass MinDetail "type checking" $
    runTypeCheckerTInitially freeCtx instanceCandidates $ do
      xs <- typeCheckDecls uncheckedProg
      return $ Main xs

typeCheckSolitaryExpr ::
  forall builtin m.
  (HasTypeSystem builtin, NormalisableBuiltin builtin, MonadCompile m) =>
  InstanceDatabase builtin ->
  FreeCtx builtin ->
  Expr Builtin ->
  m (Expr builtin)
typeCheckSolitaryExpr instanceCandidates freeCtx expr1 = do
  runTypeCheckerTInitially freeCtx instanceCandidates $ do
    expr2 <- convertExprFromStandardTypes expr1
    (expr3, _exprType) <- inferExprType mempty Relevant expr2
    solveConstraints @builtin Nothing
    expr4 <- substMetas expr3
    checkAllUnknownsSolved (Proxy @builtin)
    return expr4

-------------------------------------------------------------------------------
-- Type-class for things that can be type-checked

typeCheckDecls :: forall builtin m. (TCM builtin m) => [Decl Builtin] -> m [Decl builtin]
typeCheckDecls = \case
  [] -> return []
  d : ds -> do
    typedDecl <- typeCheckDecl d
    checkedDecls <- addDeclToContext typedDecl $ typeCheckDecls ds
    return $ typedDecl : checkedDecls

typeCheckDecl :: forall builtin m. (TCM builtin m) => Decl Builtin -> m (Decl builtin)
typeCheckDecl uncheckedDecl =
  logCompilerPass MidDetail ("typing" <+> quotePretty (identifierOf uncheckedDecl)) $ do
    logDebug MidDetail $ prettyExternal uncheckedDecl <> line

    convertedDecl <- traverse convertExprFromStandardTypes uncheckedDecl

    decl <- case convertedDecl of
      DefAbstract p n r t -> typeCheckAbstractDef p n r t
      DefFunction p n b t e -> typeCheckFunction p n b t e

    checkAllUnknownsSolved (Proxy @builtin)
    finalDecl <- substMetas decl
    logCompilerPassOutput $ prettyFriendly finalDecl

    return finalDecl

convertExprFromStandardTypes ::
  forall builtin m.
  (HasTypeSystem builtin, TCM builtin m) =>
  Expr Builtin ->
  m (Expr builtin)
convertExprFromStandardTypes = traverseBuiltinsM convertFromStandardBuiltins

typeCheckAbstractDef ::
  (TCM builtin m) =>
  Provenance ->
  Identifier ->
  DefAbstractSort ->
  Type builtin ->
  m (Decl builtin)
typeCheckAbstractDef p ident defSort uncheckedType = do
  checkedType <- checkDeclType ident uncheckedType
  finalCheckedType <- restrictAbstractDefType defSort (ident, p) checkedType
  let checkedDecl = DefAbstract p ident defSort finalCheckedType

  solveConstraints (Just checkedDecl)
  substCheckedType <- substMetas finalCheckedType

  let substDecl = DefAbstract p ident defSort substCheckedType

  logUnsolvedUnknowns (Just substDecl)

  finalDecl <- generaliseOverUnsolvedMetaVariables substDecl
  return finalDecl

typeCheckFunction ::
  forall builtin m.
  (TCM builtin m) =>
  Provenance ->
  Identifier ->
  [Annotation] ->
  Type builtin ->
  Expr builtin ->
  m (Decl builtin)
typeCheckFunction p ident anns typ body = do
  checkedType <- checkDeclType ident typ
  finalCheckedType <-
    if isProperty anns
      then restrictDeclType RestrictedProperty (ident, p) checkedType
      else return checkedType

  -- Type check the body.
  let pass = bidirectionalPassDoc <+> "body of" <+> quotePretty ident
  checkedBody <-
    logCompilerPass MidDetail pass $
      checkExprType mempty Relevant finalCheckedType body

  -- Reconstruct the function.
  let checkedDecl = DefFunction p ident anns finalCheckedType checkedBody

  -- Solve constraints and substitute through.
  solveConstraints (Just checkedDecl)
  substDecl <- substMetas checkedDecl

  if isProperty anns
    then return substDecl
    else do
      -- Otherwise if not a property then generalise over unsolved meta-variables.
      checkedDecl1 <-
        if isUserIdent ident
          then addAuxiliaryInputOutputConstraints substDecl
          else return substDecl
      logUnsolvedUnknowns (Just substDecl)

      checkedDecl2 <- generaliseOverUnsolvedConstraints checkedDecl1
      checkedDecl3 <- generaliseOverUnsolvedMetaVariables checkedDecl2
      return checkedDecl3

checkDeclType :: forall builtin m. (TCM builtin m) => Identifier -> Expr builtin -> m (Type builtin)
checkDeclType ident declType = do
  let pass = bidirectionalPassDoc <+> "type of" <+> quotePretty ident
  logCompilerPass MidDetail pass $ do
    checkExprType mempty Relevant (TypeUniverse mempty 0) declType

restrictAbstractDefType ::
  (TCM builtin m) =>
  DefAbstractSort ->
  DeclProvenance ->
  Type builtin ->
  m (Type builtin)
restrictAbstractDefType resource decl@(ident, _) defType = do
  let resourceName = pretty resource <+> quotePretty ident
  logCompilerPass MidDetail ("checking suitability of the type of" <+> resourceName) $ do
    case resource of
      ParameterDef sort -> restrictDeclType (RestrictedParameter sort) decl defType
      DatasetDef -> restrictDeclType RestrictedDataset decl defType
      NetworkDef -> restrictDeclType RestrictedNetwork decl defType
      PostulateDef {} -> return defType

-------------------------------------------------------------------------------
-- Constraint solving

-- | Tries to solve constraints. Passes in the type of the current declaration
-- being checked, as metas are handled different according to whether they
-- occur in the type or not.
solveConstraints :: forall builtin m. (TCM builtin m) => Maybe (Decl builtin) -> m ()
solveConstraints d = logCompilerPass MidDetail "constraint solving" $ do
  sortConstraints
  loopOverConstraints 1 d
  where
    sortConstraints :: m ()
    sortConstraints = do
      -- We try and priortise resolving the cast constraints first (e.g. HasTensor, IsNatLiteral)
      -- as it produces far better error messages for the user.
      instanceConstraints <- getActiveInstanceConstraints @builtin
      let sortedInstanceConstraints = sortOn (not . isCastConstraint . goalHead . instanceGoal . objectIn) instanceConstraints
      setInstanceConstraints sortedInstanceConstraints

    loopOverConstraints :: (TCM builtin m) => Int -> Maybe (Decl builtin) -> m ()
    loopOverConstraints loopNumber decl = do
      updatedDecl <- traverse substMetas decl
      logUnsolvedUnknowns updatedDecl

      -- Try to solve the constraints pass
      oldConstraintIDS <- getActiveConstraintIDs (Proxy @builtin)
      logCompilerPass MaxDetail ("constraint solving pass" <+> pretty loopNumber) $
        runSolvers updatedDecl
      newConstraintIDS <- getActiveConstraintIDs (Proxy @builtin)

      if IntSet.null newConstraintIDS
        then return ()
        else
          if newConstraintIDS /= oldConstraintIDS
            then loopOverConstraints (loopNumber + 1) updatedDecl
            else do
              -- If no constraints are unblocked then try generating new constraints using defaults.
              logDebug MaxDetail $ "Temporarily stuck" <> line
              success <- tryToUnstick updatedDecl
              when success $
                -- If new constraints generated then continue solving.
                loopOverConstraints (loopNumber + 1) decl

    runSolvers :: (TCM builtin m) => Maybe (Decl builtin) -> m ()
    runSolvers maybeDecl = do
      let proxy = Proxy @builtin
      runApplicationSolver proxy

      logUnsolvedUnknowns maybeDecl
      runUnificationSolver proxy

      logUnsolvedUnknowns maybeDecl
      runInstanceSolver proxy 0

      logUnsolvedUnknowns maybeDecl
      runAuxiliarySolver proxy

      logUnsolvedUnknowns maybeDecl

    tryToUnstick :: (TCM builtin m) => Maybe (Decl builtin) -> m Bool
    tryToUnstick decl = do
      -- First try to increase the depth limit for instance search
      solvedMetas <- logCompilerPass MidDetail "trying to increase the depth for instance search" $ do
        trackSolvedMetas (Proxy @builtin) $ runInstanceSolver (Proxy @builtin) 1

      if not (MetaSet.null solvedMetas)
        then return True
        else do
          -- Then if that fails try to use default instances
          success <- logCompilerPass MidDetail "trying to generate a new constraint using instance defaults" $ do
            addNewInstanceConstraintUsingDefaults decl

          if success
            then return True
            else logCompilerPass MidDetail "trying to generate a new constraint using instance defaults" $ do
              -- Then if that fails try to use default auxiliary instances
              generateDefaultAuxiliaryConstraint decl

-- | Attempts to solve as many type-class constraints as possible.
runAuxiliarySolver :: forall builtin m. (TCM builtin m) => Proxy builtin -> m ()
runAuxiliarySolver proxy = do
  logCompilerPass MaxDetail ("auxiliary solver run" <> line) $
    runConstraintSolver @builtin
      proxy
      getActiveAuxiliaryInstanceConstraints
      setAuxiliaryInstanceConstraints
      solveAuxiliaryInstanceConstraint

-------------------------------------------------------------------------------
-- Unsolved constraint checks

checkAllUnknownsSolved :: (MonadTypeChecker builtin m) => Proxy builtin -> m ()
checkAllUnknownsSolved proxy = do
  -- First check all user constraints (i.e. unification and type-class
  -- constraints) are solved.
  checkAllConstraintsSolved proxy
  -- Then check all meta-variables have been solved.
  checkAllMetasSolved proxy
  -- Then clear the meta-ctx
  clearMetaCtx proxy
  -- ...and the fresh names
  clearFreshNames proxy

checkAllConstraintsSolved :: forall builtin m. (MonadTypeChecker builtin m) => Proxy builtin -> m ()
checkAllConstraintsSolved _ = do
  constraints <- getActiveConstraints @builtin
  case constraints of
    [] -> return ()
    (c : cs) -> throwError $ TypingError $ UnsolvedConstraints (c :| cs)

checkAllMetasSolved :: forall builtin m. (MonadTypeChecker builtin m) => Proxy builtin -> m ()
checkAllMetasSolved proxy = do
  unsolvedMetas <- getUnsolvedMetas proxy
  case MetaSet.toList unsolvedMetas of
    [] -> return ()
    m : ms -> do
      metasAndOrigins <-
        forM
          (m :| ms)
          ( \meta -> do
              origin <- getMetaProvenance proxy meta
              return (meta, origin)
          )
      throwError $ TypingError $ UnsolvedMetas proxy metasAndOrigins

logUnsolvedUnknowns :: forall builtin m. (TCM builtin m) => Maybe (Decl builtin) -> m ()
logUnsolvedUnknowns maybeDecl = do
  logDebugM MaxDetail $ do
    newSubstitution <- getMetaSubstitution (Proxy @builtin)
    updatedSubst <- substMetas newSubstitution

    unsolvedMetas <- getUnsolvedMetas (Proxy @builtin)
    unsolvedMetasDoc <- prettyMetas (Proxy @builtin) unsolvedMetas
    unsolvedConstraints <- getActiveConstraints @builtin

    isUnblocked <- getIsUnblockedFn
    let (unblockedConstraints, blockedConstraints) = partition isUnblocked unsolvedConstraints
    let constraintsDoc =
          "unsolved-blocked-constraints:"
            <> line
            <> indent 2 (prettyConstraints blockedConstraints)
            <> line
            <> "unsolved-unblocked-constraints:"
            <> line
            <> indent 2 (prettyConstraints unblockedConstraints)
            <> line

    updatedDecl <- traverse (MetaSubstitution.subst updatedSubst) maybeDecl
    let declDoc = case updatedDecl of
          Nothing -> ""
          Just decl ->
            "current-decl:"
              <> line
              <> indent 2 (prettyExternal decl)
              <> line

    return $
      "current-solution:"
        <> line
        <> indent 2 (prettyVerbose (fmap unnormalised updatedSubst))
        <> line
        <> "unsolved-metas:"
        <> line
        <> indent 2 unsolvedMetasDoc
        <> line
        <> constraintsDoc
        <> declDoc

prettyConstraints :: (PrintableBuiltin builtin) => [WithContext (Constraint builtin)] -> Doc a
prettyConstraints constraints = do
  let sortedConstraints = sortOn (constraintID . contextOf) constraints
  let pairs = fmap (\c -> prettyExternal c <> "   " <> pretty (blockedBy $ contextOf c)) sortedConstraints
  prettySetLike pairs

bidirectionalPassDoc :: Doc a
bidirectionalPassDoc = "bidirectional pass over"
