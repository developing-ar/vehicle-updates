module Vehicle.Compile.Normalise.Builtin where

import Vehicle.Compile.Context.Free.Class (MonadFreeContext)
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print.Builtin
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Interface (BuiltinHasStandardData (..))
import Vehicle.Data.Builtin.Linearity (LinearityBuiltin (..))
import Vehicle.Data.Builtin.Loss (LossBuiltin (..))
import Vehicle.Data.Builtin.Loss qualified as L
import Vehicle.Data.Builtin.Polarity (PolarityBuiltin (..))
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.TypedView
import Vehicle.Data.Code.Value
import Vehicle.Data.Tensor (Tensor, at, foldTensor, stack, zipWithTensor, pattern ConstantTensor, pattern ZeroDimTensor)
import Vehicle.Libraries.StandardLibrary.Definitions (StdLibFunction (StdAppendList))

-- Okay so the important thing to remember about this module is that we have
-- a variety of different typing schemes for builtins (standard, polarity,
-- linearity etc.). Normalisation needs to work for all of these, and
-- therefore we can't guarantee what the implicit and instance arguments are
-- going to be for a given builtin. However, explicit arguments are always
-- the same in every type system.

-- Therefore this can be viewed as a type of runtime irrelevance, where only
-- the explicit arguments are runtime relevant. This notion isn't made
-- explicit in the code below. Maybe there's a nice way of doing so?

-----------------------------------------------------------------------------
-- Main method

-- | Type signature for the most generic method of evaluating a builtin
-- application. Crucially it takes both the method of evaluating an expression
-- and the unnormalised arguments, because it needs to be able to support
-- the non-compositional normalisation, e.g. translation to Loss functions
-- as the DL2 translation of `not` isn't compositional and therefore we
-- need access the unnormalised form of the arguments.
--
-- This can't be a type-class because it's not type directed. Different
-- Differential logics all normalise to the same type but have different
-- methods of normalisation.
type EvalBuiltinApp m builtin =
  (MonadLogger m, MonadFreeContext builtin m) =>
  EvalApp (Value builtin) m ->
  Eval builtin m ->
  builtin ->
  [Arg builtin] ->
  m (Value builtin)

type Eval builtin m =
  (MonadLogger m) =>
  Expr builtin ->
  m (Value builtin)

findInstanceArg :: (MonadLogger m, Show op) => op -> [GenericArg a] -> m (a, [GenericArg a])
findInstanceArg op = \case
  (InstanceArg _ _ inst : xs) -> return (inst, xs)
  (_ : xs) -> findInstanceArg op xs
  [] -> developerError $ "Malformed type class operation:" <+> pretty (show op)

filterOutIrrelevantArgs :: [GenericArg expr] -> [GenericArg expr]
filterOutIrrelevantArgs = filter isRelevant

-----------------------------------------------------------------------------
-- Builtin evaluation

-- | A method for evaluating an application.
-- Although there is only one implementation of this type, it needs to be
-- passed around as an argument to avoid dependency cycles between
-- this module and the module in which the general NBE algorithm lives in.
type EvalApp expr m = expr -> [GenericArg expr] -> m expr

--------------------------------------------------------------------------------
-- Evaluation

-- | A method for evaluating builtins that takes in an argument allowing the
-- recursive evaluation of applications. that takes in an argument allowing
-- the subsequent further evaluation of applications.
-- Such recursive evaluation is necessary when evaluating higher order
-- functions such as fold, map etc.
type EvalBuiltin expr m =
  (MonadLogger m) =>
  EvalApp expr m ->
  expr ->
  [GenericArg expr] ->
  m expr

type EvalSimpleBuiltin expr =
  expr ->
  [GenericArg expr] ->
  expr

evalOp1 ::
  (expr -> Maybe a) ->
  (a -> b) ->
  (b -> expr) ->
  EvalSimpleBuiltin expr
evalOp1 getArg op mkResult originalExpr = \case
  [argExpr -> (getArg -> Just x)] -> mkResult (op x)
  _ -> originalExpr

evalOp2 ::
  (expr -> Maybe a) ->
  (expr -> Maybe b) ->
  (a -> b -> c) ->
  (c -> expr) ->
  EvalSimpleBuiltin expr
evalOp2 getArg1 getArg2 op mkResult originalExpr = \case
  [argExpr -> (getArg1 -> Just x), argExpr -> (getArg2 -> Just y)] -> mkResult (op x y)
  _ -> originalExpr

evalReduceTensor ::
  (expr -> Maybe (Tensor a)) ->
  (Tensor a -> Tensor a -> Tensor a) ->
  (Tensor a -> expr) ->
  EvalSimpleBuiltin expr
evalReduceTensor getTensor f mkTensor originalExpr = \case
  [argExpr -> (getTensor -> Just e), argExpr -> (getTensor -> Just t)] ->
    mkTensor $ foldTensor f e t
  _ -> originalExpr

-----------------------------------------------------------------------------
-- Individual builtin evaluation
-----------------------------------------------------------------------------
-- Bool

evalNotBoolTensor :: (HasBoolLits expr) => EvalSimpleBuiltin expr
evalNotBoolTensor = evalOp1 getBoolTensorLit (fmap not) mkBoolTensorLit

evalAndBoolTensor :: (HasBoolLits expr) => EvalSimpleBuiltin expr
evalAndBoolTensor originalExpr = \case
  [argExpr -> e1, argExpr -> e2] -> case (e1, e2) of
    (IBoolTensor x, IBoolTensor y) -> IBoolTensor $ zipWithTensor (&&) x y
    (IBoolConstTensor (IBoolLiteral b) _, _) -> if b then e2 else e1
    (_, IBoolConstTensor (IBoolLiteral b) _) -> if b then e1 else e2
    _ -> originalExpr
  _ -> originalExpr

evalOrBoolTensor :: (HasBoolLits expr) => EvalSimpleBuiltin expr
evalOrBoolTensor originalExpr = \case
  [argExpr -> e1, argExpr -> e2] -> case (e1, e2) of
    (IBoolTensor x, IBoolTensor y) -> IBoolTensor $ zipWithTensor (||) x y
    (IBoolConstTensor (IBoolLiteral b) _, _) -> if b then e1 else e2
    (_, IBoolConstTensor (IBoolLiteral b) _) -> if b then e2 else e1
    _ -> originalExpr
  _ -> originalExpr

evalImplies :: (HasBoolLits expr) => EvalSimpleBuiltin expr
evalImplies originalExpr = \case
  [argExpr -> e1, argExpr -> e2] -> case (e1, e2) of
    (IBoolTensor x, IBoolTensor y) -> IBoolTensor $ zipWithTensor (\u v -> not u && v) x y
    _ -> originalExpr
  _ -> originalExpr

evalIf :: (HasBoolLits expr) => EvalSimpleBuiltin expr
evalIf originalExpr = \case
  [argExpr -> IBoolLiteral True, e1, _e2] -> argExpr e1
  [argExpr -> IBoolLiteral False, _e1, e2] -> argExpr e2
  _ -> originalExpr

-----------------------------------------------------------------------------
-- Index

evalOrderIndex :: (HasBoolLits expr, HasIndexLits expr) => OrderOp -> EvalSimpleBuiltin expr
evalOrderIndex op originalExpr = \case
  [_, _, argExpr -> IIndexLiteral x, argExpr -> IIndexLiteral y] -> IBoolLiteral (orderOp op x y)
  _ -> originalExpr

evalEqualsIndex :: (HasBoolLits expr, HasIndexLits expr) => EqualityOp -> EvalSimpleBuiltin expr
evalEqualsIndex op originalExpr = \case
  [_, _, argExpr -> IIndexLiteral x, argExpr -> IIndexLiteral y] -> IBoolLiteral (equalityOp op x y)
  _ -> originalExpr

-----------------------------------------------------------------------------
-- Nat

evalAddNat :: (HasNatLits expr) => EvalSimpleBuiltin expr
evalAddNat = evalOp2 getNatLit getNatLit (+) mkNatLit

evalMulNat :: (HasNatLits expr) => EvalSimpleBuiltin expr
evalMulNat = evalOp2 getNatLit getNatLit (*) mkNatLit

evalOrderNat :: (HasBoolLits expr, HasNatLits expr) => OrderOp -> EvalSimpleBuiltin expr
evalOrderNat op = evalOp2 getNatLit getNatLit (orderOp op) IBoolLiteral

evalEqualsNat :: (HasBoolLits expr, HasNatLits expr) => EqualityOp -> EvalSimpleBuiltin expr
evalEqualsNat op = evalOp2 getNatLit getNatLit (equalityOp op) IBoolLiteral

evalFromNatToIndex :: (HasIndexLits expr, HasNatLits expr) => EvalSimpleBuiltin expr
evalFromNatToIndex = evalOp1 getNatLit id mkIndexLit

-----------------------------------------------------------------------------
-- Rat

evalFromNatToNat :: EvalSimpleBuiltin expr
evalFromNatToNat originalExpr = \case
  [argExpr -> x] -> x
  _ -> originalExpr

evalFromNatToRat :: (HasRatLits expr, HasNatLits expr) => EvalSimpleBuiltin expr
evalFromNatToRat = evalOp1 getNatLit fromIntegral IRatLiteral

evalFromRatToRat :: EvalSimpleBuiltin expr
evalFromRatToRat originalExpr = \case
  [argExpr -> x] -> x
  _ -> originalExpr

evalVectorToList :: (HasNatLits expr, HasStandardListLits expr) => EvalSimpleBuiltin expr
evalVectorToList originalExpr = \case
  (argExpr -> INatLiteral d) : (argExpr -> t) : xs
    | d /= length xs -> originalExpr
    | otherwise -> mkListExpr t (fmap argExpr xs)
  _ -> originalExpr

-----------------------------------------------------------------------------
-- From here on, these only work for standard typing systems with implicit
-- arguments in the format expected by the standard typing system, as
-- otherwise we can't reconstruct the MapList and FoldList with the right
-- typing arguments.
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- List

evalMapList :: (HasStandardListLits expr) => ([GenericArg expr] -> expr) -> EvalBuiltin expr m
evalMapList mkMapList evalApp originalExpr = \case
  [_a, b, _f, argExpr -> INil _] -> return $ INil b
  [a, b, f, argExpr -> ICons _ x xs] -> do
    fx <- evalApp (argExpr f) [x]
    let defaultMap = mkMapList [a, b, f, xs]
    fxs <- evalMapList mkMapList evalApp defaultMap [a, b, f, xs]
    return $ ICons b (explicit fx) (explicit fxs)
  _ -> return originalExpr

evalFoldList :: EvalBuiltin (Value Builtin) m
evalFoldList evalApp originalExpr args =
  case args of
    [_a, _b, _f, e, argExpr -> INil _] -> return $ argExpr e
    [a, b, f, e, argExpr -> ICons _ x xs] -> do
      let defaultFold = VBuiltin (BuiltinFunction FoldList) [a, b, f, e, xs]
      r <- evalFoldList evalApp defaultFold [a, b, f, e, xs]
      evalApp (argExpr f) [x, explicit r]
    _ -> return originalExpr

-----------------------------------------------------------------------------
-- Vector

{-
evalIndices :: (HasStandardVecLits expr, HasIndexLits expr, HasNatLits expr) => ([GenericArg expr] -> expr) -> EvalSimpleBuiltin expr
evalIndices mkIndexType originalExpr = \case
  [size@(argExpr -> INatLiteral n)] -> do
    let t = implicit (mkIndexType [size])
    let xs = fmap (explicit . IIndexLiteral) ([0 .. n - 1] :: [Int])
    IVecLiteral t xs
  _ -> originalExpr

case c of
  IVecLiteral {} -> do
    i' <- unblockNonVector actions i
    liftIf i' $ \i'' -> do
      forceEvalSimple At evalAt [t, n, explicit c, explicit i'']
  IMapVector _ _ t2 f xs -> appAt f [(t2, n, xs)] i
  IZipWithVector t1 t2 _ _ f xs ys -> appAt f [(t1, n, xs), (t2, n, ys)] i
  IVectorAdd t1 t2 _ _ f xs ys -> appAt (argExpr f) [(t1, n, xs), (t2, n, ys)] i
  IVectorSub t1 t2 _ _ f xs ys -> appAt (argExpr f) [(t1, n, xs), (t2, n, ys)] i
  _ -> do
    -- Don't reduce vector bound variables in container as it may trigger extremely expensive normalisation
    -- that we can avoid because we're only looking up a single element of it.
    c' <- unblockVector actions (isVBoundVar c) c
    unblockAt actions t n c' i
  where
    appAt ::
      (MonadUnblock m) =>
      Value Builtin ->
      [(VArg Builtin, VArg Builtin, Value Builtin)] ->
      Value Builtin ->
      m (Value Builtin)
    appAt f args index = normaliseApp f =<< traverse (appIndexToArg index) args

    appIndexToArg ::
      (MonadUnblock m) =>
      Value Builtin ->
      (VArg Builtin, VArg Builtin, Value Builtin) ->
      m (VArg Builtin)
    appIndexToArg index (t', n', xs) =
      Arg mempty Explicit Relevant
        <$> unblockAt actions t' n' xs index

evalFoldVector :: (HasStandardVecLits expr) => EvalBuiltin expr m
evalFoldVector evalApp originalExpr args = case args of
  [_, _, argExpr -> f, argExpr -> e, argExpr -> IVecLiteral _t xs] -> foldrM f' e xs
    where
      f' x r = evalApp f [x, explicit r]
  _ -> return originalExpr

evalZipWith :: (HasStandardVecLits expr) => EvalBuiltin expr m
evalZipWith evalApp originalExpr = \case
  [_, _, c, argExpr -> f, argExpr -> IVecLiteral _t1 xs, argExpr -> IVecLiteral _t2 ys] ->
    IVecLiteral c <$> zipWithM f' xs ys
    where
      f' x y = explicit <$> evalApp f [x, y]
  _ -> return originalExpr

evalMapVector :: (HasStandardVecLits expr) => EvalBuiltin expr m
evalMapVector evalApp originalExpr = \case
  [_, b, argExpr -> f, argExpr -> IVecLiteral _t1 xs] ->
    IVecLiteral b <$> traverse f' xs
    where
      f' x = explicit <$> evalApp f [x]
  _ -> return originalExpr
-}
-----------------------------------------------------------------------------
-- Rational tensors

evalRatTensorOp1 :: (HasRatLits expr) => (Rational -> Rational) -> EvalSimpleBuiltin expr
evalRatTensorOp1 op = evalOp1 getRatTensorLit (fmap op) mkRatTensorLit

evalRatTensorOp2 :: (HasRatLits expr) => (Rational -> Rational -> Rational) -> EvalSimpleBuiltin expr
evalRatTensorOp2 op = evalOp2 getRatTensorLit getRatTensorLit (zipWithTensor op) mkRatTensorLit

evalReduceRatTensor :: (HasRatLits expr) => (Tensor Rational -> Tensor Rational -> Tensor Rational) -> EvalSimpleBuiltin expr
evalReduceRatTensor f = evalReduceTensor getRatTensorLit f mkRatTensorLit

evalAddRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalAddRatTensor originalExpr = \case
  [argExpr -> e1, argExpr -> e2] -> case (e1, e2) of
    (IRatTensor x, IRatTensor y) -> IRatTensor $ zipWithTensor (+) x y
    (IRatConstTensor (IRatLiteral r) _, _) | r == 0 -> e2
    (_, IRatConstTensor (IRatLiteral r) _) | r == 0 -> e1
    _ -> originalExpr
  _ -> originalExpr

evalMulRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalMulRatTensor originalExpr = \case
  [argExpr -> e1, argExpr -> e2] -> case (e1, e2) of
    (IRatTensor x, IRatTensor y) -> IRatTensor $ zipWithTensor (*) x y
    (IRatConstTensor (IRatLiteral r) _, _) | r == 1 -> e2
    (_, IRatConstTensor (IRatLiteral r) _) | r == 1 -> e1
    _ -> originalExpr
  _ -> originalExpr

evalNegRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalNegRatTensor = evalRatTensorOp1 (\x -> -x)

evalSubRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalSubRatTensor = evalRatTensorOp2 (/)

evalDivRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalDivRatTensor = evalRatTensorOp2 (/)

evalMinRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalMinRatTensor = evalRatTensorOp2 min

evalMaxRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalMaxRatTensor = evalRatTensorOp2 max

evalPowRat :: (HasNatLits expr, HasRatLits expr) => EvalSimpleBuiltin expr
evalPowRat = evalOp2 getRatTensorLit getNatLit (\t n -> fmap (^^ n) t) IRatTensor

evalReduceAddRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalReduceAddRatTensor = evalReduceRatTensor (zipWithTensor (+))

evalReduceMulRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalReduceMulRatTensor = evalReduceRatTensor (zipWithTensor (*))

evalReduceMinRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalReduceMinRatTensor = evalReduceRatTensor (zipWithTensor min)

evalReduceMaxRatTensor :: (HasRatLits expr) => EvalSimpleBuiltin expr
evalReduceMaxRatTensor = evalReduceRatTensor (zipWithTensor max)

evalEqualityRatTensor :: (HasBoolLits expr, HasRatLits expr) => EqualityOp -> EvalSimpleBuiltin expr
evalEqualityRatTensor op = evalOp2 getRatTensorLit getRatTensorLit (zipWithTensor (equalityOp op)) mkBoolTensorLit

evalOrderRatTensor :: (HasBoolLits expr, HasRatLits expr) => OrderOp -> EvalSimpleBuiltin expr
evalOrderRatTensor op = evalOp2 getRatTensorLit getRatTensorLit (zipWithTensor (orderOp op)) mkBoolTensorLit

evalReduceAndTensor :: (HasBoolLits expr) => EvalSimpleBuiltin expr
evalReduceAndTensor = evalReduceTensor getBoolTensorLit (zipWithTensor (&&)) mkBoolTensorLit

evalReduceOrTensor :: (HasBoolLits expr) => EvalSimpleBuiltin expr
evalReduceOrTensor = evalReduceTensor getBoolTensorLit (zipWithTensor (||)) mkBoolTensorLit

-----------------------------------------------------------------------------
-- Generic tensor operations

data PrimitiveTensor expr = forall a. (Eq a) => PrimitiveTensor
  { getTensor :: expr -> Maybe (Tensor a),
    mkTensor :: Tensor a -> expr
  }

primitiveBoolTensor :: (HasBoolLits expr) => PrimitiveTensor expr
primitiveBoolTensor =
  PrimitiveTensor
    { getTensor = getBoolTensorLit,
      mkTensor = mkBoolTensorLit
    }

primitiveRatTensor :: (HasRatLits expr) => PrimitiveTensor expr
primitiveRatTensor =
  PrimitiveTensor
    { getTensor = getRatTensorLit,
      mkTensor = mkRatTensorLit
    }

class HasPrimitives expr where
  primitives :: [PrimitiveTensor expr]

instance HasPrimitives (Value Builtin) where
  primitives = [primitiveBoolTensor, primitiveRatTensor]

instance HasPrimitives (Value LossBuiltin) where
  primitives = [primitiveRatTensor]

evalAt :: (HasPrimitives expr, HasIndexLits expr) => EvalSimpleBuiltin expr
evalAt originalExpr args = case args of
  [_, _, argExpr -> t, argExpr -> IIndexLiteral i] -> go originalExpr t i primitives
  _ -> originalExpr
  where
    go :: expr -> expr -> Int -> [PrimitiveTensor expr] -> expr
    go original tensor i = \case
      [] -> original
      PrimitiveTensor {..} : prims -> case getTensor tensor of
        Just t -> mkTensor (t `at` i)
        Nothing -> go original tensor i prims

evalStackTensor :: (HasPrimitives expr, HasNatLits expr, HasStandardListLits expr) => EvalSimpleBuiltin expr
evalStackTensor originalExpr = \case
  (argExpr -> INatLiteral n) : ds : _t : args
    | length args /= n -> originalExpr
    | otherwise -> do
        let exprs = fmap argExpr args
        -- If we know that all the tensors being stacked are concrete tensors, then
        -- we must know the dimensions as well.
        let dims = case getDims (argExpr ds) of
              Nothing -> developerError "Non-concrete dimensions for concrete tensor literals"
              Just r -> r
        go originalExpr dims exprs primitives
  _ -> originalExpr
  where
    go :: expr -> [Int] -> [expr] -> [PrimitiveTensor expr] -> expr
    go original elemDims args = \case
      [] -> original
      PrimitiveTensor {..} : prims -> case traverse getTensor args of
        Just xss -> mkTensor $ stack elemDims xss
        Nothing -> go original elemDims args prims

evalConstTensor :: (HasPrimitives expr, HasNatLits expr, HasStandardListLits expr) => EvalSimpleBuiltin expr
evalConstTensor originalExpr = \case
  -- Pattern matching on ds here is technically a bug as blocking will not
  -- function correctly. However, to fix it we would need to go via `StackTensor`
  -- and in particular make `StackTensor` take the size argument as an expression.
  -- Our type-system can't handle that easily yet.
  [_tElem, argExpr -> tensorExpr, getDims . argExpr -> Just dims] -> go originalExpr tensorExpr dims primitives
  _ -> originalExpr
  where
    go :: expr -> expr -> [Int] -> [PrimitiveTensor expr] -> expr
    go original tensorExpr dims = \case
      [] -> original
      PrimitiveTensor {..} : prims -> case getTensor tensorExpr of
        Just t -> case t of
          ZeroDimTensor v -> mkTensor $ ConstantTensor dims v
          _ -> developerError "Non-zero dimensional tensor argument for ConstTensor"
        Nothing -> go original tensorExpr dims prims

evalForeach :: EvalBuiltin (Value Builtin) m
evalForeach evalApp originalExpr = \case
  [tElem, d@(argExpr -> INatLiteral n), ds, argExpr -> f] -> do
    xs <- traverse (\i -> evalApp f [explicit (IIndexLiteral i)]) [0 .. (n - 1 :: Int)]
    let args = d : ds : tElem : fmap explicit xs
    let newExpr = VBuiltin (BuiltinFunction StackTensor) args
    return $ evalStackTensor newExpr args
  _ -> return originalExpr

evalIterate :: forall m expr. (HasNatLits expr) => ([GenericArg expr] -> expr) -> EvalBuiltin expr m
evalIterate mkIterate evalApp originalExpr = \case
  (t : f : (argExpr -> INatLiteral n) : e : _) -> case n of
    0 -> return $ argExpr e
    _ -> evalApp (argExpr f) [explicit (mkIterate [t, f, explicit (INatLiteral (n - 1))]), e]
  _ -> return originalExpr

-----------------------------------------------------------------------------
-- Blocking arguments

data BlockingArgs
  = Unknown
  | Known [Int]

noBlockingArgs :: BlockingArgs
noBlockingArgs = Known []

blockingArgsNot :: BlockingArgs
blockingArgsNot = Known [1]

blockingArgsAnd :: BlockingArgs
blockingArgsAnd = Known [1, 2]

blockingArgsOr :: BlockingArgs
blockingArgsOr = Known [1, 2]

blockingArgsNeg :: NegDomain -> BlockingArgs
blockingArgsNeg = \case
  NegRatTensor -> Known [1]

blockingArgsAdd :: AddDomain -> BlockingArgs
blockingArgsAdd = \case
  AddNat -> Known [0, 1]
  AddRatTensor -> Known [1, 2]

blockingArgsMul :: MulDomain -> BlockingArgs
blockingArgsMul = \case
  MulNat -> Known [0, 1]
  MulRatTensor -> Known [1, 2]

blockingArgsSub :: SubDomain -> BlockingArgs
blockingArgsSub = \case
  SubRatTensor -> Known [1, 2]

blockingArgsDiv :: DivDomain -> BlockingArgs
blockingArgsDiv = \case
  DivRatTensor -> Known [1, 2]

blockingArgsMin :: MinDomain -> BlockingArgs
blockingArgsMin = \case
  MinRatTensor -> Known [1, 2]

blockingArgsMax :: MaxDomain -> BlockingArgs
blockingArgsMax = \case
  MaxRatTensor -> Known [1, 2]

blockingArgsEquals :: EqualityDomain -> BlockingArgs
blockingArgsEquals = \case
  EqIndex -> Known [2, 3]
  EqNat -> Known [0, 1]
  EqRatTensor -> Known [1, 2]

blockingArgsOrder :: OrderDomain -> BlockingArgs
blockingArgsOrder = \case
  OrderIndex -> Known [2, 3]
  OrderNat -> Known [0, 1]
  OrderRatTensor -> Known [1, 2]

functionBlockingArgs :: BuiltinFunction -> BlockingArgs
functionBlockingArgs = \case
  QuantifyRatTensor {} -> noBlockingArgs
  Not -> blockingArgsNot
  And -> blockingArgsAnd
  Or -> blockingArgsOr
  Neg dom -> blockingArgsNeg dom
  Add dom -> blockingArgsAdd dom
  Sub dom -> blockingArgsSub dom
  Mul dom -> blockingArgsMul dom
  Div dom -> blockingArgsDiv dom
  Min dom -> blockingArgsMin dom
  Max dom -> blockingArgsMax dom
  PowRat -> Known [0, 1]
  Equals dom _op -> blockingArgsEquals dom
  Order dom _op -> blockingArgsOrder dom
  FromNat FromNatToIndex -> Known [1]
  FromNat FromNatToNat -> noBlockingArgs
  FromNat FromNatToRat -> Known [0]
  FromRat FromRatToRat -> noBlockingArgs
  If -> Known [1]
  At -> Known [3, 4]
  FoldList -> Known [4]
  MapList -> Known [3]
  Implies -> noBlockingArgs
  ConstTensor -> Known [0, 1]
  ReduceAddRatTensor -> Known [1]
  ReduceMulRatTensor -> Known [1]
  ReduceMinRatTensor -> Known [1]
  ReduceMaxRatTensor -> Known [1]
  ReduceOrTensor -> Known [1]
  ReduceAndTensor -> Known [1]
  Foreach -> Known [1]
  Iterate -> Known [2]
  StackTensor -> Unknown
  FromVectorToList -> Known [0]
  FlattenTensorType -> Known [0]

-----------------------------------------------------------------------------
-- Type-class
-----------------------------------------------------------------------------

-- | A type-class for builtins that can be normalised compositionally.
class (PrintableBuiltin builtin) => NormalisableBuiltin builtin where
  -- This function takes in the original expression (containing both relevant
  -- and irrelevant arguments), the builtin that is in the head position
  -- and the list of computationally relevant arguments.
  evalBuiltinApp ::
    (MonadLogger m) =>
    EvalApp (Value builtin) m ->
    FreeEnv builtin ->
    Value builtin ->
    builtin ->
    Spine builtin ->
    m (Value builtin)

  blockingArgs ::
    builtin ->
    BlockingArgs

-----------------------------------------------------------------------------
-- Eval domains

evalEquals :: (HasBoolLits expr, HasIndexLits expr, HasNatLits expr, HasRatLits expr) => EqualityDomain -> EqualityOp -> EvalSimpleBuiltin expr
evalEquals = \case
  EqIndex -> evalEqualsIndex
  EqNat -> evalEqualsNat
  EqRatTensor -> evalEqualityRatTensor

evalOrder :: (HasBoolLits expr, HasIndexLits expr, HasNatLits expr, HasRatLits expr) => OrderDomain -> OrderOp -> EvalSimpleBuiltin expr
evalOrder = \case
  OrderIndex -> evalOrderIndex
  OrderNat -> evalOrderNat
  OrderRatTensor -> evalOrderRatTensor

evalNot :: (HasBoolLits expr) => EvalSimpleBuiltin expr
evalNot = evalNotBoolTensor

evalAnd :: (HasBoolLits expr) => EvalSimpleBuiltin expr
evalAnd = evalAndBoolTensor

evalOr :: (HasBoolLits expr) => EvalSimpleBuiltin expr
evalOr = evalOrBoolTensor

evalNeg :: (HasRatLits expr) => NegDomain -> EvalSimpleBuiltin expr
evalNeg = \case
  NegRatTensor -> evalNegRatTensor

evalAdd :: (HasRatLits expr, HasNatLits expr) => AddDomain -> EvalSimpleBuiltin expr
evalAdd = \case
  AddNat -> evalAddNat
  AddRatTensor -> evalAddRatTensor

evalSub :: (HasRatLits expr) => SubDomain -> EvalSimpleBuiltin expr
evalSub = \case
  SubRatTensor -> evalSubRatTensor

evalMul :: (HasRatLits expr, HasNatLits expr) => MulDomain -> EvalSimpleBuiltin expr
evalMul = \case
  MulNat -> evalMulNat
  MulRatTensor -> evalMulRatTensor

evalDiv :: (HasRatLits expr) => DivDomain -> EvalSimpleBuiltin expr
evalDiv = \case
  DivRatTensor -> evalDivRatTensor

evalMin :: (HasRatLits expr) => MinDomain -> EvalSimpleBuiltin expr
evalMin = \case
  MinRatTensor -> evalMinRatTensor

evalMax :: (HasRatLits expr) => MaxDomain -> EvalSimpleBuiltin expr
evalMax = \case
  MaxRatTensor -> evalMaxRatTensor

evalFlattenTensorType :: FreeEnv Builtin -> EvalBuiltin (Value Builtin) m
evalFlattenTensorType freeEnv evalApp originalExpr = \case
  [argExpr -> t, argExpr -> dims] -> case t of
    ITensorType tElem dims2 -> do
      -- appendList : List A -> List A -> List A
      -- appendList xs ys = fold (\x y -> x :: y) ys xs
      let appendList = lookupIdentValueInEnv freeEnv (identifierOf StdAppendList)
      let args = [implicit INatType, explicit dims2, explicit dims]
      newDims <- evalApp appendList args
      return $ ITensorType tElem newDims
    IBoolType -> return $ ITensorType t dims
    INatType -> return $ ITensorType t dims
    IRatType -> return $ ITensorType t dims
    _ -> return originalExpr
  _ -> return originalExpr

evalBuiltinFunction :: FreeEnv Builtin -> BuiltinFunction -> EvalBuiltin (Value Builtin) m
evalBuiltinFunction freeEnv b evalApp originalValue args = case b of
  QuantifyRatTensor {} -> return originalValue
  Equals dom op -> return $ evalEquals dom op originalValue args
  Order dom op -> return $ evalOrder dom op originalValue args
  Not -> return $ evalNot originalValue args
  And -> return $ evalAnd originalValue args
  Or -> return $ evalOr originalValue args
  Neg dom -> return $ evalNeg dom originalValue args
  Add dom -> return $ evalAdd dom originalValue args
  Sub dom -> return $ evalSub dom originalValue args
  Mul dom -> return $ evalMul dom originalValue args
  Div dom -> return $ evalDiv dom originalValue args
  Min dom -> return $ evalMin dom originalValue args
  Max dom -> return $ evalMax dom originalValue args
  PowRat -> return $ evalPowRat originalValue args
  ReduceAddRatTensor -> return $ evalReduceAddRatTensor originalValue args
  ReduceMulRatTensor -> return $ evalReduceMulRatTensor originalValue args
  ReduceMinRatTensor -> return $ evalReduceMinRatTensor originalValue args
  ReduceMaxRatTensor -> return $ evalReduceMaxRatTensor originalValue args
  ReduceAndTensor -> return $ evalReduceAndTensor originalValue args
  ReduceOrTensor -> return $ evalReduceOrTensor originalValue args
  FromNat FromNatToIndex -> return $ evalFromNatToIndex originalValue args
  FromNat FromNatToNat -> return $ evalFromNatToNat originalValue args
  FromNat FromNatToRat -> return $ evalFromNatToRat originalValue args
  FromRat FromRatToRat -> return $ evalFromRatToRat originalValue args
  FromVectorToList -> return $ evalVectorToList originalValue args
  If -> return $ evalIf originalValue args
  FoldList -> evalFoldList evalApp originalValue args
  MapList -> evalMapList (VBuiltin $ BuiltinFunction MapList) evalApp originalValue args
  Implies -> return $ evalImplies originalValue args
  At -> return $ evalAt originalValue args
  StackTensor -> return $ evalStackTensor originalValue args
  ConstTensor -> return $ evalConstTensor originalValue args
  Foreach -> evalForeach evalApp originalValue args
  Iterate -> evalIterate (VBuiltin (BuiltinFunction Iterate)) evalApp originalValue args
  FlattenTensorType -> evalFlattenTensorType freeEnv evalApp originalValue args

instance NormalisableBuiltin Builtin where
  evalBuiltinApp evalApp freeEnv originalExpr b normArgs =
    case getBuiltinFunction b of
      Nothing -> return originalExpr
      Just f -> evalBuiltinFunction freeEnv f evalApp originalExpr normArgs

  blockingArgs = \case
    BuiltinFunction f -> functionBlockingArgs f
    _ -> noBlockingArgs

-----------------------------------------------------------------------------
-- Linearity

instance NormalisableBuiltin LinearityBuiltin where
  evalBuiltinApp _evalApp _freeEnv _originalValue b _args = notImplemented b
    where
      {-
      case b of
        SliceTensor -> notImplemented b
        FoldVector -> notImplemented b
        ZipWithVector -> notImplemented b
        MapList -> notImplemented b
        MapVector -> notImplemented b
        Indices -> notImplemented b
        Implies -> notImplemented b
        FoldList -> evalLinearityFoldList evalApp originalValue args
        _ -> evalBuiltinFunction b evalApp originalValue args
        -}

      notImplemented = normNotImplemented "Linearity"

  blockingArgs = \case
    LinearityFunction f -> functionBlockingArgs f
    _ -> noBlockingArgs

-- Need foldList at the type-level to evaluate the Tensor definition
evalLinearityFoldList :: EvalBuiltin (Value LinearityBuiltin) m
evalLinearityFoldList evalApp originalExpr args =
  case args of
    [_a, _b, _c, _f, e, argExpr -> VBuiltin (LinearityConstructor Nil) []] -> return $ argExpr e
    [a, b, c, f, e, argExpr -> VBuiltin (LinearityConstructor Cons) [_, _, _, _, x, xs]] -> do
      let defaultFold = VBuiltin (LinearityFunction FoldList) [a, b, c, f, e, xs]
      r <- evalLinearityFoldList evalApp defaultFold [a, b, c, f, e, xs]
      evalApp (argExpr f) [x, explicit r]
    _ -> return originalExpr

-----------------------------------------------------------------------------
-- Polarity

instance NormalisableBuiltin PolarityBuiltin where
  evalBuiltinApp _evalApp _freeEnv _originalValue b _args = notImplemented b
    where
      {-
        case b of
        SliceTensor -> notImplemented b
        FoldVector -> notImplemented b
        ZipWithVector -> notImplemented b
        MapList -> notImplemented b
        MapVector -> notImplemented b
        Indices -> notImplemented b
        Implies -> notImplemented b
        FoldList -> evalPolarityFoldList evalApp originalValue args
        _ -> evalBuiltinFunction b evalApp originalValue args
        -}

      notImplemented = normNotImplemented "Polarity"

  blockingArgs = \case
    PolarityFunction f -> functionBlockingArgs f
    _ -> noBlockingArgs

-- Need foldList at the type-level to evaluate the Tensor definition
evalPolarityFoldList :: EvalBuiltin (Value PolarityBuiltin) m
evalPolarityFoldList evalApp originalExpr args =
  case args of
    [_a, _b, _c, _f, e, argExpr -> VBuiltin (PolarityConstructor Nil) []] -> return $ argExpr e
    [a, b, c, f, e, argExpr -> VBuiltin (PolarityConstructor Cons) [_, _, _, _, x, xs]] -> do
      let defaultFold = VBuiltin (PolarityFunction FoldList) [a, b, c, f, e, xs]
      r <- evalPolarityFoldList evalApp defaultFold [a, b, c, f, e, xs]
      evalApp (argExpr f) [x, explicit r]
    _ -> return originalExpr

normNotImplemented :: (Pretty fn) => Doc () -> fn -> a
normNotImplemented typeSystem b = developerError $ "Normalisation of " <+> pretty b <+> "at the type-level not yet supported for" <+> typeSystem <+> "system"

-----------------------------------------------------------------------------
-- Loss

instance NormalisableBuiltin LossBuiltin where
  evalBuiltinApp _evalApp _freeEnv originalValue b args = case b of
    LossBuiltinConstructor {} -> return originalValue
    LossBuiltinType {} -> return originalValue
    LossBuiltinFunction f -> case f of
      L.Neg dom -> return $ evalNeg dom originalValue args
      L.Add dom -> return $ evalAdd dom originalValue args
      L.Sub dom -> return $ evalSub dom originalValue args
      L.Mul dom -> return $ evalMul dom originalValue args
      L.Div dom -> return $ evalDiv dom originalValue args
      L.Min dom -> return $ evalMin dom originalValue args
      L.Max dom -> return $ evalMax dom originalValue args
      L.PowRat -> return $ evalPowRat originalValue args
      L.ReduceAddRatTensor -> return $ evalReduceAddRatTensor originalValue args
      L.ReduceMulRatTensor -> return $ evalReduceMulRatTensor originalValue args
      L.ReduceMinRatTensor -> return $ evalReduceMinRatTensor originalValue args
      L.ReduceMaxRatTensor -> return $ evalReduceMaxRatTensor originalValue args
      L.At -> return $ evalAt originalValue args
      L.StackTensor -> return $ evalStackTensor originalValue args
      L.ConstTensor -> return $ evalConstTensor originalValue args
      L.SearchRatTensor {} -> return originalValue

  blockingArgs = developerError "Blocking arguments not yet implemented for LossBuiltin"
