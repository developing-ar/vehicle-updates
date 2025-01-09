module Vehicle.Compile.Boolean.LowerNot
  ( lowerNot,
    notClosure,
  )
where

import Vehicle.Compile.Error (MonadCompile)
import Vehicle.Compile.Normalise.Quote (Quote (..))
import Vehicle.Compile.Prelude (Expr (..), Lv, explicit, implicitIrrelevant, normApp)
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Standard ()
import Vehicle.Data.Code.Interface
import Vehicle.Data.Code.TypedView
import Vehicle.Data.Code.Value
import Vehicle.Prelude (GenericArg (..))

--------------------------------------------------------------------------------
-- Not elimination

type MonadDropNot m =
  ( MonadCompile m
  )

-- | Tries to push in a `Not` as far as possible into a boolean expression.
-- If it is not possible to push it all the way through, it calls the continuation.
lowerNot ::
  forall m.
  (MonadDropNot m) =>
  Lv ->
  (Value Builtin -> m (Value Builtin)) ->
  Value Builtin ->
  m (Value Builtin)
lowerNot lv onBlocked e = do
  let go = lowerNot lv onBlocked
  case toBoolValue e of
    ----------------
    -- Base cases --
    ----------------
    VNot (TensorOp1Args _dims x) -> return x
    VBoolTensorLiteral b -> return $ fromBoolValue $ VBoolTensorLiteral (fmap not b)
    VOrderIndex (op, args) -> return $ fromBoolValue $ VOrderIndex (neg op, args)
    VEqualsIndex (op, args) -> return $ fromBoolValue $ VEqualsIndex (neg op, args)
    VOrderNat (op, args) -> return $ fromBoolValue $ VOrderNat (neg op, args)
    VEqualsNat (op, args) -> return $ fromBoolValue $ VEqualsNat (neg op, args)
    VOrderRatTensor (op, args) -> return $ fromBoolValue $ VOrderRatTensor (neg op, args)
    VEqualsRatTensor (op, args) -> return $ fromBoolValue $ VEqualsRatTensor (neg op, args)
    -- We can't actually lower the `not` through the body of the quantifier as
    -- it is not yet unnormalised. However, it's fine to stop here as we'll
    -- simply continue to normalise it once we re-encounter it again after
    -- normalising the quantifier.
    VQuantifyRatTensor q dims binder closure -> do
      let negatedClosure = notClosure lv dims closure
      return $ fromBoolValue $ VQuantifyRatTensor (neg q) dims binder negatedClosure
    ---------------------
    -- Inductive cases --
    ---------------------
    VConstBoolTensor v dims -> fromBoolValue <$> (VConstBoolTensor <$> go v <*> pure dims)
    VBoolStackTensor n dims xs -> fromBoolValue . VBoolStackTensor n dims <$> traverseSpine go xs
    VOr args -> fromBoolValue . VAnd <$> traverse go args
    VAnd args -> fromBoolValue . VOr <$> traverse go args
    VBoolIf dims c x y -> fromBoolValue <$> (VBoolIf dims c <$> go x <*> go y)
    -------------------
    -- Blocked cases --
    -------------------
    VReduceOrTensor {} -> onBlocked e
    VReduceAndTensor {} -> onBlocked e
    VBoolAt {} -> onBlocked e
    VBoolForeach {} -> onBlocked e

notClosure :: Lv -> VArg Builtin -> Closure Builtin -> Closure Builtin
notClosure lv dims (Closure env body) = do
  let dims' = implicitIrrelevant $ quote mempty lv $ argExpr dims
  let newBody = normApp (Builtin mempty (BuiltinFunction Not)) [dims', explicit body]
  Closure env newBody
