module Vehicle.Compile.Boolean.LowerNot
  ( lowerNot,
    notClosure,
  )
where

import Vehicle.Compile.Error (MonadCompile)
import Vehicle.Compile.Prelude (Expr (..), explicit, implicitIrrelevant, normApp)
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Standard ()
import Vehicle.Data.Code.TypedView
import Vehicle.Data.Code.Value

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
  (Value Builtin -> m (Value Builtin)) ->
  Value Builtin ->
  m (Value Builtin)
lowerNot onBlocked e = case toBoolValue e of
  ----------------
  -- Base cases --
  ----------------
  VNot _dims x -> return x
  VBoolTensorLiteral b -> return $ fromBoolValue $ VBoolTensorLiteral (fmap not b)
  VOrderIndex op n1 n2 x y -> return $ fromBoolValue $ VOrderIndex (neg op) n1 n2 x y
  VEqualsIndex op n1 n2 x y -> return $ fromBoolValue $ VEqualsIndex (neg op) n1 n2 x y
  VOrderNat op x y -> return $ fromBoolValue $ VOrderNat (neg op) x y
  VEqualsNat op x y -> return $ fromBoolValue $ VEqualsNat (neg op) x y
  VOrderRatTensor op dims x y -> return $ fromBoolValue $ VOrderRatTensor (neg op) dims x y
  VEqualsRatTensor op dims x y -> return $ fromBoolValue $ VEqualsRatTensor (neg op) dims x y
  -- We can't actually lower the `not` through the body of the quantifier as
  -- it is not yet unnormalised. However, it's fine to stop here as we'll
  -- simply continue to normalise it once we re-encounter it again after
  -- normalising the quantifier.
  VQuantifyRatTensor q dims binder closure -> do
    return $ fromBoolValue $ VQuantifyRatTensor (neg q) dims binder (notClosure closure)
  ---------------------
  -- Inductive cases --
  ---------------------
  VConstBoolTensor v dims -> fromBoolValue <$> (VConstBoolTensor <$> lowerNot onBlocked v <*> pure dims)
  VBoolStackTensor n dims xs -> fromBoolValue . VBoolStackTensor n dims <$> traverseSpine (lowerNot onBlocked) xs
  VOr dims x y -> fromBoolValue <$> (VAnd dims <$> lowerNot onBlocked x <*> lowerNot onBlocked y)
  VAnd dims x y -> fromBoolValue <$> (VOr dims <$> lowerNot onBlocked x <*> lowerNot onBlocked y)
  VBoolIf dims c x y -> fromBoolValue <$> (VBoolIf dims c <$> lowerNot onBlocked x <*> lowerNot onBlocked y)
  -------------------
  -- Blocked cases --
  -------------------
  VReduceOrTensor {} -> onBlocked e
  VReduceAndTensor {} -> onBlocked e
  VBoolAt {} -> onBlocked e
  VBoolForeach {} -> onBlocked e

notClosure :: Closure Builtin -> Closure Builtin
notClosure (Closure env body) = do
  let dims' = implicitIrrelevant $ Hole mempty "dims" -- fmap (quote mempty _) dims
  let newBody = normApp (Builtin mempty (BuiltinFunction Not)) [dims', explicit body]
  Closure env newBody
