--------------------------------------------------------------------------------
-- Type annotations
--------------------------------------------------------------------------------

-- Implementation of the `:` syntax
typeAnn : forallT (t : Type) . t -> t
typeAnn t a = a

id : A -> A
id x = x

--------------------------------------------------------------------------------
-- List
--------------------------------------------------------------------------------

appendList : List A -> List A -> List A
appendList xs ys = fold (\x y -> x :: y) ys xs

--------------------------------------------------------------------------------
-- Bool
--------------------------------------------------------------------------------

implies : Tensor Bool dims -> Tensor Bool dims -> Tensor Bool dims
implies x y = (not x) or y

forallInList : (A -> Bool) -> List A -> Bool
forallInList f xs = fold (\x y -> x and y) True (map f xs)

existsInList : (A -> Bool) -> List A -> Bool
existsInList f xs = fold (\x y -> x or y) False (map f xs)

--------------------------------------------------------------------------------
-- Tensor
--------------------------------------------------------------------------------

-- TODO can we replace with?
-- type Vector A n = Tensor A [n]
Vector : forallT A . forallT n . {{IsTensorType A [n]}} -> Type
Vector A n = Tensor A [n]

{-
forallInTensor : (A -> Bool) -> Tensor A dims -> Bool
forallInTensor f xs = reduceAnd (foreach (\x y -> x and y) True (map f xs))

existsInTensor : (A -> Bool) -> Tensor A dims -> Bool
existsInTensor f xs = reduceOr (map f xs)

--------------------------------------------------------------------------------
-- Index
--------------------------------------------------------------------------------

foreachIndex : forallT n . (Index n -> A) -> Vector A n
foreachIndex n f = map f (indices n)
-}
existsIndex : forallT n . (Index n -> Bool) -> Bool
existsIndex n f = reduceOr (foreach i . f i)

forallIndex : forallT n . (Index n -> Bool) -> Bool
forallIndex n f = reduceAnd (foreach i . f i)
