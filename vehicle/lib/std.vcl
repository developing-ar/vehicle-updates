--------------------------------------------------------------------------------
-- Type annotations
--------------------------------------------------------------------------------

-- Implementation of the `:` syntax
typeAnn : forallT (t : Type) . t -> t
typeAnn t a = a

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

eqRatTensor : Tensor Rat dims -> Tensor Rat dims -> Bool
eqRatTensor xs ys = reduceAnd (xs ==. ys)

neRatTensor : Tensor Rat dims -> Tensor Rat dims -> Bool
neRatTensor xs ys = reduceAnd (xs !=. ys)

leRatTensor : Tensor Rat dims -> Tensor Rat dims -> Bool
leRatTensor xs ys = reduceAnd (xs <=. ys)

ltRatTensor : Tensor Rat dims -> Tensor Rat dims -> Bool
ltRatTensor xs ys = reduceAnd (xs <. ys)

geRatTensor : Tensor Rat dims -> Tensor Rat dims -> Bool
geRatTensor xs ys = reduceAnd (xs >=. ys)

gtRatTensor : Tensor Rat dims -> Tensor Rat dims -> Bool
gtRatTensor xs ys = reduceAnd (xs >. ys)

--------------------------------------------------------------------------------
-- Index
--------------------------------------------------------------------------------

existsIndex : forallT {n} . (Index n -> Bool) -> Bool
existsIndex f = reduceOr False (foreach i . f i)

forallIndex : forallT {n} . (Index n -> Bool) -> Bool
forallIndex f = reduceAnd True (foreach i . f i)
