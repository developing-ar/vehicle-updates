
module Vehicle.Data.Tensor where

open import Level using (Level; 0ℓ)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; tabulate; concat; foldr)
open import Data.Vec.Functional using (Vector)
import Data.Vec.Functional as Vec
open import Data.Fin using (Fin)
import Data.Rational as ℚ
open import Data.Rational using (ℚ)

Dimension : Set
Dimension = ℕ

Dimensions : Set
Dimensions = List Dimension

private
  variable
    a p : Level
    A B C : Set a
    d : Dimension
    ds : Dimensions

Tensor : Set a → Dimensions → Set a
Tensor A []       = A
Tensor A (d ∷ ds) = Vector (Tensor A ds) d

Pointwise : (A → B → Set p) → Tensor A ds → Tensor B ds → Set p
Pointwise = {!!}

foreach : (Fin d → Tensor A ds) → Tensor A (d ∷ ds)
foreach f = f

const : A → (ds : Dimensions) → Tensor A ds
const v [] = v
const v (d ∷ ds) = λ i → const v ds

map : (A → B) → Tensor A ds → Tensor B ds
map {ds = []}      f xs = f xs
map {ds = d ∷ ds} f xs = λ i → map f (xs i)

zipWith : (A → B → C) → Tensor A ds → Tensor B ds → Tensor C ds
zipWith {ds = []}      f xs ys = f xs ys
zipWith {ds = d ∷ ds} f xs ys = λ i → zipWith f (xs i) (ys i)

toList : Tensor A ds → List A
toList {ds = []} x = x ∷ []
toList {ds = d ∷ ds} xs = concat (tabulate λ i → toList (xs i))

reduce : (A → B → B) → B → Tensor A ds → Tensor B []
reduce f e xs = foldr f e (toList xs)

--------------------------------------------------------------------------------
-- Rational specialisations

infix  8 -_
infixl 7 _*_ _⊓_
infixl 6 _-_ _+_ _⊔_

_+_ : Tensor ℚ ds → Tensor ℚ ds → Tensor ℚ ds
_+_ = zipWith ℚ._+_

_-_ : Tensor ℚ ds → Tensor ℚ ds → Tensor ℚ ds
_-_ = zipWith ℚ._-_

_*_ : Tensor ℚ ds → Tensor ℚ ds → Tensor ℚ ds
_*_ = zipWith ℚ._*_

-_ : Tensor ℚ ds → Tensor ℚ ds
-_ = map (ℚ.-_)

_⊔_ : Tensor ℚ ds → Tensor ℚ ds → Tensor ℚ ds
_⊔_ = zipWith ℚ._⊔_

_⊓_ : Tensor ℚ ds → Tensor ℚ ds → Tensor ℚ ds
_⊓_ = zipWith ℚ._⊓_

reduceAnd : Tensor Bool ds → Tensor Bool []
reduceAnd = reduce _∧_ true

reduceOr : Tensor Bool ds → Tensor Bool []
reduceOr = reduce _∨_ false


_≤_ : Tensor ℚ ds → Tensor ℚ ds → Set 0ℓ
xs ≤ ys = Pointwise ℚ._≤_ xs ys

_<_ : Tensor ℚ ds → Tensor ℚ ds → Set 0ℓ
xs < ys = Pointwise ℚ._<_ xs ys

_≥_ : Tensor ℚ ds → Tensor ℚ ds → Set 0ℓ
xs ≥ ys = Pointwise ℚ._≥_ xs ys

_>_ : Tensor ℚ ds → Tensor ℚ ds → Set 0ℓ
xs > ys = Pointwise ℚ._>_ xs ys

_≤ᵇ_ : Tensor ℚ ds → Tensor ℚ ds → Tensor Bool []
xs ≤ᵇ ys = reduceAnd (zipWith ℚ._≤ᵇ_ xs ys)

_<ᵇ_ : Tensor ℚ ds → Tensor ℚ ds → Tensor Bool []
xs <ᵇ ys = reduceAnd (zipWith {!!} xs ys)

_≥ᵇ_ : Tensor ℚ ds → Tensor ℚ ds → Tensor Bool []
xs ≥ᵇ ys = reduceAnd (zipWith {!!} xs ys)

_>ᵇ_ : Tensor ℚ ds → Tensor ℚ ds → Tensor Bool []
xs >ᵇ ys = reduceAnd (zipWith {!!} xs ys)
