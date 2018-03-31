open import Data.List hiding (lookup)
open import Data.Maybe
open import Data.Vec hiding (lookup)
open import Data.Nat
open import Bits

data Map (A : Set) : Set where
  leaf : Map A
  node : Maybe A → Map A → Map A → Map A

-- Stores a key, value pair on a map.
insert : {A : Set} → {n : ℕ} → Bits n → A → Map A → Map A
insert []       v leaf         = node (just v) leaf leaf
insert []       v (node a x y) = node (just v) x y
insert (O ∷ bs) v leaf         = node nothing (insert bs v leaf) leaf
insert (O ∷ bs) v (node a x y) = node a (insert bs v x) y
insert (I ∷ bs) v leaf         = node nothing leaf (insert bs v leaf)
insert (I ∷ bs) v (node a x y) = node a x (insert bs v y)

-- Looks a key up on a map, returning stored value.
lookup : {A : Set} → {n : ℕ} → Bits n → Map A → Maybe A
lookup []       leaf         = nothing
lookup []       (node a x y) = a
lookup (O ∷ bs) leaf         = nothing
lookup (O ∷ bs) (node a x y) = lookup bs x
lookup (I ∷ bs) leaf         = nothing
lookup (I ∷ bs) (node a x y) = lookup bs y

-- Deletes a key, val pair stored on a map.
delete : {A : Set} → {n : ℕ} → Bits n → Map A → Map A
delete []      leaf         = leaf
delete []      (node a x y) = leaf
delete (O ∷ k) leaf         = leaf
delete (O ∷ k) (node a x y) = node a (delete k x) y
delete (I ∷ k) leaf         = leaf
delete (I ∷ k) (node a x y) = node a x (delete k y)
