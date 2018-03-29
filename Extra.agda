module Extra where

open import Prelude.Product using (_,_; _×_)
open import Prelude.Vec
open import Prelude.List
open import Prelude.Nat
open import Prelude.Nat.Properties
open import Prelude.Product
open import Prelude.Equality
open import Agda.Builtin.Equality

call : {a : Set} -> Nat -> (a -> a) -> a -> a
call zero    f x = x
call (suc n) f x = f (call n f x)

listRoundIndex : {A : Set} -> Nat -> A -> List A -> A
listRoundIndex {A} n x xs = go n xs where
  go : Nat -> List A -> A
  go (suc n) (x ∷ xs) = go n xs
  go (suc n) []       = go n xs
  go zero    (x ∷ xs) = x
  go zero    []       = x

listGenerate : {A : Set} -> Nat -> (Nat -> A) -> List A
listGenerate {A} n f = go zero n where
  go : Nat -> Nat -> List A
  go zero    i = []
  go (suc n) i = f i ∷ go n (suc i)

vecSplit : {A : Set} -> {n : Nat} -> {m : Nat} -> Vec A (n +N m) -> Vec A n × Vec A m
vecSplit {A} {zero}    {m} x∷xs     = [] , x∷xs
vecSplit {A} {(suc n)} {m} (x ∷ xs) = 
  let parts = vecSplit {A} {n} {m} xs
      part0 = x ∷ fst parts
      part1 = snd parts
  in part0 , part1

vecCommuteSize : {A : Set} -> (n : Nat) -> (m : Nat) -> Vec A (n +N m) -> Vec A (m +N n)
vecCommuteSize {A} n m = transport (\ x -> Vec A x) (add-commute n m)

vecRotateLeft : {A : Set} -> {m : Nat} -> (n : Nat) -> Vec A (n +N m) -> Vec A (n +N m)
vecRotateLeft {A} {m} n x∷xs =
  let parts = vecSplit {A} {n} {m} x∷xs
  in  vecCommuteSize m n (snd parts v++ fst parts)

vecRotateRight : {A : Set} -> {m : Nat} -> (n : Nat) -> Vec A (n +N m) -> Vec A (n +N m)
vecRotateRight {A} {m} n x∷xs =
  let commuted   = vecCommuteSize n m x∷xs
      rotated    = vecRotateLeft {A} {n} m commuted
      recommuted = vecCommuteSize m n rotated
  in  recommuted

foo : Vec Nat 8
foo = vecRotateRight 3 (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ [])
  
  
