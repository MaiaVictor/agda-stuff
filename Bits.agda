module Bits where

open import Prelude.Product using (_,_)
open import Prelude.Bool
open import Prelude.Nat
open import Prelude.List
open import Prelude.Equality
open import Prelude.Vec
open import Extra

data Bit : Set where
  O : Bit
  I : Bit

Bits : Nat -> Set
Bits n = Vec Bit n

O∷ : {n : Nat} -> Bits n -> Bits (suc n)
O∷ xxs = O ∷ xxs

I∷ : {n : Nat} -> Bits n -> Bits (suc n)
I∷ xxs = I ∷ xxs

binOp : {n : Nat} -> (Bit -> Bit -> Bit) -> Bits n -> Bits n -> Bits n
binOp f []       []       = []
binOp f (x ∷ xs) (y ∷ ys) = f x y ∷ binOp f xs ys

xor : {n : Nat} -> Bits n -> Bits n -> Bits n
xor = binOp bitXor where
  bitXor : Bit -> Bit -> Bit
  bitXor O O = O
  bitXor O I = I
  bitXor I O = I
  bitXor I I = O

and : {n : Nat} -> Bits n -> Bits n -> Bits n
and = binOp bitAnd where
  bitAnd : Bit -> Bit -> Bit
  bitAnd O O = O
  bitAnd O I = O
  bitAnd I O = O
  bitAnd I I = I

or : {n : Nat} -> Bits n -> Bits n -> Bits n
or = binOp bitOr where
  bitOr : Bit -> Bit -> Bit
  bitOr O O = O
  bitOr O I = I
  bitOr I O = I
  bitOr I I = I

inc : {n : Nat} -> Bits n -> Bits n
inc []       = []
inc (O ∷ xs) = I ∷ xs
inc (I ∷ xs) = O ∷ inc xs

add : {n : Nat} -> Bits n -> Bits n -> Bits n
add []       []       = []
add (O ∷ xs) (O ∷ ys) = O ∷ (add xs ys)
add (O ∷ xs) (I ∷ ys) = I ∷ (add xs ys)
add (I ∷ xs) (O ∷ ys) = I ∷ (add xs ys)
add (I ∷ xs) (I ∷ ys) = inc (I ∷ (add xs ys))

pad : {n : Nat} -> {m : Nat} -> Bits n -> Bits m
pad {n}     {zero} x∷xs      = []
pad {zero}  {suc m} []       = O ∷ pad {zero} {m} []
pad {suc n} {suc m} (x ∷ xs) = x ∷ pad {n}    {m} xs

mul : {n : Nat} -> Bits n -> Bits n -> Bits n
mul []       []   = []
mul (O ∷ xs) y∷ys = O ∷ mul xs (pad y∷ys)
mul (I ∷ xs) y∷ys = add y∷ys (O ∷ mul xs (pad y∷ys))

repeat : {n : Nat} -> Bit -> Bits n
repeat {zero}    b = [] 
repeat {(suc n)} b = b ∷ repeat {n} b

b0 : {n : Nat} -> Bits n
b0 = repeat O

b1 : {n : Nat} -> Bits n
b1 = repeat I

fromNat : {n : Nat} -> Nat -> Bits n
fromNat zero    = b0
fromNat (suc m) = inc (fromNat m)

toNat : {n : Nat} -> Bits n -> Nat
toNat {n} = go 1 where
  go : {n : Nat} -> Nat -> Bits n -> Nat
  go k []       = 0
  go k (O ∷ xs) = go (k *N 2) xs
  go k (I ∷ xs) = go (k *N 2) xs +N k

add-comm : {n : Nat} -> (a : Bits n) -> (b : Bits n) -> add a b ≡ add b a
add-comm []       []       = refl
add-comm (O ∷ xs) (O ∷ ys) = cong O∷ (add-comm xs ys)
add-comm (O ∷ xs) (I ∷ ys) = cong I∷ (add-comm xs ys)
add-comm (I ∷ xs) (O ∷ ys) = cong I∷ (add-comm xs ys)
add-comm (I ∷ xs) (I ∷ ys) = cong O∷ (cong inc (add-comm xs ys))
