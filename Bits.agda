module Bits where

open import Data.Vec
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.String
open import Data.List hiding (and; or)
open import Agda.Builtin.Char

data Bit : Set where
  O : Bit
  I : Bit

bitNot : Bit → Bit
bitNot O = I
bitNot I = O

bitXor : Bit → Bit → Bit
bitXor O O = O
bitXor O I = I
bitXor I O = I
bitXor I I = O

bitAnd : Bit → Bit → Bit
bitAnd O O = O
bitAnd O I = O
bitAnd I O = O
bitAnd I I = I

bitOr : Bit → Bit → Bit
bitOr O O = O
bitOr O I = I
bitOr I O = I
bitOr I I = I

Bits : ℕ → Set
Bits n = Vec Bit n

O∷ : {n : ℕ} → Bits n → Bits (suc n)
O∷ xxs = O ∷ xxs

I∷ : {n : ℕ} → Bits n → Bits (suc n)
I∷ xxs = I ∷ xxs

op₁ : {n : ℕ} → (Bit → Bit) → Bits n → Bits n
op₁ f []       = []
op₁ f (x ∷ xs) = f x ∷ op₁ f xs

op₂ : {n : ℕ} → (Bit → Bit → Bit) → Bits n → Bits n → Bits n
op₂ f []       []       = []
op₂ f (x ∷ xs) (y ∷ ys) = f x y ∷ op₂ f xs ys

not : {n : ℕ} → Bits n → Bits n
not = op₁ bitNot

xor : {n : ℕ} → Bits n → Bits n → Bits n
xor = op₂ bitXor

and : {n : ℕ} → Bits n → Bits n → Bits n
and = op₂ bitAnd

or : {n : ℕ} → Bits n → Bits n → Bits n
or = op₂ bitOr

inc : {n : ℕ} → Bits n → Bits n
inc []       = []
inc (O ∷ xs) = I ∷ xs
inc (I ∷ xs) = O ∷ inc xs

add : {n : ℕ} → Bits n → Bits n → Bits n
add []       []       = []
add (O ∷ xs) (O ∷ ys) = O ∷ (add xs ys)
add (O ∷ xs) (I ∷ ys) = I ∷ (add xs ys)
add (I ∷ xs) (O ∷ ys) = I ∷ (add xs ys)
add (I ∷ xs) (I ∷ ys) = inc (I ∷ (add xs ys))

add-comm : {n : ℕ} → (a : Bits n) → (b : Bits n) → add a b ≡ add b a
add-comm []       []       = refl
add-comm (O ∷ xs) (O ∷ ys) = cong O∷ (add-comm xs ys)
add-comm (O ∷ xs) (I ∷ ys) = cong I∷ (add-comm xs ys)
add-comm (I ∷ xs) (O ∷ ys) = cong I∷ (add-comm xs ys)
add-comm (I ∷ xs) (I ∷ ys) = cong O∷ (cong inc (add-comm xs ys))

pad : {n : ℕ} → {m : ℕ} → Bits n → Bits m
pad {n}     {zero} x∷xs      = []
pad {zero}  {suc m} []       = O ∷ pad {zero} {m} []
pad {suc n} {suc m} (x ∷ xs) = x ∷ pad {n}    {m} xs

mul : {n : ℕ} → Bits n → Bits n → Bits n
mul []       []   = []
mul (O ∷ xs) y∷ys = O ∷ mul xs (pad y∷ys)
mul (I ∷ xs) y∷ys = add y∷ys (O ∷ mul xs (pad y∷ys))

repeat : {n : ℕ} → Bit → Bits n
repeat {zero}    b = [] 
repeat {(suc n)} b = b ∷ repeat {n} b

b0 : {n : ℕ} → Bits n
b0 = repeat O

b1 : {n : ℕ} → Bits n
b1 = repeat I

fromℕ : {n : ℕ} → ℕ → Bits n
fromℕ zero    = b0
fromℕ (suc m) = inc (fromℕ m)

toℕ : {n : ℕ} → Bits n → ℕ
toℕ {n} = go 1 where
  go : {n : ℕ} → ℕ → Bits n → ℕ
  go k []       = 0
  go k (O ∷ xs) = go (k * 2) xs
  go k (I ∷ xs) = go (k * 2) xs + k

fromString : (str : String) → Bits (length (primStringToList str))
fromString str = withCcs (primStringToList str) where
  getBit : ℕ → ℕ → Bit
  getBit zero    zero    = I
  getBit zero    (suc m) = O
  getBit (suc n) zero    = O
  getBit (suc n) (suc m) = getBit n m
  withCcs : (ccs : List Char) → Bits (length ccs)
  withCcs []       = []
  withCcs (c ∷ cs) = getBit 49 (primCharToNat c) ∷ withCcs cs

toString : {n : ℕ} → Bits n → String
toString []       = ""
toString (O ∷ xs) = "0" Data.String.++ toString xs
toString (I ∷ xs) = "1" Data.String.++ toString xs
