module Extra where

{-open import Prelude-}
{-open import Numeric.Nat.DivMod-}

open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Bool hiding (_≟_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

the : (A : Set) → (x : A) → A
the A x = x

icall : {A : Set} → (n : ℕ) → (Fin n → A → A) → A → A
icall zero    f x = x
icall (suc n) f x = icall n (λ w → f (suc w)) (f zero x)

call : {A : Set} → ℕ → (A → A) → A → A
call n f = icall n (λ i → f)

NonZero : ℕ → Set
NonZero n = False (n ≟ 0)

roundLookup : {A : Set} → {w : ℕ} → {w≢0 : NonZero w} → ℕ → Vec A w → A
roundLookup {A} {w} {w≢0} n vec = lookup (_mod_ n w {≢0 = w≢0}) vec

roundLookup₂ : {A : Set} → {w : ℕ} → {w>0 : NonZero w} → {h : ℕ} → {h>0 : NonZero h} → ℕ → ℕ → Vec (Vec A w) h → A
roundLookup₂ {A} {w} {w≢0} {h} {h≢0} x y mat = roundLookup {w = w} {w≢0 = w≢0} x (roundLookup {w = h} {w≢0 = h≢0} y mat)

applyAt : {A : Set} → {w : ℕ} → Fin w → (A → A) → Vec A w → Vec A w
applyAt zero    f (v ∷ vec) = f v ∷ vec
applyAt (suc x) f (v ∷ vec) = v ∷ applyAt x f vec

applyAt₂ : {A : Set} → {w : ℕ} → {h : ℕ} → Fin w → Fin h → (A → A) → Vec (Vec A w) h → Vec (Vec A w) h
applyAt₂ x y f mat = applyAt y (applyAt x f) mat

setAt : {A : Set} → {w : ℕ} → Fin w → A → Vec A w → Vec A w
setAt x v = applyAt x (λ v₂ → v)

setAt₂ : {A : Set} → {w : ℕ} → {h : ℕ} → Fin w → Fin h → A → Vec (Vec A w) h → Vec (Vec A w) h
setAt₂ x y v = applyAt₂ x y (λ v₂ → v)

diff : {a : ℕ} → {b : Fin a} → ∃ λ c → toℕ b + c ≡ a
diff {zero}  {()}
diff {suc a} {zero}  = suc a , refl
diff {suc a} {suc b} with diff {a} {b}
... | c , prf = c , cong suc prf

rotate : {A : Set} → {w : ℕ} → {w≢0 : NonZero w} → Bool → ℕ → Vec A w → Vec A w
rotate {A} {w} {w≢0} left n v =
  let m  = _mod_ n w {w≢0}
      d  = diff {w} {m}
      d₁ = proj₁ d
      d₂ = proj₂ d
      d₃ = subst (λ x → x ≡ w) (+-comm (toℕ (n mod w)) d₁) d₂
      v₁ = subst (λ x → Vec A x) (sym d₂) v
      v₂ = subst (λ x → Vec A x) (sym d₃) v
      s₁ = splitAt {A = A} (toℕ m) {n = d₁} v₁
      s₂ = splitAt {A = A} d₁ {n = (toℕ m)} v₂
      l₁ = proj₁ (proj₂ s₁)
      r₁ = proj₁ s₁
      o₁ = subst (λ x → Vec A x) d₃ (l₁ ++ r₁)
      l₂ = proj₁ (proj₂ s₂)
      r₂ = proj₁ s₂
      o₂ = subst (λ x → Vec A x) d₂ (l₂ ++ r₂)
  in  if left then o₁ else o₂

rotateLeft : {A : Set} → {w : ℕ} → {w≢0 : NonZero w} → ℕ → Vec A w → Vec A w
rotateLeft {A} {w} {w≢0} n vec = rotate {A} {w} {w≢0} true n vec

rotateRight : {A : Set} → {w : ℕ} → {w≢0 : NonZero w} → ℕ → Vec A w → Vec A w
rotateRight {A} {w} {w≢0} n vec = rotate {A} {w} {w≢0} false n vec

foo : Vec ℕ 5
foo = rotateRight 2 (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])

imap : {A : Set} → {B : Set} → {n : ℕ} → (ℕ → A → B) → Vec A n → Vec B n
imap {A} {B} {n} f = go 0 where
  go : {n : ℕ} → ℕ → Vec A n → Vec B n
  go n []       = []
  go n (x ∷ xs) = f n x ∷ go (suc n) xs

imap₂ : {A : Set} → {B : Set} → {w : ℕ} → {h : ℕ} → (ℕ → ℕ → A → B) → Vec (Vec A w) h → Vec (Vec B w) h
imap₂ f mat = imap (λ y row → imap (λ x v → f x y v) row) mat

generate : {A : Set} → {n : ℕ} → (ℕ → A) → Vec A n
generate f = tabulate (λ i → f (toℕ i))

generate₂ : {A : Set} → {w : ℕ} → {h : ℕ} → (ℕ → ℕ → A) → Vec (Vec A w) h
generate₂ {A} {w} {h} f = generate {n = h} (λ y → (generate {n = w} (λ x → f x y)))
