
module plfa.part1.Midterm where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
-- you can add any import definitions that you need
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _>_; z≤n; s≤s; _≤?_; _<?_; _^_)
open import Data.Nat.Properties using (+-assoc; +-suc; +-comm; *-comm)
open import Relation.Nullary using (yes; no; Dec)

-- used for rewrite
simplify : ∀ {A : Set} (x : A) → x ≡ x
simplify x = refl

sum : ℕ → ℕ
sum 0 = 0
sum n@(suc sn) = sum sn + n

-- Problem 1
-- remove the "postulate" and prove this theorem, which is a version of
--   sum n ≡ n * (n - 1) / 2

--- my solution from Induction HW, copied here instead of importing for ease of grading
*-distrib-+ : ∀ (m n p : ℕ) →  (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
   n * p
  ≡⟨⟩
   zero + n * p
  ≡⟨⟩
   zero * p + n * p
  ∎
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
   (suc (m + n)) * p
  ≡⟨⟩
   p + ((m + n) * p)
  ≡⟨ cong (λ x -> p + x) (*-distrib-+ m n p) ⟩
   p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p))⟩
   (p + m * p) + n * p
  ≡⟨⟩
   suc m * p + n * p
  ∎

1-suc : ∀ ( n : ℕ )
  → n + 1 ≡ suc n
1-suc (zero) = refl
1-suc (suc n) =
  begin
    suc n + 1
  ≡⟨ (+-comm (suc n) 1) ⟩
    1 + suc n
  ≡⟨⟩
    suc ( 1 + n)
  ≡⟨ cong suc (+-comm 1 n) ⟩
    suc ( n + 1)
  ≡⟨ cong suc (1-suc n) ⟩
    suc ( suc n )
  ∎

simple : ∀ (n : ℕ) → (sum n) * 2 ≡ (suc n) * n
simple zero = refl
simple (suc n) =
  begin
    (sum (suc n)) * 2
  ≡⟨⟩
    ((sum n) + (suc n)) * 2
  ≡⟨ cong (λ x -> x) (*-distrib-+ (sum n) (suc n) 2 )⟩
    (sum n) * 2 + (suc n) * 2
  ≡⟨ cong (λ x -> x + (suc n) * 2) (simple (n))⟩
    (suc n) * n + (suc n) * 2
  ≡⟨ cong (λ x → x + (suc n) * 2) (*-comm (suc n) n)⟩
    n * (suc n) + (suc n) * 2
  ≡⟨ cong (λ x → n * (suc n) + x) (*-comm (suc n) 2)⟩
    n * (suc n) + 2 * (suc n)
  ≡⟨ cong (λ x → x) (sym (*-distrib-+ n 2 (suc n)))⟩
    (n + 2) * (suc n)
  ≡⟨⟩
    (n + suc 1) * (suc n)
  ≡⟨ cong (λ x → x * (suc n)) (+-suc n 1)⟩
    (suc (n + 1)) * (suc n)
  ≡⟨ cong (λ x → (suc (x)) * (suc n)) (1-suc n)⟩
    (suc (suc n)) * (suc n)
  ∎

-- Problem 2
-- remove the postulate and implement this function, which gives an Natural
-- number approximation of square root

if_then_else_ : { A : Set }
  → Dec A
  → ℕ
  → ℕ
  → ℕ
if yes A then a else b = a
if no A then a else b = b

sqrt : ℕ → ℕ

rt_sub_ : ℕ → ℕ → ℕ
rt_sub_ n  sqrtn = if ((suc n) <? (((sqrtn) + 1) ^ 2)) then (sqrtn) else ((sqrtn) + 1)

sqrt 0 = 0
sqrt (suc n) = rt n sub (sqrt n)

-- you can run these test cases
_ : sqrt 0 ≡ 0
_ = refl
_ : sqrt 1 ≡ 1
_ = refl
_ : sqrt 2 ≡ 1
_ = refl
_ : sqrt 3 ≡ 1
_ = refl
_ : sqrt 4 ≡ 2
_ = refl
_ : sqrt 5 ≡ 2
_ = refl
_ : sqrt 6 ≡ 2
_ = refl
_ : sqrt 7 ≡ 2
_ = refl
_ : sqrt 8 ≡ 2
_ = refl
_ : sqrt 9 ≡ 3
_ = refl
_ : sqrt 10 ≡ 3
_ = refl
_ : sqrt 11 ≡ 3
_ = refl
_ : sqrt 12 ≡ 3
_ = refl
_ : sqrt 13 ≡ 3
_ = refl
_ : sqrt 14 ≡ 3
_ = refl
_ : sqrt 15 ≡ 3
_ = refl
_ : sqrt 16 ≡ 4
_ = refl
_ : sqrt 17 ≡ 4
_ = refl
_ : sqrt 18 ≡ 4
_ = refl
_ : sqrt 19 ≡ 4
_ = refl
_ : sqrt 20 ≡ 4
_ = refl
_ : sqrt 21 ≡ 4
_ = refl
_ : sqrt 22 ≡ 4
_ = refl
_ : sqrt 23 ≡ 4
_ = refl
_ : sqrt 24 ≡ 4
_ = refl
_ : sqrt 24 ≡ 4
_ = refl
_ : sqrt 24 ≡ 4
_ = refl
_ : sqrt 25 ≡ 5
_ = refl
_ : sqrt 26 ≡ 5
_ = refl
_ : sqrt 27 ≡ 5
_ = refl


_ : sqrt 100 ≡ 10
_ = refl
_ : sqrt 101 ≡ 10
_ = refl

