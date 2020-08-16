module plfa.Induction where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; _≡⟨_⟩_)

open import Function

infixl 6 _+_ _∸_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_^_ : ℕ → ℕ → ℕ
n ^ 0     = 1
n ^ suc m = n * (n ^ m)

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
  
+-identityʳ (suc n) =
  begin
    suc n + zero
  ≡⟨⟩
    suc (n + zero)
  ≡⟨ cong suc (+-identityʳ n) ⟩
    suc n
  ∎


+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n)⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎


*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p
  rewrite *-distrib-+ m n p
        | sym (+-assoc p (m * p) (n * p))
          = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
  ≡⟨⟩
    (n + m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p
  ≡⟨ cong (n * p +_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ∎

*-zero : ∀ (n : ℕ) → n * zero ≡ zero
*-zero zero = refl
*-zero (suc n) =
  begin
    suc n * zero
  ≡⟨ (*-zero n) ⟩
    refl

*-succ : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-succ zero n =
  begin
    zero * suc n
  ≡⟨⟩
    zero
  ∎
*-succ (suc m) n =
  begin
    suc m * suc n
  ≡⟨ cong (suc n +_) (*-succ m n) ⟩
    suc (n + (m + m * n))
  ≡⟨ cong suc (+-swap n m (m * n))⟩
    suc (m + (n + m * n))
  ∎

*-comm : ∀ (m n : ℕ) → (m * n) ≡ (n * m)
*-comm m zero =
  begin
    m * zero
  ≡⟨ *-zero m ⟩
    zero
  ≡⟨⟩
    zero * m
  ∎
*-comm m (suc n) =
  begin
    m * suc n
  ≡⟨ *-succ m n ⟩
    m + m * n
  ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + n * m
  ≡⟨⟩
    suc n * m
  ∎


0∸n : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n zero = refl
0∸n (suc n) = refl


∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero n p =
  begin
    zero ∸ n ∸ p
  ≡⟨ cong (_∸ p) (0∸n n) ⟩
    zero ∸ p
  ≡⟨ 0∸n p ⟩
    zero
  ≡⟨ sym (0∸n (n + p)) ⟩
    zero ∸ (n + p)
  ∎
∸-+-assoc (suc m) (suc n) p =
  begin
    suc m ∸ suc n ∸ p
  ≡⟨ ∸-+-assoc m n p ⟩
    suc m ∸ (suc n + p)
  ∎

*-identity : ∀ (n : ℕ) → 1 * n ≡ n
*-identity zero = refl
*-identity (suc n) rewrite *-identity n = refl

^-zero : ∀ (n : ℕ) → n ^ zero ≡ 1
^-zero n = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p =
  begin
    m ^ (zero + p)
  ≡⟨⟩
    m ^ p
  ≡⟨ sym (*-identity (m ^ p)) ⟩
    1 * (m ^ p)
  ≡⟨ cong (_* (m ^ p)) (sym (^-zero m)) ⟩
    (m ^ zero) * (m ^ p)
  ∎

^-distribˡ-+-* m (suc n) p =
  begin
    m ^ (suc n + p)
  ≡⟨⟩
    m * m ^ (n + p)
  ≡⟨ cong (m *_) (^-distribˡ-+-* m n p) ⟩
    m * ((m ^ n) * (m ^ p))
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m * (m ^ n) * (m ^ p)
  ≡⟨⟩
    m ^ (suc n) * m ^ p
  ∎


*-swap-* : ∀ (a b c d : ℕ) → (a * b) * (c * d) ≡ (a * c) * (b * d)
*-swap-* a b c d =
  begin
    (a * b) * (c * d)
  ≡⟨ *-assoc a b (c * d) ⟩
    a * (b * (c * d))
  ≡⟨ cong (_*_ a) (sym (*-assoc b c d)) ⟩
    a * ((b * c) * d)
  ≡⟨ cong (_*_ a ∘ flip _*_ d) (*-comm b c) ⟩
    a * ((c * b) * d)
  ≡⟨ cong (_*_ a) (*-assoc c b d) ⟩
    a * (c * (b * d))
  ≡⟨ sym (*-assoc a c (b * d)) ⟩
    a * c * (b * d)
  ∎

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) =
  begin
    (m * n) ^ (suc p)
  ≡⟨⟩
    m * n * (m * n) ^ p
  ≡⟨ cong ((m * n) *_) (^-distribʳ-* m n p) ⟩
    m * n * (m ^ p * n ^ p)
  ≡⟨ *-swap-* m n (m ^ p) (n ^ p) ⟩
    m * (m ^ p) * (n * n ^ p)
  ≡⟨⟩
    m ^ suc p * (n ^ suc p)
  ∎

^-1 : ∀ (n : ℕ) → 1 ^ n ≡ 1
^-1 zero = refl
^-1 (suc n) =
  begin
    1 ^ (suc n)
  ≡⟨⟩
    1 * 1 ^ n
  ≡⟨ cong (1 *_) (^-1 n) ⟩
    1 * 1
  ≡⟨⟩
    1
  ∎


^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m zero p =
  begin
    (m ^ zero) ^ p
  ≡⟨⟩
    1 ^ p
  ≡⟨ ^-1 p ⟩
    1
  ≡⟨⟩
    m ^ (zero * p)
  ∎
^-*-assoc m (suc n) p =
  begin
    (m ^ suc n) ^ p
  ≡⟨⟩
    (m * (m ^ n)) ^ p
  ≡⟨ ^-distribʳ-* m (m ^ n) p ⟩
    (m ^ p) * ((m ^ n) ^ p)
  ≡⟨ cong ((m ^ p) *_) (^-*-assoc m n p) ⟩
    (m ^ p) * (m ^ (n * p))
  ≡⟨ sym (^-distribˡ-+-* m p (n * p)) ⟩
    m ^ (p + (n * p))
  ≡⟨⟩
    m ^ (suc n * p)
  ∎

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin
  
inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (h O) = h I
inc (h I) = (inc h) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : inc (⟨⟩ O O O I) ≡ ⟨⟩ O O I O
_ = refl

to : ℕ → Bin
to zero    = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (n O) = 2 * from n
from (n I) = 1 + 2 * from n

_ : from (⟨⟩ I I O O) ≡ 12
_ = refl

_ : from (⟨⟩ O I O I) ≡ 5
_ = refl

law1 : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
law1 ⟨⟩ = refl
law1 (b O) = refl
law1 (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from (inc b O)
  ≡⟨⟩
    2 * from (inc b)
  ≡⟨ cong (2 *_) (law1 b) ⟩
    2 * (1 + (from b))
  ≡⟨ *-comm 2 (1 + (from b)) ⟩
    (1 + (from b)) * 2
  ≡⟨ *-distrib-+ 1 (from b) 2 ⟩
    2 + (from b) * 2
  ≡⟨ cong (2 +_) (*-comm (from b) 2) ⟩
    2 + 2 * (from b)
  ≡⟨⟩
    1 + (1 + 2 * (from b))
  ≡⟨⟩
    suc (from (b I))
  ∎

_ : to (from (⟨⟩ O O)) ≡ ⟨⟩
_ =
  begin
    to (from (⟨⟩ O O))
  ≡⟨⟩
    to (2 * (from (⟨⟩ O)))
  ≡⟨⟩
    to (2 * (2 * from ⟨⟩))
  ≡⟨⟩
    to (2 * (2 * zero))
  ≡⟨⟩
    to zero
  ≡⟨⟩
    ⟨⟩
  ∎

law3 : ∀ (n : ℕ) → from (to n) ≡ n
law3 zero = refl
law3 (suc n) =
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ law1 (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (law3 n) ⟩
    suc n
  ∎
