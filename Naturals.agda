module plfa.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

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

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin
  
inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (h O) = h I
inc (h I) = inc h O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
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
