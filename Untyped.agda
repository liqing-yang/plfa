module plfa.Untyped where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map)
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Product using (_×-dec_)


infix  4  _⊢_
infix  4  _∋_
infixl 5  _,_

infix  6  ƛ_
infix  6  ′_
infixl 7  _·_

data Type : Set where
  ★ : Type

η-★ : ∀ (x : Type) → ★ ≡ x
η-★ ★ = refl

η-⊤ : ∀ (x : ⊤) → tt ≡ x
η-⊤ tt = refl

open import plfa.part1.Isomorphism using (_≃_)

Type≃⊤ : Type ≃ ⊤
Type≃⊤ =
  record
    { to = λ _ → tt
    ; from = λ _ → ★
    ; from∘to = λ x → η-★ x
    ; to∘from = λ y → η-⊤ tt
    }
    
data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

Context→ℕ : Context → ℕ
Context→ℕ ∅ = zero
Context→ℕ (c , t) = suc (Context→ℕ c)

ℕ→Context : ℕ → Context
ℕ→Context zero = ∅
ℕ→Context (suc n) = ℕ→Context n , ★

Context≃ℕ : Context ≃ ℕ
Context≃ℕ =
  record
    { to = Context→ℕ
    ; from = ℕ→Context
    ; from∘to = λ{ ∅ → refl ; (c , ⋆) → {!!} }
    ; to∘from = λ{ zero → refl ; (suc n) → {!!} }
    }

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ----------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

data _⊢_ : Context → Type → Set where

  ′_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_ : ∀ {Γ}
    → Γ , ★ ⊢ ★
      ----------
    → Γ ⊢ ★

  _·_ : ∀ {Γ}
    → Γ ⊢ ★
    → Γ ⊢ ★
      ------
    → Γ ⊢ ★


