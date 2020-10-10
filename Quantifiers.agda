module plfa.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    ---------------------
  → B M
∀-elim L M = L M

∀-distrib-× : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× {A} =
  record
    { to = λ{ f → ⟨ (λ x → proj₁ (f x)) , (λ x → proj₂ (f x)) ⟩ }
    ; from = λ{ ⟨ fst , snd ⟩ → λ x → ⟨ fst x , snd x ⟩ }
    ; from∘to = λ{ f → refl }
    ; to∘from = λ{ ⟨ fst , snd ⟩ → refl }
    }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (_⊎_.inj₁ f) x = _⊎_.inj₁ (f x)
⊎∀-implies-∀⊎ (_⊎_.inj₂ g) x = _⊎_.inj₂ (g x)

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set}

∀-× : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-× =
  record
    { to = λ{ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩ }
    ; from = λ{ ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → λ{ aa → Baa ; bb → Bbb ; cc → Bcc } }
    ; from∘to = λ{ f → {!!} }
    ; to∘from = λ{ ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → refl }
    }
