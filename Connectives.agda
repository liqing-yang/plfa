module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.part1.Isomorphism using (_≃_; _≲_; extensionality)
open plfa.part1.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y

record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B

open _×′_

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to = λ{⟨ x , y ⟩ → ⟨ y , x ⟩}
    ; from = λ{⟨ y , x ⟩ → ⟨ x , y ⟩}
    ; from∘to = λ{⟨ x , y ⟩ → refl}
    ; to∘from = λ{⟨ y , x ⟩ → refl}
    }

×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to = λ{ ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ{ ⟨ ⟨ x , y ⟩ , z  ⟩ → refl }
    ; to∘from = λ{ ⟨ x , ⟨ y , z ⟩ ⟩ → refl }
    }

open import plfa.Isomorphism using (_⇔_)
open _⇔_

⇔≃× : ∀ {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ{ A⇔B → ⟨ to A⇔B , from A⇔B ⟩ }
    ; from = λ{ ⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A } }
    ; from∘to = λ{ A⇔B → refl }
    ; to∘from = λ{ ⟨ A→B , B→A ⟩ → refl }
    }

data ⊤ : Set where

  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to = λ{ ⟨ ⊤ , A ⟩ → A }
    ; from = λ{ A  → ⟨ tt , A ⟩ }
    ; from∘to = λ{ ⟨ tt , A ⟩ → refl  }
    ; to∘from = λ{ A → refl }
    }

⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ =
  record
    { to = λ{ ⟨ A , tt ⟩ → A }
    ; from = λ{ A → ⟨ A , tt ⟩ }
    ; from∘to = λ{ ⟨ A , tt ⟩ → refl }
    ; to∘from = λ{ A → refl }
    }
{-
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎
-}

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B


  inj₂ :
      B
      -----
    → A ⊎ B

case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -------
  → C
case-⊎ A→C B→C (inj₁ A) = A→C A
case-⊎ A→C B→C (inj₂ B) = B→C B

η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infixr 1 _⊎_

⊎-comm : ∀ {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ{ (inj₁ x) → inj₂ x ;
              (inj₂ y) → inj₁ y }
    ; from = λ{ (inj₁ x) → inj₂ x ;
                (inj₂ x) → inj₁ x }
    ; from∘to = λ{ (inj₁ x) → refl ;
                   (inj₂ x) → refl }
    ; to∘from = λ{ (inj₁ x) → refl ;
                   (inj₂ x) → refl }
    }
⊎-assoc : ∀ {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = λ{ (inj₁ (inj₁ A)) → inj₁ A ;
              (inj₁ (inj₂ B)) → inj₂ (inj₁ B) ;
              (inj₂ C) → inj₂ (inj₂ C) }
    ; from = λ{ (inj₁ A) → inj₁ (inj₁ A) ;
                (inj₂ (inj₁ B)) → inj₁ (inj₂ B) ;
                (inj₂ (inj₂ C)) → inj₂ C }
    ; from∘to = λ{ (inj₁ (inj₁ A)) → refl ;
                   (inj₁ (inj₂ B)) → refl ;
                   (inj₂ C) → refl }
    ; to∘from = λ{ (inj₁ A) → refl ;
                   (inj₂ (inj₁ B)) → refl ;
                   (inj₂ (inj₂ C)) → refl}
    }

data ⊥ : Set where

⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()

uniq-⊥ : ∀ {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

⊥-identityˡ : ∀ {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ{ (inj₂ x) → x }
    ; from = λ{ x → inj₂ x }
    ; from∘to = λ{ (inj₂ x) → refl }
    ; to∘from = λ{ A → refl }
    }

⊥-identityʳ : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎

→-elim : ∀ {A B : Set}
  → (A → B)
  → A
    -------
  → B
→-elim L M = L M

η-→ : ∀ {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

currying : ∀ {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to = λ{ f → λ{ ⟨ x , y ⟩ → f x y } }
    ; from = λ{ g → λ{ x → λ y → g ⟨ x , y ⟩ } } 
    ; from∘to = λ{ f → refl }
    ; to∘from = λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl} }
    }

→-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to = λ{ f → ⟨ (λ{x → f (inj₁ x) })  , (λ{y → f (inj₂ y)}) ⟩ } 
    ; from = λ{ ⟨ g , h ⟩ → λ{ (inj₁ x) → g x ; (inj₂ y) → h y } }
    ; from∘to = λ{ f → extensionality λ{ (inj₁ x) → refl ; (inj₂ y) → refl} }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

→-distrib-× : ∀ {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to = λ{ f → ⟨ (λ{ x → proj₁ (f x) }) , (λ{ y → proj₂ (f y) }) ⟩ }
    ; from = λ{ ⟨ g , h ⟩ → λ{ x → ⟨ g x , h x ⟩ } }
    ; from∘to = λ{ f → extensionality λ{ x → η-× (f x) }  }
    ; to∘from = λ{ ⟨ g , h ⟩ → refl }
    }

×-distrib-⊎ : ∀ {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to = λ{ ⟨ inj₁ x , z ⟩ → inj₁ ⟨ x , z ⟩
            ; ⟨ inj₂ y , z ⟩ → inj₂ ⟨ y , z ⟩
            }
    ; from = λ{ (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
              ; (inj₂ ⟨ x , z ⟩) → ⟨ inj₂ x , z ⟩
              }
    ; from∘to = λ{ ⟨ inj₁ x , z ⟩ → refl
                 ; ⟨ inj₂ y , z ⟩ → refl
                 }
    ; to∘from = λ{ (inj₁ ⟨ x , z ⟩) → refl
                 ; (inj₂ ⟨ y , z ⟩) → refl
                 }
    }

⊎-distrib-× : ∀ {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to = λ{ (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
            ; (inj₂ z) → ⟨ inj₂ z , inj₂ z ⟩
            }
    ; from = λ{ ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
              ; ⟨ inj₁ x , inj₂ z ⟩ → inj₂ z
              ; ⟨ inj₂ z , _ ⟩ → inj₂ z
              }
    ; from∘to = λ{ (inj₁ ⟨ x , y ⟩) → refl
                 ; (inj₂ z) → refl
                 }
    }

⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , z ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩

⊎×-implies-×⊎ : ∀ {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ z , h ⟩) = ⟨ inj₂ z , inj₂ h ⟩
