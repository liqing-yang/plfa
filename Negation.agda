module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x 

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x 

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x ((¬¬-intro x))

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

open import plfa.part1.Relations using (_<_; z<s; s<s)

<-irreflexive : ∀ {n : ℕ} → ¬(n < n)
<-irreflexive (s<s n<n) = <-irreflexive n<n

suc-≡ : ∀ {m n : ℕ}
  → suc m ≡ suc n
    -------------
  → m ≡ n
suc-≡ refl = refl


open import Data.Nat using (_>_; s≤s; z≤n)
open import Data.Product using (_,_)

data Trichotomy : ℕ → ℕ → Set where

  lll : ∀ {m n : ℕ}
    → (m < n) × ¬ (m ≡ n) × ¬ (n < m)
      --------
    → Trichotomy m n

  eee : ∀ {m n : ℕ}
    → ¬ (m < n) × (m ≡ n) × ¬ (n < m)
      --------
    → Trichotomy m n

  ggg : ∀ {m n : ℕ}
    → ¬ (m < n) × ¬ (m ≡ n) × (n < m)
      ---------
    → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = eee ((λ ()) , refl , (λ ()))
trichotomy zero (suc n) = lll (z<s , (λ ()) , (λ ()))
trichotomy (suc m) zero = ggg ((λ ()) , (λ ()) , z<s) 
trichotomy (suc m) (suc n) with trichotomy m n
...                             | lll (m<n , ¬m≡n , ¬m>n) = lll ( (s<s m<n) , (λ x → ¬m≡n ((suc-≡ x))) , (λ{ (s<s n<m) → ¬m>n n<m }))
...                             | eee (¬m<n , m≡n , ¬m>n) = eee ((λ{ (s<s m<n) → ¬m<n m<n }) , cong suc m≡n , λ{ (s<s n<m) → ¬m>n n<m })
...                             | ggg (¬m<n , ¬m≡n , m>n) = ggg ((λ{ (s<s m<n) → ¬m<n m<n }) , (λ{ x → ¬m≡n (suc-≡ x) }) , s<s m>n)


open import plfa.part1.Connectives using (→-distrib-⊎)
