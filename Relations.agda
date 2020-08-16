module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _>_)
open import Data.Nat.Properties using (+-comm; *-comm)

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
      → zero ≤ n
      
  s≤s : ∀ {m n : ℕ}
      → m ≤ n
      --------
      → suc m ≤ suc n

infix 4 _≤_

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    -------
  → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ}
  -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
      → Total m n

data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
      ---------
    → Total′ m n


  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
      ---------
    → Total′ m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    --------------
  → n + p ≤ n + q

+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    --------------
  → m + p ≤ n + p

+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    ---------
  → m + p ≤ n + q

*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    ------------
  → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    ----------------
  → m * p ≤ n * p

*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    ------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      ------------
    → suc m < suc n


<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -------
  → m < p

<-trans z<s (s<s m<n) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

data Trichotomy : ℕ → ℕ → Set where

  lll : ∀ {m n : ℕ}
    → m < n
      --------
    → Trichotomy m n

  eee : ∀ {m n : ℕ}
    → m ≡ n
      --------
    → Trichotomy m n

  ggg : ∀ {m n : ℕ}
    → n < m
      ---------
    → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = eee refl
trichotomy zero (suc n) = lll z<s
trichotomy (suc m) zero = ggg z<s 
trichotomy (suc m) (suc n) with trichotomy m n
...                          | lll m<n = lll (s<s m<n)
...                          | eee m≡n = eee (cong suc m≡n)
...                          | ggg n<m = ggg (s<s n<m)


+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    ------
  → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------
  → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -----------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

≤-iff-< : ∀ (m n : ℕ)
  → suc m ≤ n
    ---------
  → m < n

≤-iff-< zero (suc n) _ = z<s
≤-iff-< (suc m) n (s≤s m≤n) = {!!}

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc   : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero en = en
e+e≡e (suc om) en = suc (o+e≡o om en)

o+e≡o (suc em) en = suc (e+e≡e em en)

-- e+e≡e zero     en  =  en
-- e+e≡e (suc om) en  =  suc (o+e≡o om en)

-- o+e≡o (suc em) en  =  suc (e+e≡e em en)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    -----------
  → even (m + n)

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    --------
  → odd (m + n)

e+o≡o zero on = on
e+o≡o (suc om) on = suc (o+o≡e om on)

o+o≡e (suc em) (suc en) = suc (e+o≡o em (suc en))


