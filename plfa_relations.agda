import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

module plfa_relations where
  data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ} → zero ≤ n
    s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

  _ : 2 ≤ 4
  _ = s≤s (s≤s z≤n)

  inv-s≤s : ∀ {m n : ℕ}
    → suc m ≤ suc n
    -------------
    → m ≤ n
  inv-s≤s (s≤s m≤n) = m≤n

  inv-z≤n : ∀ {m : ℕ}
    → m ≤ zero
    --------
    → m ≡ zero
  inv-z≤n z≤n = refl

  -- Reflexivity
  ≤-refl : ∀ {n : ℕ}
    -----
    → n ≤ n
  ≤-refl {zero} = z≤n
  ≤-refl {suc n} = s≤s ≤-refl

  ≤-trans : ∀ {m n p : ℕ}
    → m ≤ n
    → n ≤ p    
    → m ≤ p
  ≤-trans z≤n n = z≤n
  ≤-trans (s≤s m) n = {!!}
