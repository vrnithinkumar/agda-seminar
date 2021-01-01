open import Level
open import Data.List
open import Data.Sum
open import Relation.Binary

module InsertionSort {ℓ ℓ₁ ℓ₂} (totalOrder : TotalOrder ℓ ℓ₁ ℓ₂) where

open TotalOrder totalOrder renaming (Carrier to A)
open IsTotalOrder  isTotalOrder renaming (trans to ≤-trans; total to _≤?_)

insert : A → List A → List A
insert x [] = [ x ]
insert x (y ∷ ys)
  with x ≤? y
...  | inj₁ x≤y = x ∷ y ∷ ys
...  | inj₂ y≤x = y ∷ insert x ys

insertion-sort : List A → List A
insertion-sort [] = []
insertion-sort (x ∷ xs) = insert x (insertion-sort xs)

module Properties where
  data _≤*_ (x : A) : List A → Set ( suc (ℓ ⊔ ℓ₁ ⊔ ℓ₂)) where
    [] : x ≤* []
    _∷_ : ∀ {y ys} → x ≤ y → x ≤* ys → x ≤* (y ∷ ys)

  ≤*-trans : ∀ {ys x y} → x ≤ y → y ≤* ys → x ≤* ys
  ≤*-trans {[]} _ _ = []
  ≤*-trans {z ∷ zs} x≤y (y≤z ∷ y≤*zs) = ≤-trans x≤y y≤z ∷ ≤*-trans x≤y y≤*zs

  data Sorted : List A → Set (suc (ℓ ⊔ ℓ₁ ⊔ ℓ₂)) where
    []  : Sorted []
    _∷_ : ∀ {x xs} → x ≤* xs → Sorted xs → Sorted (x ∷ xs)

  ≤*-insert : ∀ {ys y x} → x ≤ y → x ≤* ys → x ≤* insert y ys
  ≤*-insert {[]} x≤y _ = x≤y ∷ []
  ≤*-insert {z ∷ zs} {y} x≤y (x≤z ∷ x≤*zs)
    with y ≤? z
  ...  | inj₁ y≤z = x≤y ∷ (x≤z ∷ x≤*zs)
  ...  | inj₂ z≤y = x≤z ∷ ≤*-insert x≤y x≤*zs

  insert-preserves-sorted : ∀ x xs → Sorted xs → Sorted (insert x xs)
  insert-preserves-sorted _ [] [] = [] ∷ []
  insert-preserves-sorted x (y ∷ ys) (y≤*ys ∷ sys)
    with x ≤? y
  ...  | inj₁ x≤y = (x≤y ∷ ≤*-trans x≤y y≤*ys) ∷ (y≤*ys ∷ sys)
  ...  | inj₂ y≤x = ≤*-insert y≤x y≤*ys ∷ insert-preserves-sorted x ys sys

  insertion-sort-sorts : ∀ xs → Sorted (insertion-sort xs)
  insertion-sort-sorts [] = []
  insertion-sort-sorts (x ∷ xs) = insert-preserves-sorted x (insertion-sort xs) (insertion-sort-sorts xs)
