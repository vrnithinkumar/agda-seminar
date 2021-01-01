open import Agda.Builtin.Bool


module InSort where

  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  data Either (A : Set) (B : Set) : Set where
    left  : A → Either A B
    right : B → Either A B

  data Empty : Set where

  absurd : {X : Set} → Empty → X
  absurd ()

  infixr 40 _::_
  infix 3 ¬_

  ¬_ : Set → Set
  ¬ X = X → Empty

  [_,_] : ∀ {A B} {C : Set} → (A → C) → (B → C) → Either A B → C
  [ f , g ] (left x)  = f x
  [ f , g ] (right x) = g x

{-
  insert : A → List A → List A
  insert y [] = y :: []
  insert y (x :: xs) with x < y
  ... | true = x :: insert y xs
  ... | false = y :: x :: xs

  sort : List A → List A
  sort [] = []
  sort (x :: xs) = insert x (sort xs)
-}

  foldr : ∀ {A} {B : Set} → (A → B → B) → B → List A → B
  foldr f b []       = b
  foldr f b (a :: as) = f a (foldr f b as)

  Rel : Set → Set₁
  Rel X = X → X → Set


  Decidable : ∀ {X} → Rel X → Set
  Decidable R = ∀ x y → Either (R x y) (¬ (R x y))

  record Equivalence {X} (_≈_ : Rel X) : Set₁ where
    field
      refl  : ∀ {x}     → x ≈ x
      sym   : ∀ {x y}   → x ≈ y → y ≈ x
      trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

  record TotalOrder {X} (_≈_ : Rel X) (_≤_ : Rel X) : Set₁ where
    field
      antisym     : ∀ {x y}   → x ≤ y → y ≤ x → x ≈ y
      trans       : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
      total       : ∀ x y     → Either (x ≤ y) (y ≤ x)
      reflexive   : ∀ {x y}   → x ≈ y → x ≤ y
      equivalence : Equivalence _≈_

  module Sort {X} {_≈_ _≤_ : Rel X} (_≤?_ : Decidable _≤_) (ord : TotalOrder _≈_ _≤_) where
         open TotalOrder ord using (total; equivalence)
         open Equivalence equivalence using (refl)

         data ⊥X⊤ : Set where
           ⊤ ⊥ : ⊥X⊤
           ⟦_⟧ : X → ⊥X⊤
         data _≤̂_ : Rel ⊥X⊤ where
           ⊥≤̂     : ∀ {x} → ⊥ ≤̂ x
           ≤̂⊤     : ∀ {x} → x ≤̂ ⊤
           ≤-lift : ∀ {x y} → x ≤ y → ⟦ x ⟧ ≤̂ ⟦ y ⟧
         data OList (l u : ⊥X⊤) : Set where
           nil  : l ≤̂ u → OList l u
           cons : ∀ x (xs : OList ⟦ x ⟧ u) → l ≤̂ ⟦ x ⟧ → OList l u

         toList : ∀ {l u} → OList l u → List X
         toList (nil _)       = []
         toList (cons x xs _) = x :: toList xs

         insert : ∀ {l u} x → OList l u → l ≤̂ ⟦ x ⟧ → ⟦ x ⟧ ≤̂ u → OList l u
         insert y (nil _)         l≤y y≤u = cons y (nil y≤u) l≤y
         insert y (cons x xs l≤x) l≤y y≤u with y ≤? x
         insert y (cons x xs l≤x) l≤y y≤u | left  y≤x = cons y (cons x xs (≤-lift y≤x)) l≤y
         insert y (cons x xs l≤x) l≤y y≤u | right y>x =
           cons x (insert y xs ([ ≤-lift , (λ y≤x → absurd (y>x y≤x)) ] (total x y)) y≤u) l≤x

         isort′ : List X → OList ⊥ ⊤
         isort′ = foldr (λ x xs → insert x xs ⊥≤̂ ≤̂⊤) (nil ⊥≤̂)

         isort : List X → List X
         isort xs = toList (isort′ xs)
