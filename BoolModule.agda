module BoolModule where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

¬¬ : Bool → Bool
¬¬ b = not (not b)

_&&_ : Bool → Bool → Bool
l && true = l
l && false = false

_||_ : Bool → Bool → Bool
l || true = true
l || false = l

-- This is comment
{- this is also a comment  -}

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

one = succ zero

_+_ : Nat → Nat → Nat
a + zero   = a
a + succ b =  succ (a + b)

id : {X : Set } → X → X
id x =  x

data List (A : Set) : Set where
  [] :  List A
  _::_ : A → List A → List A


data Maybe(A : Set) : Set where
  Nothing : Maybe A
  Just _ : A → Maybe A

head : {A : Set} → List A → Maybe A
head [] = Nothing
head (a :: as ) = Just a

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x :: x₁) =  f x :: map f x₁

data _×_(A B : Set) : Set where
  <_,_> : A → B → A × B

fst : {A B : Set} → A × B → A
fst < a , b > = a

snd : {A B : Set} → A × B → B
snd < a , b > = b

record _×`_ (A B : Set) : Set where
  constructor <_,_>`
  field
    f : A
    s : B

fst` : {A B : Set} → A ×` B → A
fst` = _×`_.f

data Vect (A : Set) : Nat → Set where
  [] : Vect A zero
  _::_ : {n : Nat} → A →  Vect A n →  Vect A (succ n)

head` : { A : Set} → { n : Nat} → Vect A (succ n) → A
head` (a :: as) = a

-- what is a : A here
data _≡_ {A : Set} (a : A) : A →  Set where
  refl : a ≡ a

onepp : ((succ zero) + (succ zero)) ≡ (succ (succ zero))
onepp = refl

dblneg : (b : Bool) → not (not b) ≡ b
dblneg true = refl
dblneg false = refl

sym : {A : Set} → (a a` : A) → a ≡ a` → a` ≡ a
sym a .a refl = refl

trans : {A : Set} → {a1 a2 a3 : A} → a1 ≡ a2 → a2 ≡ a3 → a1 ≡ a3
trans refl refl = refl


cong : {A B : Set} → (a₁ a₂ : A) → (f : A → B)  → a₁ ≡ a₂ → f a₁ ≡ f a₂
cong f refl  =  {!refl!}
