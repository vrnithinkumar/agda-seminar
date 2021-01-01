module agda_basics where

data Bool : Set where
  true : Bool
  false : Bool

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

infixl 6 _+_
infixl 7 _*_
infixr 8 !_
infix 5 if_then_else_
infixr 6 _::_

!_ : Bool → Bool
!_ true = false
!_ false = true

_+_ : Nat → Nat → Nat
zero + m = m
suc n + m = suc (n + m)

_*_ : Nat → Nat → Nat
zero * m = zero
suc n * m = m + ( n * m )

_||_ : Bool → Bool → Bool
false || x = x
true || _ = true

_&&_ : Bool → Bool → Bool
false && _ = false
true && x = x

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then  x else y = y


