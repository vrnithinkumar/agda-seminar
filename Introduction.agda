{-# OPTIONS --without-K #-}

module Introduction where

open import Agda.Primitive

{- excerpt from HoTT book, p. 11: Comparing points of view on type-theoretic operations
| Logic               | Types           |
| :------------------ | :-------------- |
| proposition         | A               |
| proof               | a : A           |
| ⊥, ⊤                |  𝟘, 𝟙           |
| A ∨ B               | A + B           |
| A ∧ B               | A × B           |
| A ⟹ B              |  A → B          |
| ∃ x ∈ A . B(x)      | Σ (x:A) B(x)    |
| ∀ x ∈ A . B(x)      | Π (x:A) B(x)    |
| equality =          | Id_A            |
| predicate           | B(x)            |
| conditional proof   | b(x) : B(x)     |
-}


{-
## Symbols
In Emacs' agda-mode we can easily write many Unicode symbols, e.g. 𝔹, ℕ, →, α, …
List of symbols for example here: https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html
Some frequently used symbols:
* \Ga → α, \Gb β, ...
* \b{B,N,0,1,...} → 𝔹, ℕ, 𝟘, 𝟙, ...
* \st → ⋆ ✦ ✧ ✶ ... (different stars, check status bar and move the cursor to select one)
* \lr (pos. 7) → ⟺
* \== → ≡
* \< → ⟨
* \> → ⟩
* \qed → ∎

## Emacs cheat sheet (C - Ctrl; M - meta key, usually Alt or Windows key)
C-c C-l save + load file into agda
C-c C-c case split
C-c C-s solve constraints

M-x describe-char (move cursor over a symbol, then enter the command, it will show you how to type the symbol)

C-x C-s save file
C-x C-c exit
-}


-- Types 'live' in so called universes (sorts).
-- The fundamental universe is called 'Set'.


------------------------------------------------------------------------
-- Define basic data types
------------------------------------------------------------------------
data 𝟘 : Set where

data 𝟙 : Set where
  ★ : 𝟙

data 𝔹 : Set where
  false : 𝔹
  true : 𝔹

-- example: write a function using 𝔹
_&&_ : 𝔹 → 𝔹 → 𝔹
false && y = false
true  && y = y

-- example: mixfix notation
if_then_else_ : {A : Set} → 𝔹 → A → A → A
if false then x else y = y
if true  then x else y = x

------------------------------------------------------------------------
-- dependent pair type
------------------------------------------------------------------------
record Σ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor
    _,_
  field
    π₁ : A
    π₂ : B π₁


-- product type
_×_ : ∀ {ℓ₁ ℓ₂} → ∀ (A : Set ℓ₁) (B : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
A × B = Σ A (λ x → B)

-- examples
_ : 𝔹 × 𝔹
_ = (true , false)

_ : Σ 𝔹 (λ {true → 𝔹 ; false → 𝟙})
_ = false , ★
--_ = true , true
--_ = true , false

------------------------------------------------------------------------
-- coproduct type
------------------------------------------------------------------------
data _⊎_ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  inl : (a : A) → A ⊎ B
  inr : (b : B) → A ⊎ B

-- example
_ : 𝔹 ⊎ 𝟙
_ = inl true
--_ = inr ★

------------------------------------------------------------------------
-- Identity type / Propositional equality
------------------------------------------------------------------------
data _≡_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  refl : ∀ {x} → x ≡ x

-- symmetry of ≡
sym≡ : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → b ≡ a
sym≡ refl = refl

-- transitivity of ≡
_∘_ : ∀ {ℓ} {A : Set ℓ} {a b c : A} →
      (a ≡ b) → (b ≡ c) → (a ≡ c)
refl ∘ refl = refl

-- function composition
_∙_ : ∀{ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
      (f : B → C) → (g : A → B) → (A → C)
f ∙ g = λ a → f (g a)

------------------------------------------------------------------------
-- Equivalence
record Eq {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  --constructor makeEq
  constructor »⟹«:_»⟸«:_∎
  field
    fun : A → B
    inv : B → A

syntax Eq A B = A ⟺ B

symEq : ∀{ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → Eq A B → Eq B A
symEq i = »⟹«: (Eq.inv i)
          »⟸«: (Eq.fun i) ∎

transEq : ∀{ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} →
          Eq A B → Eq B C → Eq A C
transEq i j = »⟹«: Eq.fun j ∙ Eq.fun i
              »⟸«: Eq.inv i ∙ Eq.inv j ∎


------------------------------------------------------------------------
-- Problem:
-- Identity and equivalence proofs get confusing fast, because
-- when using _∘_ and transEq we don't see any intermediate steps.
ex∘ : {A : Set} {a b c : A} → (p : a ≡ b) → (q : c ≡ b) → a ≡ c
ex∘ {A} {a} {b} {c} p q = p ∘ (sym≡ q)

-- Solution:
-- ≡-Reasoning and ⟺-Reasoning modules, which define nice syntax for displaying intermediate steps


module ≡-Reasoning {a} {A : Set a} where
  -- aus stdlib übernommen

  infix  3 _∎
  infixr 2 _≡⟨⟩_ step-≡ step-≡˘
  infix  1 begin_

  begin_ : ∀{x y : A} → x ≡ y → x ≡ y
  begin_ x≡y = x≡y

  _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  step-≡ : ∀ (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ y≡z x≡y = x≡y ∘ y≡z

  step-≡˘ : ∀ (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
  step-≡˘ _ y≡z y≡x = (sym≡ y≡x) ∘ y≡z

  _∎ : ∀ (x : A) → x ≡ x
  _∎ _ = refl

  syntax step-≡  x y≡z x≡y = x ≡⟨  x≡y ⟩ y≡z
  syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z


open ≡-Reasoning

-- example:
exReasoning : {A : Set} {a b c : A} → (p : a ≡ b) → (q : c ≡ b) → a ≡ c
exReasoning {A} {a} {b} {c} p q = begin
    a
  ≡⟨ p ⟩
    b
  ≡˘⟨ q ⟩
    c ∎

------------------------------------------------------------------------
--- Natural numbers and induction
------------------------------------------------------------------------
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

one = succ zero
two = succ (succ zero)

_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
succ m * n = n + (m * n)

-- congruence (functions respect equalities; sometimes called ap)
cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl



-- To perform induction proofs we usually need a recursive call
-- and cong to exhibit the induction step

+-zero : (m : ℕ) → (m + zero) ≡ m
+-zero zero = refl
+-zero (succ m) = cong succ (+-zero m)

+-succ : (m n : ℕ) → (m + succ n) ≡ (succ m + n)
+-succ zero n = refl
+-succ (succ m) n = cong succ (+-succ m n)

+-comm : (m n : ℕ) → (m + n) ≡ (n + m)
+-comm zero n = sym≡ (+-zero n)
+-comm (succ m) n = begin
    (succ m + n)
  ≡⟨⟩
    succ (m + n)
  ≡⟨ cong succ (+-comm m n) ⟩
    succ (n + m)
  ≡⟨⟩
    succ n + m
  ≡˘⟨ +-succ n m ⟩
    (n + succ m) ∎

n+n≡n*2 : (n : ℕ) → (n + n) ≡ (n * two)
n+n≡n*2 zero = refl
n+n≡n*2 (succ n) = begin
    succ (n + succ n)
  ≡⟨ cong succ (+-succ n n) ⟩
    succ (succ n + n)
  ≡⟨⟩
    succ (succ (n + n))
  ≡⟨⟩
    two + (n + n)
  ≡⟨ cong (two +_) (n+n≡n*2  n) ⟩
    two + (n * two)
  ≡⟨⟩
    (succ n * two) ∎



------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

-- Problem: We want to put a function into out product, but Agda complains:
--_ : (𝔹 → Set) × 𝟙
--_ = {!!}

-- What's the type of (𝔹 → Set)? Agda can infer the type for you, type: C-c C-d 𝔹 → Set
-- Agda will tell you that it has type Set₁.

-- Solution: introduce universe levels:
-- Set is Set₀
-- Set₀ : Set₁
-- Set₁ : Set₂
-- ...

-- same problem with another example:
--_ : {p q : Set} → (q ≡ p) ×' 𝟙
--_ = ?
