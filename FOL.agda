module FOL where

open import Basic hiding (all ; lookup)

data Var : Set where
  v : ℕ → Var

data Term : Set where
  c : ℕ → Term
  v : Var → Term

{-
 n is the number of binary relation symbols
-}

data FOL (n : ℕ) : Set where
  empty : FOL n -- equivalent to True
  rel : Fin n → Term → Term → FOL n
  ~ : FOL n → FOL n
  _&_ : FOL n → FOL n → FOL n
  _||_ : FOL n → FOL n → FOL n
  exists : Var → FOL n → FOL n
  all : Var → FOL n → FOL n

record PreInterpretation {n : ℕ} : Set₁ where
  field
   A : Set
   objs : ℕ → A
   rels : Fin n → (A → A → Set)

lookup : {A : Set} → List (Var × A) → A → Var → A
lookup [] default _ = default
lookup (((v k) , o) ∷ kvs) default (v x) = if (k eq x) then o else (lookup kvs default (v x))


I-helper :
  {n : ℕ} →
  (A : Set) →
  (o : ℕ → A) →
  (r : Fin n → (A → A → Set)) →
  (subs : List (Var × A)) →
  FOL n → Set
I-helper A o r subs empty = ⊥
I-helper A o r subs (rel R (c x) (c y)) = (r R) (o x) (o y)
I-helper A o r subs (rel R (c x) (v (v y))) = (r R) obj-x obj-y
  where
    obj-x = o x
    obj-y = lookup subs (o y) (v y)
I-helper A o r subs (rel R (v (v x)) (c y)) = (r R) obj-x obj-y
  where
    obj-x = lookup subs (o x) (v x)
    obj-y = o y
I-helper A o r subs (rel R (v (v x)) (v (v y))) = (r R) obj-x obj-y
  where
    obj-x : A
    obj-x = lookup subs (o x) (v x)

    obj-y : A
    obj-y = lookup subs (o y) (v y)
I-helper A o r subs (~ ϕ) = ¬ (I-helper A o r subs ϕ)
I-helper A o r subs (ϕ₁ & ϕ₂) = (I-helper A o r subs ϕ₁) × (I-helper A o r subs ϕ₂)
I-helper A o r subs (ϕ₁ || ϕ₂) = (I-helper A o r subs ϕ₁) ⊎ (I-helper A o r subs ϕ₂)
I-helper A o r subs (exists x ϕ) = Σ[ y ∈ A ] (I-helper A o r ((x , y) ∷ subs) ϕ)
I-helper A o r subs (all x ϕ) = (y : A) → (I-helper A o r ((x , y) ∷ subs) ϕ)


I :
  {n : ℕ} →
  (A : Set) →
  (o : ℕ → A) →
  (r : Fin n → (A → A → Set)) →
  FOL n → Set
I A o r ϕ = I-helper A o r [] ϕ


model : {n : ℕ} (T : FOL n) (p : PreInterpretation {n}) → Set
model {n} T p = I A objs rels T
  where
    open PreInterpretation p

_⊨_ : {n : ℕ} (T : FOL n) → (ϕ : FOL n) → Set₁
_⊨_ {n} T ϕ =  (p : PreInterpretation {n}) → (model {n} T p) → (model {n} ϕ p)

Th : {n : ℕ} → (T : FOL n) → (ϕ : FOL n) → Set₁
Th = _⊨_
