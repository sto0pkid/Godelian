module Util.Vec where

open import Basic
open import Data.Vec using (head)


Vec-get : {A : Set} {n : ℕ} → Vec A n → Fin n → A
Vec-get {A} {0} [] ()
Vec-get {A} {suc n} (x ∷ xs) zero = x
Vec-get {A} {suc n} (x ∷ xs) (suc m) = Vec-get xs m

vec-map : {l₁ l₂ : Level} → {A : Set l₁} → {B : Set l₂} → {n : ℕ} → (f : A → B) → Vec A n → Vec B n
vec-map f [] = []
vec-map f (x ∷ xs) = f x ∷ vec-map f xs

vec-append : {A : Set} → {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
vec-append {A} {0} {m} [] v = v
vec-append {A} {suc n} {m} (x ∷ xs) v = x ∷ (vec-append xs v)


vec-flatten : {A : Set} → {n m : ℕ} → Vec (Vec A m) n → Vec A (n * m)
vec-flatten {A} {0} {m} [] = []
vec-flatten {A} {suc n} {m} (v ∷ vs) = vec-append v (vec-flatten vs)

Vector-find : {A : Set} {n : ℕ} → (P : A → Bool) → Vec A n → Maybe A
Vector-find {A} {n} P [] = nothing
Vector-find {A} {n} P (x ∷ xs) = if (P x) then (just x) else (Vector-find P xs)

vec-tail : {A : Set} {n : ℕ} → Vec A (1 + n) → Vec A n
vec-tail (x ∷ xs) = xs

List→Vec : {A : Set} → (l : List A) → Vec A (length l)
List→Vec [] = []
List→Vec (x ∷ xs) = x ∷ (List→Vec xs)

index-suc : {A : Set} {n : ℕ} → (v : Vec A (1 + n)) → (x : Fin n) → (Vec-get (vec-tail v) x) ≡ (Vec-get v (suc x))
index-suc {A} {0} v ()
index-suc {A} {suc n} (x ∷ xs) k = refl

Vec-any : {A : Set} {n : ℕ} → (v : Vec A n) → (P : A → Set) → Set
Vec-any {_} {n} v P = Σ[ i ∈ (Fin n) ] (P (Vec-get v i ))

Vec-all : {A : Set} {n : ℕ} → (v : Vec A n) → (P : A → Set) → Set
Vec-all {_} {n} v P = (i : Fin n) → P (Vec-get v i)

Vec-any-monotonic : {A : Set} {n : ℕ} → (P : A → Set) → {v : Vec A n} → Vec-any v P → (a : A) → Vec-any (a ∷ v) P
Vec-any-monotonic {A} {n} P {v} (i , Pvi) a = suc i , (resp P (index-suc (a ∷ v) i) Pvi)

Vec-foldr : {A B : Set} {n : ℕ} → (A → B → B) → B → Vec A n → B
Vec-foldr f z [] = z
Vec-foldr f z (x ∷ xs) = f x (Vec-foldr f z xs)

Vec-sum : {n : ℕ} → Vec ℕ n → ℕ
Vec-sum v = Vec-foldr _+_ 0 v

Vec→List : {A : Set} {n : ℕ} → Vec A n → List A
Vec→List [] = []
Vec→List (x ∷ xs) = x ∷ (Vec→List xs)

Vec→List-preserves-length : {A : Set} {n : ℕ} → (v : Vec A n) → length (Vec→List v) ≡ n
Vec→List-preserves-length [] = refl
Vec→List-preserves-length {n = (suc n)} (x ∷ xs) = cong suc (Vec→List-preserves-length xs)

Vec-ext : {i : Level} {A : Set i} {n : ℕ} {x y : A} {xs ys : Vec A n} → x ≡ y → xs ≡ ys → _≡_ {i} {Vec A (1 + n)} (x ∷ xs) (y ∷ ys)
Vec-ext refl refl = refl

Vec-ext2 : {i : Level} {A : Set i} {n : ℕ} (xs : Vec A (1 + n)) → xs ≡ (Data.Vec.head xs) ∷ (Data.Vec.tail xs)
Vec-ext2 (x ∷ xs) = refl

Vec-empty : {i : Level} {A : Set i} → (xs : Vec A 0) → xs ≡ []
Vec-empty [] = refl

Vec1-ext : {i : Level} {A : Set i} → (xs : Vec A 1) → xs ≡ ((Data.Vec.head xs) ∷ [])
Vec1-ext (x ∷ []) = refl



List→Vec-length : {A : Set} {n : ℕ} → (l : List A) → length l ≡ n → Vec A n
List→Vec-length {A} {0} [] _ = []
List→Vec-length {A} {suc n} l@(x ∷ xs) |l|≡1+n = x ∷ (List→Vec-length xs (suc-injective |l|≡1+n))

List→Vec→List : {A : Set} {n : ℕ} → (l : List A) → (|l|≡n : length l ≡ n) → Vec→List (List→Vec-length l |l|≡n) ≡ l
List→Vec→List {A} {0} [] _ = refl
List→Vec→List {A} {suc n} l@(x ∷ xs) |l|≡1+n = cong (_∷_ x) (List→Vec→List xs (suc-injective |l|≡1+n))
