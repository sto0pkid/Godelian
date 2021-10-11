module Util.List where

open import Basic
open import Data.Vec using (head)
open import Util.Bool

_∷?_ : {A : Set} → Maybe A → List A → List A
nothing ∷? xs = xs
(just x) ∷? xs = x ∷ xs



_[_]? : {A : Set} → List A → ℕ → Maybe A
_[_]? [] _ = nothing
(x ∷ xs) [ 0 ]? = just x
(x ∷ xs) [ (suc n) ]? = xs [ n ]?

_[_]:=_ : {A : Set} → List A → ℕ → A → List A
_[_]:=_ [] _ _ = []
(x ∷ xs) [ 0 ]:= a = (a ∷ xs)
(x ∷ xs) [ (suc n) ]:= a = (x ∷ (xs [ n ]:= a))

_[[_]] : {A : Set} → List A → ℕ × A → A
[] [[ _ , a ]] = a
(x ∷ xs) [[ 0 , _ ]] = x
(x ∷ xs) [[ (suc n) , a ]] = xs [[ n , a ]]

get : {A : Set} → List A → ℕ → Maybe A
get l n = (reverse l) [ n ]?

get-default : {A : Set} → A → List A → ℕ → A
get-default a l n = (reverse l) [[ n , a ]]

set : {A : Set} → List A → ℕ → A → List A
set l n x = reverse ((reverse l) [ n ]:= x)


find : {A : Set} (P : A → Bool) → List A → Maybe A
find {A} P [] = nothing
find {A} P (x ∷ xs) = if (P x) then (just x) else (find P xs)



lookupℕ : {A : Set} → List A → ℕ → Maybe A
lookupℕ [] _ = nothing
lookupℕ (x ∷ xs) 0 = just x
lookupℕ (x ∷ xs) (suc n) = lookupℕ xs n

lookupℕ-end : {A : Set} → List A → ℕ → Maybe A
lookupℕ-end l n = lookupℕ (reverse l) n

lookup< : {A : Set} → (l : List A) → (n : ℕ) → (n < length l) → A
lookup< [] _ ()
lookup< (x ∷ xs) 0 _ = x
lookup< l@(x ∷ xs) (suc n) (s≤s n<|xs|) = lookup< xs n n<|xs|





match : {A : Set} → (A → Bool) → List A → Bool
match _ []       = false
match P (x ∷ xs) = (P x) or (match P xs)

sublist : {A : Set} → (l₁ l₂ : List A) → Set
sublist {A} l₁ l₂ = Σ[ x ∈ List A ] (Σ[ y ∈ List A ] (l₂ ≡ (x ++ l₁) ++ y))

list-subset : {A : Set} → (l₁ l₂ : List A) → Set
list-subset {A} l₁ l₂ = (i₁ : Fin (length l₁)) → Σ[ i₂ ∈ Fin (length l₂) ] (lookup l₁ i₁ ≡ lookup l₂ i₂)

list-subset< : {A : Set} → (l₁ l₂ : List A) → Set
list-subset< {A} l₁ l₂ = (i₁ : ℕ) → (i₁<|l₁| : i₁ < (length l₁)) → Σ[ i₂ ∈ ℕ ] (Σ[ i₂<|l₂| ∈ i₂ < (length l₂) ] (lookup< l₁ i₁ i₁<|l₁| ≡ lookup< l₂ i₂ i₂<|l₂|))


pop : {A : Set} → List A → List A
pop [] = []
pop (x ∷ xs) = xs


list-subset? : {A : Set} → List A → List A → Set
list-subset? {A} l₁ l₂ = (i : ℕ) (x : A) → l₁ [ i ]? ≡ just x → Σ[ j ∈ ℕ ] (l₂ [ j ]? ≡ just x)

list-ordered-subset? : {A : Set} → List A → List A → Set
list-ordered-subset? {A} l₁ l₂ = (i : ℕ) (x : A) → l₁ [ i ]? ≡ just x → Σ[ j ∈ ℕ ] ( i ≤ j × l₂ [ j ]? ≡ just x)


flatten : {A : Set} → List (List A) → List A
flatten nested = foldr _++_ [] nested


list-product : {A B : Set} → List A → List B → List (A × B)
list-product []       _  = []
list-product (a ∷ as) l₂ = ((map (λ x → a , x)) l₂) ++ (list-product as l₂)

filter : {A : Set} → (A → Bool) → List A → List A
filter P [] = []
filter P (x ∷ xs) = if (P x) then (x ∷ (filter P xs)) else (filter P xs)


_⊗_ : {A B : Set} → List A → List B → List (A × B)
_⊗_ = list-product
