module Util.DependentIf where

open import Basic

dite : {A : Bool → Set} → (b : Bool) → ((b ≡ true) → A true) → ((b ≡ false) → A false) → A b
dite true case-true _ = case-true refl
dite false _ case-false = case-false refl


dite' : {A : Set} (b : Bool) → ((b ≡ true) → A) → ((b ≡ false) → A) → A
dite' true case-true _ = case-true refl
dite' false _ case-false = case-false refl



dite'-true : {A : Set} (b : Bool) → (case-true : b ≡ true → A) (case-false : b ≡ false → A) → (e : b ≡ true) → dite' b case-true case-false ≡ case-true e
dite'-true true _ _ refl = refl
dite'-true false _ _ ()

dite'-false : {A : Set} (b : Bool) → (case-true : b ≡ true → A) (case-false : b ≡ false → A) → (e : b ≡ false) → dite' b case-true case-false ≡ case-false e
dite'-false true _ _ ()
dite'-false false _ _ refl = refl

dite'-LEM :
  {A : Set}
  (b : Bool)
  (case-true : b ≡ true → A)
  (case-false : b ≡ false → A) →
  (Σ[ e ∈ b ≡ true ] (dite' b case-true case-false ≡ case-true e)) ⊎
  (Σ[ e ∈ b ≡ false ] (dite' b case-true case-false ≡ case-false e))
dite'-LEM true _ _ = inj₁ (refl , refl)
dite'-LEM false _ _ = inj₂ (refl , refl)
