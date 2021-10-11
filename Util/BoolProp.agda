module Util.BoolProp where

open import Basic
open import Util.Bool


not-or-lemma : (A B : Bool) → A or B ≡ false → A ≡ false × B ≡ false
not-or-lemma true true ()
not-or-lemma true false ()
not-or-lemma false true ()
not-or-lemma false false _ = refl , refl

process-of-eliminationₗ : {A B : Bool} → A or B ≡ true → A ≡ false → B ≡ true
process-of-eliminationₗ {true}  {_}     _  ()
process-of-eliminationₗ {false} {true}  _  _ = refl
process-of-eliminationₗ {false} {false} ()

process-of-eliminationᵣ : {A B : Bool} → A or B ≡ true → B ≡ false → A ≡ true
process-of-eliminationᵣ {_}     {true}  _  () 
process-of-eliminationᵣ {true}  {false} _  _ = refl
process-of-eliminationᵣ {false} {false} ()


¬true→false : (A : Bool) → not A ≡ true → A ≡ false
¬true→false true ()
¬true→false false _ = refl

¬≡→≡¬ : {A B : Bool} → A ≢ B → A ≡ not B
¬≡→≡¬ {true}  {true}  true≢true   = ⊥-elim (true≢true refl)
¬≡→≡¬ {true}  {false} _           = refl
¬≡→≡¬ {false} {true}  _           = refl
¬≡→≡¬ {false} {false} false≢false = ⊥-elim (false≢false refl) 


if-lemma : {A : Set} → (b : Bool) → (a₁ a₂ : A) → ((if b then a₁ else a₂) ≡ a₁) ⊎ ((if b then a₁ else a₂) ≡ a₂)
if-lemma true _ _ = inj₁ refl
if-lemma false _ _ = inj₂ refl


Bool-LEM : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
Bool-LEM true = inj₁ refl
Bool-LEM false = inj₂ refl

true≠false : true ≢ false
true≠false ()

eq-∧ : {A B : Set} (eq-A : A → A → Bool) (eq-B : B → B → Bool) → (A × B) → (A × B) → Bool
eq-∧ _eq-A_ _eq-B_ (a , b) (a' , b') = (a eq-A a') and (b eq-B b')

if-lemma2 : {A : Set} (b : Bool) (c : Bool) → (if b then true else c) ≡ b or c
if-lemma2 true _ = refl
if-lemma2 false _ = refl
