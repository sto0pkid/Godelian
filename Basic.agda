module Basic where

open import Agda.Primitive public
open import Data.Bool public using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; _xor_ ; if_then_else_)
open import Data.Empty public using (⊥ ; ⊥-elim)
open import Data.Fin public using (Fin ; zero ; suc ; toℕ ; fromℕ ; fromℕ< ; raise ; cast ; inject+)
open import Data.Fin.Properties public using (toℕ-fromℕ<)
open import Data.List public using (List ; [] ; _∷_ ; [_] ; length ; _++_ ; map ; foldl ; foldr ; reverse ; any ; all ; lookup ; replicate ; sum ; product)
open import Data.List.Properties public using (length-++ ; length-map)
open import Data.Maybe public using (Maybe ; nothing ; just ; is-nothing ; is-just) renaming (map to Maybe-map)
open import Data.Nat public using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_ ; pred ; _<_ ; _≤_ ; _>_ ; _≥_ ; _≮_ ; _≰_ ; _≯_ ; _≱_ ; z≤n ; s≤s) renaming (_<ᵇ_ to _lt_ ; _∸_ to _-_ ; _≡ᵇ_ to _eq_ ; _⊔_ to max)
open import Data.Nat.Properties public using (+-assoc ; +-comm ; +-identityˡ ; +-identityʳ ; +-identity ; 1+n≢0 ; ≤-step ; ≤-reflexive ;  ≤-refl ; ≤-trans ; ≤-antisym ; <-irrefl ; <-transʳ ; <-transˡ ; n≤1+n ; m<n⇒m≤1+n ;  m≤m+n ; m≤n+m ; m<n+m ; m<m+n ; >⇒≢ ; <⇒≱ ; ≮⇒≥ ; n≢0⇒n>0  ; <⇒≤ ; ≤∧≢⇒< ; 0<1+n ; ⊔-identityʳ ;  suc-injective ; ≤-isPartialOrder ; module ≤-Reasoning; *-comm ; *-zeroʳ ; *-zeroˡ ; *-identityʳ ; m<n⇒n≢0 ; _≟_ ; +-mono-<-≤ ; *-mono-≤)
open import Data.Nat.GeneralisedArithmetic public using (fold)
open import Data.Nat.DivMod public using (_/_ ; _%_ ; m≡m%n+[m/n]*n ; m≤n⇒m%n≡m ; [m+kn]%n≡m%n ; m*n%n≡0 ; +-distrib-/ ; m<n⇒m/n≡0 ; m*n/n≡m ; m%n<n ; /-mono-≤ ; m/n*n≤m)
open import Data.Product public using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ ; Σ-syntax)
open import Data.String public using (String)
open import Data.Sum public using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit public using (⊤) renaming (tt to unit)
open import Data.Vec public using (Vec ; [] ; _∷_ ; toList ; fromList)
open import Function.Base public using (id ; _∘_)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.PropositionalEquality public using (_≡_ ; refl ; _≢_ ; resp ; cong ; module ≡-Reasoning ; ≢-sym) renaming (sym to ≡-sym ; trans to ≡-trans )
open import Relation.Nullary public using (¬_)



pattern 1+ x = suc x



contrapositive : {A B : Set} → (A → B) → (¬ B → ¬ A)
contrapositive f ¬B a = ¬B (f a)

_↔_ : {i j : Level} → Set i → Set j → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)


coerce : {i : Level} → {A B : Set i} → A ≡ B → A → B
coerce refl a = a


≡-Irrelevance : {A : Set} {x y : A} → (e₁ e₂ : x ≡ y) → e₁ ≡ e₂
≡-Irrelevance refl refl = refl



{-
 Disjoint union _⊎_
-}

⊎-LEM : {A B : Set} → (option : A ⊎ B) → (Σ[ a ∈ A ] (option ≡ inj₁ a)) ⊎ (Σ[ b ∈ B ] (option ≡ inj₂ b))
⊎-LEM (inj₁ a) = inj₁ (a , refl)
⊎-LEM (inj₂ b) = inj₂ (b , refl)


mk-inl : (A B : Set) → A → A ⊎ B
mk-inl A B a = inj₁ a

mk-inr : (A B : Set) → B → A ⊎ B
mk-inr A B b = inj₂ b


process-of-elimination : {A B : Set} → A ⊎ B → ¬ A → B
process-of-elimination (inj₁ a) ¬A = ⊥-elim (¬A a)
process-of-elimination (inj₂ b) _ = b

process-of-elimination-r : {A B : Set} → A ⊎ B → ¬ B → A
process-of-elimination-r (inj₁ a) _ = a
process-of-elimination-r (inj₂ b) ¬B = ⊥-elim (¬B b)

⊎-elim : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
⊎-elim case-A _ (inj₁ a) = case-A a
⊎-elim _ case-B (inj₂ b) = case-B b


{-
  Cartesian product _×_
-}

×-ext : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
×-ext refl refl = refl

×-ext₂ : {A B : Set} → {a₁ a₂ : A} {b₁ b₂ : B} → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂ × b₁ ≡ b₂
×-ext₂ refl = refl , refl


{-
  De Morgan

-}

demorgan-¬∨ : {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
demorgan-¬∨ ¬[A∨B] = (λ a → ¬[A∨B] (inj₁ a)) , (λ b → ¬[A∨B] (inj₂ b))

demorgan-∨¬ : {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
demorgan-∨¬ (inj₁ ¬A) (a , _) = ¬A a
demorgan-∨¬ (inj₂ ¬B) (_ , b) = ¬B b

demorgan-×¬ : {A B : Set} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
demorgan-×¬ (¬A , _) (inj₁ a) = ¬A a
demorgan-×¬ (_ , ¬B) (inj₂ b) = ¬B b

-- The last one is non-constructive ; we don't know whether it's ¬A that's true or ¬B that's true
{-
demorgan-¬× : {A B : Set} → ¬ (A × B) → (¬ A) ⊎ (¬ B)
-}




{-
  Maybe
-}

Maybe-LEM : {A : Set} → (m : Maybe A) → (m ≡ nothing) ⊎ (Σ[ a ∈ A ] (m ≡ (just a)))
Maybe-LEM nothing = inj₁ refl
Maybe-LEM (just a) = inj₂ (a , refl)


nothing≢just : {A : Set} → {a : A} → nothing ≢ just a
nothing≢just {_}{_} ()

just-injective : {A : Set} {a₁ a₂ : A} → just a₁ ≡ just a₂ → a₁ ≡ a₂
just-injective refl = refl


{-

  Functions

-}

{-
 agda-stdlib has these but I'd prefer to be able to use these definitions without relying on Setoids & records etc...
-}
Injective : {i j : Level} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
Injective {i} {j} {A} {B} f = {x y : A} → (f x) ≡ (f y) → x ≡ y

Surjective : {i j : Level} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
Surjective {i} {j} {A} {B} f = (y : B) → Σ[ x ∈ A ] ((f x) ≡ y)

Bijective : {i j : Level} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
Bijective f = Injective f × Surjective f





-- More..








Sym→Prop→Trans :
  {A : Set} → (R : A → A → Set) →
  ({a b : A} → R a b → R b a) →
  ({a b c : A} → R a b → R a c → R b c) →
  ({a b c : A} → R a b → R b c → R a c)
Sym→Prop→Trans R sym prop Rab Rbc = prop (sym Rab) Rbc

Sym→Trans→Prop :
  {A : Set} → (R : A → A → Set) →
  ({a b : A} → R a b → R b a) →
  ({a b c : A} → R a b → R b c → R a c) →
  ({a b c : A} → R a b → R a c → R b c)
Sym→Trans→Prop R sym trans Rab Rac = trans (sym Rab) Rac


Functional : {A B : Set} → (A → B → Set) → Set
Functional {A} {B} R = (a : A) → (b₁ b₂ : B) → R a b₁ → R a b₂ → b₁ ≡ b₂

Total : {A B : Set} → (A → B → Set) → Set
Total {A} {B} R = (a : A) → Σ[ b ∈ B ] (R a b)

agda-functional : {A B : Set} → (f : A → B) → Functional (_≡_ ∘ f)
agda-functional f a b₁ b₂ fa≡b₁ fa≡b₂ = ≡-trans (≡-sym fa≡b₁) fa≡b₂

agda-total : {A B : Set} → (f : A → B) → Total (_≡_ ∘ f)
agda-total f a = (f a) , refl

TotalFunctional→Function :
  {A B : Set} →
  (R : A → B → Set) →
  Total R →
  Functional R →
  Σ[ f ∈ (A → B) ] (
    (a : A) → (b : B) → 
    (R a b) ↔ ((f a) ≡ b)
  )
TotalFunctional→Function {A} {B} R R-total R-functional = f , proof
  where
    f = λ a → proj₁ (R-total a)
    proof : (a : A) → (b : B) → (R a b) ↔ ((f a) ≡ b)
    proof a b = Rab→fa≡b , fa≡b→Rab
      where
        Rab→fa≡b : (R a b) → ((f a) ≡ b)
        Rab→fa≡b Rab = R-functional a (f a) b (proj₂ (R-total a)) Rab
            
        fa≡b→Rab : ((f a) ≡ b) → (R a b)
        fa≡b→Rab fa≡b = resp (λ y → R a y) fa≡b (proj₂ (R-total a))

Function→TotalFunctional :
  {A B : Set} →
  (R : A → B → Set) →
  (f : A → B) →
  ((a : A) → (b : B) → (R a b) ↔ ((f a ≡ b))) →
  Total R × Functional R
Function→TotalFunctional {A} {B} R f hyp = R-total , R-functional
  where
    R-total : Total R
    R-total a = (f a) , ((proj₂ (hyp a (f a))) refl)
    
    R-functional : Functional R
    R-functional a b₁ b₂ Rab₁ Rab₂ = ≡-trans b₁≡fa fa≡b₂
      where
        b₁≡fa = ≡-sym ((proj₁ (hyp a b₁)) Rab₁)
        fa≡b₂ = (proj₁ (hyp a b₂)) Rab₂




domain : {A B : Set} → (A → B → Set) → A → Set
domain {A} {B} R x = (Σ[ y ∈ B ] (R x y))

Defined : {A B : Set} → (A → B → Set) → A → Set
Defined {A} {B} R x = domain R x


rel-map : {A B : Set} → {k : ℕ} → (A → B → Set) → Vec A k → Vec B k → Set
rel-map R [] [] = ⊤
rel-map R (a ∷ as) (b ∷ bs) = (R a b) × (rel-map R as bs)

rel-fold : {A B C : Set} → {k : ℕ} → (A → B → C → Set) → Vec A k → B → Vec C k → Set
rel-fold R [] b [] = ⊤
rel-fold R (a ∷ as) b (c ∷ cs) = (R a b c) × (rel-fold R as b cs)




func-rep : {A : Set} → (A → A) → ℕ → A → A
func-rep f 0 = id
func-rep f (suc n) a = f (func-rep f n a)



func-rep-inner : {A : Set} (f : A → A) (n : ℕ) → A → A
func-rep-inner f 0 a = a
func-rep-inner f (suc n) a = (func-rep-inner f n) (f a)

func-rep-lemma1 : {A : Set} (f : A → A) (n : ℕ) (a : A) → f (func-rep f n a) ≡ func-rep f n (f a)
func-rep-lemma1 {A} f 0 a = refl
func-rep-lemma1 {A} f (suc n) a = cong f (func-rep-lemma1 f n a)


func-rep-lemma : {A : Set} (f : A → A) (n : ℕ) (a : A) → func-rep f n a ≡ func-rep-inner f n a
func-rep-lemma f 0 a = refl
func-rep-lemma f (suc n) a = --proof
  func-rep f (suc n) a         ≡⟨ func-rep-lemma1 f n a ⟩ 
  func-rep f n (f a)           ≡⟨ func-rep-lemma f n (f a) ⟩
  func-rep-inner f n (f a)     ≡⟨ refl ⟩
  func-rep-inner f (suc n) a   ∎
  where
    open ≡-Reasoning
