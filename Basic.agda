module Basic where

open import Agda.Primitive public
open import Data.Bool public using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; _xor_ ; if_then_else_)
open import Data.Empty public using (⊥ ; ⊥-elim)
open import Data.Fin public using (Fin ; zero ; suc ; toℕ ; fromℕ ; raise)
open import Data.List public using (List ; [] ; _∷_ ; [_] ; length ; _++_ ; map ; foldl ; foldr ; reverse ; any ; all) renaming (sum to list-sum ; product to list-product ; mapMaybe to filter)
open import Data.Maybe public using (Maybe ; nothing ; just ) renaming (map to Maybe-map)
open import Data.Nat public using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_ ; pred ; _<_ ; _≤_ ; _>_ ; _≥_ ; _≮_ ; _≰_ ; _≯_ ; _≱_ ; z≤n ; s≤s) renaming (_≤ᵇ_ to _le_ ; _<ᵇ_ to _lt_ ; _∸_ to _-_ ; _≡ᵇ_ to _eq_)
open import Data.Nat.Properties public using (+-assoc ; +-comm ; +-identityˡ ; +-identityʳ ; +-identity ; 1+n≢0 ; ≤-refl ; ≤-trans ; <-irrefl ; n≤1+n ; m<n⇒m≤1+n)
open import Data.Nat.GeneralisedArithmetic public using (fold)
open import Data.Product public using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ ; Σ-syntax)
open import Data.Sum public using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit public using (⊤) renaming (tt to unit)
open import Data.Vec public using (Vec ; [] ; _∷_)
open import Function.Base public using (id ; _∘_)
open import Relation.Binary.PropositionalEquality as PropEq public renaming (sym to ≡-sym ; trans to ≡-trans) hiding ([_])
-- open import Relation.Binary.EqReasoning
-- open import Relation.Binary.PropositionalEquality.Core using (≡-Reasoning_)
open import Relation.Nullary public using (¬_)


contrapositive : {A B : Set} → (A → B) → (¬ B → ¬ A)
contrapositive f ¬B a = ¬B (f a)

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

_and_ : Bool → Bool → Bool
_and_ = _∧_

_or_ : Bool → Bool → Bool
_or_ = _∨_

true≠false : true ≢ false
true≠false ()

x≮0 : {x : ℕ} → x ≮ 0
x≮0 ()

sx≠x : {x : ℕ} → (1 + x) ≢ x
sx≠x ()

{-
Alternative definitions of the standard ordering relations on ℕ
-}
_>'_ : ℕ → ℕ → Set
x >' y = Σ[ n ∈ ℕ ] (((1 + n) + y) ≡ x)

_≥'_ : ℕ → ℕ → Set
x ≥' y = (x ≡ y) ⊎ (x > y)


_ge_ : ℕ → ℕ → Bool
x ge y = y le x

_gt_ : ℕ → ℕ → Bool
x gt y = y lt x


Bool→Nat : Bool → ℕ
Bool→Nat false = 0
Bool→Nat true = 1

mod2 : ℕ → Bool
mod2 0 = false
mod2 (suc n) = not (mod2 n) 

parity : List Bool → Bool
parity [] = false
parity (false ∷ xs) = parity xs
parity (true ∷ xs) = not (parity xs)

threshold : ℕ → List Bool → Bool
threshold n l = (list-sum (map Bool→Nat l)) ge n


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

Vec-get : {A : Set} {n : ℕ} → Vec A n → Fin n → A
Vec-get {A} {0} [] ()
Vec-get {A} {suc n} (x ∷ xs) zero = x
Vec-get {A} {suc n} (x ∷ xs) (suc m) = Vec-get xs m

get : {A : Set} → List A → ℕ → Maybe A
get l n = (reverse l) [ n ]?

get-default : {A : Set} → A → List A → ℕ → A
get-default a l n = (reverse l) [[ n , a ]]

set : {A : Set} → List A → ℕ → A → List A
set l n x = reverse ((reverse l) [ n ]:= x)


base-n→unary : {n : ℕ} → List (Fin n) → ℕ
base-n→unary {0} [] = 0
base-n→unary {1} [] = 0
base-n→unary {1} (x ∷ xs) = suc (base-n→unary {1} xs)
base-n→unary {(suc (suc n))} [] = 0
base-n→unary {(suc (suc n))} (x ∷ xs) = (x' * (base ^ (length xs))) + (base-n→unary xs)  
  where
    x' = toℕ x
    base = (suc (suc n))


¬Fin0 : ¬ (Fin 0)
¬Fin0 ()

mk-inl : (A B : Set) → A → A ⊎ B
mk-inl A B a = inj₁ a

mk-inr : (A B : Set) → B → A ⊎ B
mk-inr A B b = inj₂ b

data Inductive₁ (P : Set) : Set where
  cons : P → Inductive₁ P

Inductive₁-bool : Set
Inductive₁-bool = Inductive₁ Bool

Inductive₁-true : Inductive₁-bool
Inductive₁-true = cons true

Inductive₁-false : Inductive₁-bool
Inductive₁-false = cons false

range : ℕ → List ℕ
range 0 = []
range (suc n) = n ∷ (range n)


-- you can do similarly for any inductive type
-- can we abstract this pattern?

Bool-LEM : (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
Bool-LEM true = inj₁ refl
Bool-LEM false = inj₂ refl

Maybe-LEM : {A : Set} → (m : Maybe A) → (m ≡ nothing) ⊎ (Σ[ a ∈ A ] (m ≡ (just a)))
Maybe-LEM nothing = inj₁ refl
Maybe-LEM (just a) = inj₂ (a , refl)

ℕ-LEM : (n : ℕ) → (n ≡ 0) ⊎ (Σ[ m ∈ ℕ ] (n ≡ (suc m)))
ℕ-LEM 0 = inj₁ refl
ℕ-LEM (suc m) = inj₂ (m , refl)

List-LEM : {A : Set} → (l : List A) → (l ≡ []) ⊎ (Σ[ x ∈ A ] (Σ[ xs ∈ List A ] (l ≡ (x ∷ xs))))
List-LEM [] = inj₁ refl
List-LEM (x ∷ xs) = inj₂ (x , (xs , refl))

⊎-LEM : {A B : Set} → (option : A ⊎ B) → (Σ[ a ∈ A ] (option ≡ inj₁ a)) ⊎ (Σ[ b ∈ B ] (option ≡ inj₂ b))
⊎-LEM (inj₁ a) = inj₁ (a , refl)
⊎-LEM (inj₂ b) = inj₂ (b , refl)

process-of-elimination : {A B : Set} → A ⊎ B → ¬ A → B
process-of-elimination (inj₁ a) ¬A = ⊥-elim (¬A a)
process-of-elimination (inj₂ b) _ = b

process-of-elimination-r : {A B : Set} → A ⊎ B → ¬ B → A
process-of-elimination-r (inj₁ a) _ = a
process-of-elimination-r (inj₂ b) ¬B = ⊥-elim (¬B b)


Fin-Map : {n : ℕ} {A : Set} → (f : Fin n → A) → (x : Fin n) → Vec A (suc (toℕ x))
Fin-Map {0} {A} f ()
Fin-Map {suc n} {A} f zero = (f zero) ∷ []
Fin-Map {suc n} {A} f (suc m) = (f (suc m)) ∷ (Fin-Map (f ∘ (raise 1)) m)


Nat-Map : {A : Set} → (f : ℕ → A) → (n : ℕ) → Vec A n
Nat-Map {A} f 0 = []
Nat-Map {A} f (suc n) = (f n) ∷ (Nat-Map f n)


Fin-lemma : (n : ℕ) → toℕ (fromℕ n) ≡ n
Fin-lemma 0 = refl
Fin-lemma (suc n) = cong suc (Fin-lemma n)

coerce : {i : Level} → {A B : Set i} → A ≡ B → A → B
coerce refl a = a


Nat-foldr : {A : Set} → (ℕ → A → A) → A → ℕ → A
Nat-foldr f z n = foldr f z (range n)


Nat-Map-list : {A : Set} → (ℕ → A) → ℕ → List A
Nat-Map-list f n = map f (range n)

Nat-filter : {A : Set} → (ℕ → Maybe A) → ℕ → List A
Nat-filter f n = filter f (range n)


Fin-fold : {A :  Set} {n : ℕ} → (Fin n → A → A) → A → Fin n → A
Fin-fold {A} {0} f z ()
Fin-fold {A} {suc n} f z zero = f zero z
Fin-fold {A} {suc n} f z (suc m) = f (suc m) (Fin-fold (f ∘ (raise 1)) z m) 

Fin-map-list : {A : Set} {n : ℕ} → (Fin n → A) → Fin n → List A
Fin-map-list {A} {n} f m = Fin-fold (_∷_ ∘ f) [] m

Fin-filter : {A : Set} {n : ℕ} → (Fin n → Maybe A) → Fin n → List A
Fin-filter {A} {n} f m = Fin-fold (_∷?_ ∘ f) [] m


vec-append : {A : Set} → {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
vec-append {A} {0} {m} [] v = v
vec-append {A} {suc n} {m} (x ∷ xs) v = x ∷ (vec-append xs v)


vec-flatten : {A : Set} → {n m : ℕ} → Vec (Vec A m) n → Vec A (n * m)
vec-flatten {A} {0} {m} [] = []
vec-flatten {A} {suc n} {m} (v ∷ vs) = vec-append v (vec-flatten vs)

Vector-find : {A : Set} {n : ℕ} → (P : A → Bool) → Vec A n → Maybe A
Vector-find {A} {n} P [] = nothing
Vector-find {A} {n} P (x ∷ xs) = if (P x) then (just x) else (Vector-find P xs)


eq-Fin : {n : ℕ} → Fin n → Fin n → Bool
eq-Fin {n} m₁ m₂ = (toℕ m₁) eq (toℕ m₂)


eq-∧ : {A B : Set} (eq-A : A → A → Bool) (eq-B : B → B → Bool) → (A × B) → (A × B) → Bool
eq-∧ _eq-A_ _eq-B_ (a , b) (a' , b') = (a eq-A a') and (b eq-B b')

List-find : {A : Set} (P : A → Bool) → List A → Maybe A
List-find {A} P [] = nothing
List-find {A} P (x ∷ xs) = if (P x) then (just x) else (List-find P xs)

Injective : {A B : Set} → (A → B) → Set
Injective {A} {B} f = {x y : A} → (f x) ≡ (f y) → x ≡ y

Surjective : {A B : Set} → (A → B) → Set
Surjective {A} {B} f = (y : B) → Σ[ x ∈ A ] ((f x) ≡ y)

Bijective : {A B : Set} → (A → B) → Set
Bijective f = Injective f × Surjective f

Finite : (A : Set) → Set
Finite A = Σ[ n ∈ ℕ ] (Σ[ f ∈ (A → Fin n)] (Bijective f))




-- More..

x+1+y=1+x+y : (x y : ℕ) → x + (1 + y) ≡ 1 + (x + y)
x+1+y=1+x+y x y =
  x + (1 + y) ≡⟨ +-comm x (1 + y) ⟩
  (1 + y) + x ≡⟨ ≡-sym (+-assoc 1 y x) ⟩
  1 + (y + x) ≡⟨ cong suc (+-comm y x) ⟩
  1 + (x + y) ∎
  where open PropEq.≡-Reasoning



sx+y>y : (x y : ℕ) → ((1 + x) + y) > y
sx+y>y x 0 = s≤s z≤n
sx+y>y x (suc y) = proof
  where
    lemma1 : ((1 + x) + (1 + y)) ≡ 1 + ((1 + x) + y)
    lemma1 = x+1+y=1+x+y (1 + x) y

    lemma2 : 1 + ((1 + x) + y) > 1 + y
    lemma2 = s≤s (sx+y>y x y)
    
    proof = resp (λ t → t > 1 + y) (≡-sym lemma1) lemma2

sx+y=sz→x+y=z : {x y z : ℕ} → ((1 + x) + y) ≡ (1 + z) → (x + y) ≡ z
sx+y=sz→x+y=z refl = refl



x>sy→x>y : {x y : ℕ} → x > suc y → x > y
x>sy→x>y {0} {y} ()
x>sy→x>y {(suc x)} {y} (s≤s hyp) = s≤s (≤-trans (n≤1+n y) hyp)


vec-tail : {A : Set} {n : ℕ} → Vec A (1 + n) → Vec A n
vec-tail (x ∷ xs) = xs

List→Vec : {A : Set} → (l : List A) → Vec A (length l)
List→Vec [] = []
List→Vec (x ∷ xs) = x ∷ (List→Vec xs)


sx>sy→x>y : {x y : ℕ} → 1 + x > 1 + y → x > y
sx>sy→x>y {x} {y} (s≤s x>y) = x>y

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

min-Nat : (ℕ → Set) → ℕ → Set
min-Nat P n = (P n) × ((m : ℕ) → P m → m ≤ n)
