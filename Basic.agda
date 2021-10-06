module Basic where

open import Agda.Primitive public
open import Data.Bool public using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; _xor_ ; if_then_else_)
open import Data.Empty public using (⊥ ; ⊥-elim)
open import Data.Fin public using (Fin ; zero ; suc ; toℕ ; fromℕ ; fromℕ< ; raise ; cast ; inject+)
open import Data.Fin.Properties public using (toℕ-fromℕ<)
open import Data.List public using (List ; [] ; _∷_ ; [_] ; length ; _++_ ; map ; foldl ; foldr ; reverse ; any ; all ; lookup ; replicate) renaming (sum to list-sum ; product to list-product ; mapMaybe to filter)
open import Data.List.Properties public using (length-++ ; length-map)
open import Data.Maybe public using (Maybe ; nothing ; just ; is-nothing ; is-just) renaming (map to Maybe-map)
open import Data.Nat public using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_ ; pred ; _<_ ; _≤_ ; _>_ ; _≥_ ; _≮_ ; _≰_ ; _≯_ ; _≱_ ; z≤n ; s≤s) renaming (_<ᵇ_ to _lt_ ; _∸_ to _-_ ; _≡ᵇ_ to _eq_ ; _⊔_ to max)
open import Data.Nat.Properties public using (+-assoc ; +-comm ; +-identityˡ ; +-identityʳ ; +-identity ; 1+n≢0 ; ≤-step ; ≤-reflexive ;  ≤-refl ; ≤-trans ; ≤-antisym ; <-irrefl ; <-transʳ ; <-transˡ ; n≤1+n ; m<n⇒m≤1+n ;  m≤m+n ; m≤n+m ; m<n+m ; m<m+n ; >⇒≢ ; <⇒≱ ; ≮⇒≥ ; n≢0⇒n>0 ; <⇒≤ ; ≤∧≢⇒< ; 0<1+n ; ⊔-identityʳ ;  suc-injective ; ≤-isPartialOrder ; module ≤-Reasoning)
open import Data.Nat.GeneralisedArithmetic public using (fold)
open import Data.Product public using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ ; Σ-syntax)
open import Data.String public using (String)
open import Data.Sum public using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit public using (⊤) renaming (tt to unit)
open import Data.Vec public using (Vec ; [] ; _∷_ ; toList ; fromList)
open import Function.Base public using (id ; _∘_)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.PropositionalEquality as PropEq public renaming (sym to ≡-sym ; trans to ≡-trans) hiding ([_])
-- open import Relation.Binary.Reasoning.PartialOrder as POReasoning public
-- open import Relation.Binary.EqReasoning
-- open import Relation.Binary.PropositionalEquality.Core using (≡-Reasoning_)
open import Relation.Nullary public using (¬_)


contrapositive : {A B : Set} → (A → B) → (¬ B → ¬ A)
contrapositive f ¬B a = ¬B (f a)

_↔_ : {i j : Level} → Set i → Set j → Set (i ⊔ j)
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

{-
More alternative definitions of the standard ordering on ℕ
-}
_≥''_ : ℕ → ℕ → Set
x ≥'' y = Σ[ n ∈ ℕ ] ((n + y) ≡ x)

_>''_ : ℕ → ℕ → Set
x >'' y = x ≥'' (1 + y)


_le_ : ℕ → ℕ → Bool
0 le y = true
(suc x) le 0 = false
(suc x) le (suc y) = x le y

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

Fin-raise : {n : ℕ} → Fin n → Fin (suc n)
Fin-raise {0} ()
Fin-raise {suc n} zero = zero
Fin-raise {suc n} (suc x) = suc (Fin-raise x)

Fin-raise' : {n : ℕ} → (m : ℕ) → Fin n → Fin (m + n)
Fin-raise' {0} _ ()
Fin-raise' {suc n} 0 x = x
Fin-raise' {suc n} (suc m) x = Fin-raise (Fin-raise' m x)



Fin-fold : {A :  Set} {n : ℕ} → (Fin n → A → A) → A → Fin n → A
Fin-fold {A} {0} f z ()
Fin-fold {A} {suc n} f z zero = f zero z
Fin-fold {A} {suc n} f z (suc m) = f (suc m) (Fin-fold (f ∘ (Fin-raise' 1)) z m) 

Fin-map-list : {A : Set} {n : ℕ} → (Fin n → A) → Fin n → List A
Fin-map-list {A} {n} f m = Fin-fold (_∷_ ∘ f) [] m

Fin-filter : {A : Set} {n : ℕ} → (Fin n → Maybe A) → Fin n → List A
Fin-filter {A} {n} f m = Fin-fold (_∷?_ ∘ f) [] m

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


eq-Fin : {n : ℕ} → Fin n → Fin n → Bool
eq-Fin {n} m₁ m₂ = (toℕ m₁) eq (toℕ m₂)


eq-∧ : {A B : Set} (eq-A : A → A → Bool) (eq-B : B → B → Bool) → (A × B) → (A × B) → Bool
eq-∧ _eq-A_ _eq-B_ (a , b) (a' , b') = (a eq-A a') and (b eq-B b')

find : {A : Set} (P : A → Bool) → List A → Maybe A
find {A} P [] = nothing
find {A} P (x ∷ xs) = if (P x) then (just x) else (find P xs)

{-
 agda-stdlib has these but I'd prefer to be able to use these definitions without relying on Setoids & records etc...
-}
Injective : {i j : Level} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
Injective {i} {j} {A} {B} f = {x y : A} → (f x) ≡ (f y) → x ≡ y

Surjective : {i j : Level} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
Surjective {i} {j} {A} {B} f = (y : B) → Σ[ x ∈ A ] ((f x) ≡ y)

Bijective : {i j : Level} {A : Set i} {B : Set j} → (A → B) → Set (i ⊔ j)
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
sx+y>y x (suc y) = begin-strict
  1 + y               <⟨ s≤s (sx+y>y x y) ⟩
  1 + ((1 + x) + y)   ≡⟨ ≡-sym (x+1+y=1+x+y (1 + x) y) ⟩
  (1 + x) + (1 + y)   ∎
  where
      open ≤-Reasoning

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
min-Nat P n = (P n) × ((m : ℕ) → P m → n ≤ m)

min-Nat-unique : (P : ℕ → Set) → {x y : ℕ} → min-Nat P x → min-Nat P y → x ≡ y
min-Nat-unique P {x} {y} (Px , hyp-x) (Py , hyp-y) = ≤-antisym x≤y y≤x
  where
    x≤y = hyp-x y Py
    y≤x = hyp-y x Px


demorgan-∨ : {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
demorgan-∨ ¬[A∨B] = (λ a → ¬[A∨B] (inj₁ a)) , (λ b → ¬[A∨B] (inj₂ b))

m<1+n+m : (m n : ℕ) → m < (1 + n) + m
m<1+n+m m n = m<n+m m (s≤s z≤n)

m<m+1+n : (m n : ℕ) → m < m + (1 + n)
m<m+1+n m n = m<m+n m (s≤s z≤n)

Fin-lt : {n : ℕ} → Fin n → ℕ → Bool
Fin-lt {0} ()
Fin-lt {suc n} f 0 = false
Fin-lt {suc n} zero (suc m) = true
Fin-lt {suc n} (suc f) (suc m) = Fin-lt f m


x+y-x=y : (x y : ℕ) → (x + y) - x ≡ y
x+y-x=y 0 y = refl
x+y-x=y (suc x) y = x+y-x=y x y

dite' : {A : Set} (b : Bool) → ((b ≡ true) → A) → ((b ≡ false) → A) → A
dite' true case-true _ = case-true refl
dite' false _ case-false = case-false refl

≡-Irrelevance : {A : Set} {x y : A} → (e₁ e₂ : x ≡ y) → e₁ ≡ e₂
≡-Irrelevance refl refl = refl

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

dite : {A : Bool → Set} → (b : Bool) → ((b ≡ true) → A true) → ((b ≡ false) → A false) → A b
dite true case-true _ = case-true refl
dite false _ case-false = case-false refl

⊎-elim : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
⊎-elim case-A _ (inj₁ a) = case-A a
⊎-elim _ case-B (inj₂ b) = case-B b


le→≤ : {m n : ℕ} → (m le n) ≡ true → m ≤ n
le→≤ {0} {n} hyp = z≤n
le→≤ {suc m} {0} ()
le→≤ {suc m} {suc n} hyp = s≤s (le→≤ hyp)

≤→le : {m n : ℕ} → m ≤ n → (m le n) ≡ true
≤→le {0} {n} z≤n = refl
≤→le {suc m} {0} ()
≤→le {suc m} {suc n} (s≤s m≤n) = ≤→le m≤n

lt→< : {m n : ℕ} → (m lt n) ≡ true → m < n
lt→< {m} {0} ()
lt→< {0} {suc n} hyp = s≤s (z≤n)
lt→< {suc m} {suc n} hyp = s≤s (lt→< hyp)

<→lt : {m n : ℕ} → m < n → (m lt n) ≡ true
<→lt {m} {0} ()
<→lt {0} {suc n} (s≤s z≤n) = refl
<→lt {suc m} {suc n} (s≤s m<n) = <→lt m<n

Fin-pred : {n : ℕ} → Fin (suc (suc n)) → Fin (suc n)
Fin-pred zero = zero
Fin-pred (suc f) = f

Fin-sub : {n : ℕ} → Fin n → (m : ℕ) → m < n → Fin (n - m)
Fin-sub {0} ()
Fin-sub {1} zero 0 (s≤s z≤n) = zero
Fin-sub {1} zero (suc m) (s≤s ())
Fin-sub {suc (suc n)} f 0 hyp = f
Fin-sub {suc (suc n)} zero (suc m) (s≤s m<1+n) = Fin-sub zero m m<1+n
Fin-sub {suc (suc n)} (suc f) (suc m) (s≤s m<1+n) = Fin-sub f m m<1+n

m⊔n≥n : (m n : ℕ) → (max m n) ≥ n
m⊔n≥n m 0 = z≤n
m⊔n≥n 0 (suc n) = ≤-refl
m⊔n≥n (suc m) (suc n) = s≤s (m⊔n≥n m n)

m⊔n≥m : (m n : ℕ) → (max m n) ≥ m
m⊔n≥m 0 n = z≤n
m⊔n≥m (suc m) (suc n) = s≤s (m⊔n≥m m n)
m⊔n≥m (suc m) 0 = ≤-refl

list-max : (l : List ℕ) → ℕ
list-max [] = 0
list-max (x ∷ xs) = max x (list-max xs)

list-max-is-max : (l : List ℕ) → (i : Fin (length l)) → (list-max l) ≥ (lookup l i)
list-max-is-max [] ()
list-max-is-max (x ∷ xs) zero = resp (λ y → (list-max (x ∷ xs)) ≥ y) refl (m⊔n≥m x (list-max xs))
list-max-is-max l@(x ∷ xs) 1+i@(suc i) = begin
  lookup l 1+i   ≡⟨ refl ⟩
  lookup xs i    ≤⟨ list-max-is-max xs i ⟩
  list-max xs    ≤⟨ m⊔n≥n x (list-max xs) ⟩
  list-max l     ∎ 
  where
    open ≤-Reasoning

x+x≡2x : (x : ℕ) → x + x ≡ 2 * x
x+x≡2x x =
  x + x        ≡⟨ ≡-sym (+-identityʳ (x + x)) ⟩
  (x + x) + 0  ≡⟨ +-assoc x x 0 ⟩
  2 * x        ∎
    where open PropEq.≡-Reasoning


Fin-finite : (x : ℕ) → Σ[ f ∈ ((Fin x) → (Fin x)) ] ((n : Fin x) → Σ[ i ∈ Fin x ] ((f i) ≡ n))
Fin-finite x = id , λ n → n , refl

inc-rev : List Bool → List Bool
inc-rev [] = true ∷ []
inc-rev (false ∷ as) = true ∷ as
inc-rev (true ∷ as) = false ∷ (inc-rev as)

ℕ→Binary : ℕ → List Bool
ℕ→Binary 0 = false ∷ []
ℕ→Binary (suc n) = reverse (inc-rev (reverse (ℕ→Binary n)))

lookupℕ : {A : Set} → List A → ℕ → Maybe A
lookupℕ [] _ = nothing
lookupℕ (x ∷ xs) 0 = just x
lookupℕ (x ∷ xs) (suc n) = lookupℕ xs n

lookupℕ-end : {A : Set} → List A → ℕ → Maybe A
lookupℕ-end l n = lookupℕ (reverse l) n



+ₗ-preserves-< : {m n : ℕ} → (x : ℕ) → m < n → (x + m) < (x + n)
+ₗ-preserves-< 0 m<n = m<n
+ₗ-preserves-< (suc x) m<n = s≤s (+ₗ-preserves-< x m<n)

+ᵣ-preserves-< : {m n : ℕ} → (x : ℕ) → m < n → (m + x) < (n + x)
+ᵣ-preserves-< {m} {n} x m<n = begin-strict
  m + x   ≡⟨ +-comm m x ⟩
  x + m   <⟨ +ₗ-preserves-< x m<n ⟩
  x + n   ≡⟨ +-comm x n ⟩
  n + x   ∎
  where
    open ≤-Reasoning

lookup< : {A : Set} → (l : List A) → (n : ℕ) → (n < length l) → A
lookup< [] _ ()
lookup< (x ∷ xs) 0 _ = x
lookup< l@(x ∷ xs) (suc n) (s≤s n<|xs|) = lookup< xs n n<|xs|


index-map-lemma : {A B : Set} → (l : List A) → (n : ℕ) → n < length l → (f : A → B) → n < length (map f l)
index-map-lemma [] n ()
index-map-lemma (x ∷ xs) 0 (s≤s z≤n) f = (s≤s z≤n)
index-map-lemma (x ∷ xs) (suc n) (s≤s n<|xs|) f = s≤s (index-map-lemma xs n n<|xs| f)

ℕ-Poset : Poset lzero lzero lzero
ℕ-Poset = record{ Carrier = ℕ ; _≈_ = _≡_ ; _≤_ = _≤_ ; isPartialOrder = ≤-isPartialOrder }

index-++-lemma₁ : {A : Set} → (l₁ l₂ : List A) → (n : ℕ) → n < length l₁ → n < length (l₁ ++ l₂)
index-++-lemma₁ l₁ l₂ n n<|l₁| = begin-strict
  n                      <⟨ n<|l₁| ⟩
  length l₁              ≤⟨ m≤m+n (length l₁) (length l₂) ⟩
  length l₁ + length l₂  ≡⟨ ≡-sym (length-++ l₁) ⟩
  length (l₁ ++ l₂)      ∎
  where
    open ≤-Reasoning

index-++-lemma₂ : {A : Set} → (l₁ l₂ : List A) → (n : ℕ) → n < length l₂ → (length l₁) + n < length (l₁ ++ l₂)
index-++-lemma₂ l₁ l₂ n n<|l₂| = begin-strict -- |l₁|+n<|l₁++l₂|
  (length l₁) + n            <⟨ +ₗ-preserves-< (length l₁) n<|l₂| ⟩
  (length l₁) + (length l₂)  ≡⟨ ≡-sym (length-++ l₁) ⟩
  length (l₁ ++ l₂)          ∎
  where
    open ≤-Reasoning


lookup<-irrelevance : {A : Set} → (l : List A) → (n : ℕ) → (n<|l|₁ n<|l|₂ : n < length l) → lookup< l n n<|l|₁ ≡ lookup< l n n<|l|₂
lookup<-irrelevance [] 0 ()
lookup<-irrelevance (x ∷ xs) 0 _ _ = refl
lookup<-irrelevance l@(x ∷ xs) (suc n) (s≤s n<|xs|₁) (s≤s n<|xs|₂) = lookup<-irrelevance xs n n<|xs|₁ n<|xs|₂

lookup<-index-irrelevance : {A : Set} → (l : List A) → (n₁ n₂ : ℕ) → n₁ ≡ n₂ → (n₁<|l| : n₁ < length l) → (n₂<|l| : n₂ < length l) → lookup< l n₁ n₁<|l| ≡ lookup< l n₂ n₂<|l|
lookup<-index-irrelevance [] _ _ _ ()
lookup<-index-irrelevance (x ∷ xs) 0 0 refl _ _ = refl
lookup<-index-irrelevance l@(x ∷ xs) (suc n₁) (suc n₂) 1+n₁≡1+n₂ (s≤s n₁<|xs|) (s≤s n₂<|xs|) = lookup<-index-irrelevance xs n₁ n₂ (suc-injective 1+n₁≡1+n₂) n₁<|xs| n₂<|xs|

lookup<-map-lemma : {A B : Set} → (l : List A) → (n : ℕ) → (n<|l| : n < length l) → (f : A → B) → lookup< (map f l) n (index-map-lemma l n n<|l| f) ≡ f (lookup< l n n<|l|)
lookup<-map-lemma [] _ ()
lookup<-map-lemma (x ∷ xs) 0 _ _ = refl
lookup<-map-lemma (x ∷ xs) (suc n) (s≤s n<|xs|) f = lookup<-map-lemma xs n n<|xs| f

lookup<-++-lemma₁ : {A : Set} → (l₁ l₂ : List A) → (n : ℕ) → (n<|l₁| : n < length l₁) → lookup< l₁ n n<|l₁| ≡ lookup< (l₁ ++ l₂) n (index-++-lemma₁ l₁ l₂ n n<|l₁|)
lookup<-++-lemma₁ [] _ _ ()
lookup<-++-lemma₁ (x ∷ xs) _ 0 _ = refl
lookup<-++-lemma₁ l₁@(x ∷ xs) l₂ (suc n) 1+n<|l₁|@(s≤s n<|xs|) =
  lookup< l₁ (1 + n) 1+n<|l₁|                                         ≡⟨ refl ⟩
  lookup< xs n n<|xs|                                                 ≡⟨ lookup<-++-lemma₁ xs l₂ n n<|xs| ⟩
  lookup< (xs ++ l₂) n n<|xs++l₂|                                     ≡⟨ refl ⟩
  lookup< (l₁ ++ l₂) (1 + n) (s≤s n<|xs++l₂|)                         ≡⟨ lookup<-irrelevance (l₁ ++ l₂) (1 + n) (s≤s n<|xs++l₂|) (index-++-lemma₁ l₁ l₂ (1 + n) 1+n<|l₁|) ⟩
  lookup< (l₁ ++ l₂) (1 + n) (index-++-lemma₁ l₁ l₂ (1 + n) 1+n<|l₁|) ∎ 

  where
    open PropEq.≡-Reasoning
    n<|xs++l₂| : n < length (xs ++ l₂)
    n<|xs++l₂| = index-++-lemma₁ xs l₂ n n<|xs|


lookup<-++-lemma₂ : {A : Set} → (l₁ l₂ : List A) → (n : ℕ) → (n<|l₂| : n < length l₂) → lookup< l₂ n n<|l₂| ≡ lookup< (l₁ ++ l₂) ((length l₁) + n) (index-++-lemma₂ l₁ l₂ n n<|l₂|)
lookup<-++-lemma₂ _ [] _ ()
lookup<-++-lemma₂ [] (y ∷ ys) 0 _ = refl
lookup<-++-lemma₂ [] l₂@(y ∷ ys) (suc n) 1+n<|l₂| = refl
lookup<-++-lemma₂ l₁@(x ∷ xs) l₂@(y ∷ ys) 0 0<|l₂| =
  lookup< l₂ 0 0<|l₂|

    ≡⟨ lookup<-++-lemma₂ xs l₂ 0 0<|l₂| ⟩
      
  lookup< (l₁ ++ l₂) (1 + ((length xs) + 0)) (s≤s |xs|+0<|xs++l₂|)

    ≡⟨ lookup<-index-irrelevance (l₁ ++ l₂) (1 + ((length xs) + 0)) ((length l₁) + 0) (+-assoc 1 (length xs) 0) (s≤s |xs|+0<|xs++l₂|) |l₁|+0<|l₁++l₂| ⟩
      
  lookup< (l₁ ++ l₂) ((length l₁) + 0) (index-++-lemma₂ l₁ l₂ 0 0<|l₂|) ∎
  where
    open PropEq.≡-Reasoning
    |l₁|+0<|l₁++l₂| = index-++-lemma₂ l₁ l₂ 0 0<|l₂|
    |xs|+0<|xs++l₂| = index-++-lemma₂ xs l₂ 0 0<|l₂|

lookup<-++-lemma₂ l₁@(x ∷ xs) l₂@(y ∷ ys) (suc n) 1+n<|l₂|@(s≤s n<|ys|) = -- l₂[1+n]≡l₁++l₂[|l₁|+1+n]
  lookup< l₂ (1 + n) 1+n<|l₂|
  
    ≡⟨ lookup<-++-lemma₂ xs l₂ (1 + n) 1+n<|l₂| ⟩
    
  lookup< (l₁ ++ l₂) (1 + ((length xs) + (1 + n))) (s≤s |xs|+1+n<|xs++l₂|)

    ≡⟨ lookup<-index-irrelevance (l₁ ++ l₂) (1 + ((length xs) + (1 + n))) ((length l₁) + (1 + n)) (+-assoc 1 (length xs) (1 + n)) (s≤s |xs|+1+n<|xs++l₂|) |l₁|+1+n<|l₁++l₂| ⟩

  lookup< (l₁ ++ l₂) ((length l₁) + (1 + n)) |l₁|+1+n<|l₁++l₂|      ∎
  where
    open PropEq.≡-Reasoning
    |xs|+1+n<|xs++l₂| = index-++-lemma₂ xs l₂ (1 + n) 1+n<|l₂|
    |l₁|+1+n<|l₁++l₂| = index-++-lemma₂ l₁ l₂ (1 + n) 1+n<|l₂|


𝟚^ : (n : ℕ) → List (Vec Bool n)
𝟚^ 0 = [] ∷ []
𝟚^ (suc n) = (map (_∷_ true) (𝟚^ n)) ++ (map (_∷_ false) (𝟚^ n))

|𝟚^n|≡2^n : (n : ℕ) → length (𝟚^ n) ≡ 2 ^ n
|𝟚^n|≡2^n 0 = refl
|𝟚^n|≡2^n (suc n) = 
  length (𝟚^ (1 + n))
  
      ≡⟨ refl ⟩
      
  length ((map (_∷_ true) (𝟚^ n)) ++ (map (_∷_ false) (𝟚^ n)))
  
      ≡⟨ length-++ (map (_∷_ true) (𝟚^ n)) ⟩
      
  length (map (_∷_ true) (𝟚^ n)) + length (map (_∷_ false) (𝟚^ n))
  
      ≡⟨ cong (λ y → y + length (map (Data.Vec._∷_ false) (𝟚^ n))) (length-map (_∷_ true) (𝟚^ n)) ⟩
      
  length (𝟚^ n) + length ((map (_∷_ false) (𝟚^ n)))
  
      ≡⟨ cong (λ y → length (𝟚^ n) + y) (length-map (_∷_ false) (𝟚^ n)) ⟩
      
  length (𝟚^ n) + length (𝟚^ n)
  
      ≡⟨ x+x≡2x (length (𝟚^ n)) ⟩
      
  2 * (length (𝟚^ n))
  
      ≡⟨ cong (λ y → 2 * y) ind ⟩
      
  2 * (2 ^ n)
  
      ≡⟨ refl ⟩
      
  2 ^ (1 + n)
  
      ∎
    where
      open PropEq.≡-Reasoning

      ind : length (𝟚^ n) ≡ 2 ^ n
      ind = |𝟚^n|≡2^n n


𝟚^n-complete : {n : ℕ} → (v : Vec Bool n) → Σ[ i ∈ ℕ ] (Σ[ i<|l| ∈ i < length (𝟚^ n) ] (lookup< (𝟚^ n) i i<|l|) ≡ v)
𝟚^n-complete {0} [] = 0 , ((s≤s z≤n) , refl)
𝟚^n-complete {suc n} v@(true ∷ xs) = i , (i<|𝟚^1+n| , 𝟚^1+n[i]≡v)
  where
    ind : Σ[ i' ∈ ℕ ] (Σ[ i'<|𝟚^n| ∈ i' < length (𝟚^ n) ] (lookup< (𝟚^ n) i' i'<|𝟚^n|) ≡ xs)
    ind = 𝟚^n-complete xs
    i' = proj₁ ind
    i'<|𝟚^n| = proj₁ (proj₂ ind)
    𝟚^n[i']≡xs = proj₂ (proj₂ ind)

    i'<|map-t-𝟚^n| : i' < length (map (_∷_ true) (𝟚^ n))
    i'<|map-t-𝟚^n| = (index-map-lemma (𝟚^ n) i' i'<|𝟚^n| (_∷_ true))
    
    map-t-𝟚^n[i']≡t∷𝟚^n[i'] : lookup< (map (_∷_ true) (𝟚^ n)) i' i'<|map-t-𝟚^n| ≡ (true ∷ (lookup< (𝟚^ n) i' i'<|𝟚^n|))
    map-t-𝟚^n[i']≡t∷𝟚^n[i'] = lookup<-map-lemma (𝟚^ n) i' i'<|𝟚^n| (_∷_ true)

    t∷𝟚^n[i']≡v : (true ∷ (lookup< (𝟚^ n) i' i'<|𝟚^n|)) ≡ v
    t∷𝟚^n[i']≡v = cong (_∷_ true) 𝟚^n[i']≡xs

    map-t-𝟚^n[i']≡v : lookup< (map (_∷_ true) (𝟚^ n)) i' i'<|map-t-𝟚^n| ≡ v
    map-t-𝟚^n[i']≡v = ≡-trans map-t-𝟚^n[i']≡t∷𝟚^n[i'] t∷𝟚^n[i']≡v

    i'<|𝟚^1+n| : i' < length (𝟚^ (1 + n))
    i'<|𝟚^1+n| = index-++-lemma₁ (map (_∷_ true) (𝟚^ n)) (map (_∷_ false) (𝟚^ n)) i' i'<|map-t-𝟚^n|

    map-t-𝟚^n[i']≡𝟚^1+n[i'] : lookup< (map (_∷_ true) (𝟚^ n)) i' i'<|map-t-𝟚^n| ≡ lookup< (𝟚^ (1 + n)) i' i'<|𝟚^1+n|
    map-t-𝟚^n[i']≡𝟚^1+n[i'] = lookup<-++-lemma₁ (map (_∷_ true) (𝟚^ n)) (map (_∷_ false) (𝟚^ n)) i' i'<|map-t-𝟚^n|
    
    i = i'
    i<|𝟚^1+n| = i'<|𝟚^1+n|
    
    𝟚^1+n[i]≡v = ≡-trans (≡-sym map-t-𝟚^n[i']≡𝟚^1+n[i']) map-t-𝟚^n[i']≡v
    
𝟚^n-complete {suc n} v@(false ∷ xs) = i , (i<|𝟚^1+n| , 𝟚^1+n[i]≡v)
  where
    ind : Σ[ i' ∈ ℕ ] (Σ[ i'<|𝟚^n| ∈ i' < length (𝟚^ n) ] (lookup< (𝟚^ n) i' i'<|𝟚^n|) ≡ xs)
    ind = 𝟚^n-complete xs
    
    i' = proj₁ ind
    i'<|𝟚^n| = proj₁ (proj₂ ind)
    𝟚^n[i']≡xs = proj₂ (proj₂ ind)

    i'<|map-f-𝟚^n| : i' < length (map (_∷_ false) (𝟚^ n))
    i'<|map-f-𝟚^n| = (index-map-lemma (𝟚^ n) i' i'<|𝟚^n| (_∷_ false))
    
    map-f-𝟚^n[i']≡f∷𝟚^n[i'] : lookup< (map (_∷_ false) (𝟚^ n)) i' i'<|map-f-𝟚^n| ≡ (false ∷ (lookup< (𝟚^ n) i' i'<|𝟚^n|))
    map-f-𝟚^n[i']≡f∷𝟚^n[i'] = lookup<-map-lemma (𝟚^ n) i' i'<|𝟚^n| (_∷_ false)

    f∷𝟚^n[i']≡v : (false ∷ (lookup< (𝟚^ n) i' i'<|𝟚^n|)) ≡ v
    f∷𝟚^n[i']≡v = cong (_∷_ false) 𝟚^n[i']≡xs

    map-f-𝟚^n[i']≡v : lookup< (map (_∷_ false) (𝟚^ n)) i' i'<|map-f-𝟚^n| ≡ v
    map-f-𝟚^n[i']≡v = ≡-trans map-f-𝟚^n[i']≡f∷𝟚^n[i'] f∷𝟚^n[i']≡v
    
    i = length (map (_∷_ true) (𝟚^ n)) + i'
    
    i<|𝟚^1+n| : i < length (𝟚^ (1 + n))
    i<|𝟚^1+n| = index-++-lemma₂ (map (_∷_ true) (𝟚^ n)) (map (_∷_ false) (𝟚^ n)) i' i'<|map-f-𝟚^n|

    map-f-𝟚^n[i']≡𝟚^1+n[i] : lookup< (map (_∷_ false) (𝟚^ n)) i' i'<|map-f-𝟚^n| ≡ lookup< (𝟚^ (1 + n)) i i<|𝟚^1+n|
    map-f-𝟚^n[i']≡𝟚^1+n[i] = lookup<-++-lemma₂ (map (_∷_ true) (𝟚^ n)) (map (_∷_ false) (𝟚^ n)) i' i'<|map-f-𝟚^n|

    𝟚^1+n[i]≡v = ≡-trans (≡-sym map-f-𝟚^n[i']≡𝟚^1+n[i]) map-f-𝟚^n[i']≡v


Vec→List : {A : Set} {n : ℕ} → Vec A n → List A
Vec→List [] = []
Vec→List (x ∷ xs) = x ∷ (Vec→List xs)

Vec→List-preserves-length : {A : Set} {n : ℕ} → (v : Vec A n) → length (Vec→List v) ≡ n
Vec→List-preserves-length [] = refl
Vec→List-preserves-length {n = (suc n)} (x ∷ xs) = cong suc (Vec→List-preserves-length xs)

List→Vec-length : {A : Set} {n : ℕ} → (l : List A) → length l ≡ n → Vec A n
List→Vec-length {A} {0} [] _ = []
List→Vec-length {A} {suc n} l@(x ∷ xs) |l|≡1+n = x ∷ (List→Vec-length xs (suc-injective |l|≡1+n))

List→Vec→List : {A : Set} {n : ℕ} → (l : List A) → (|l|≡n : length l ≡ n) → Vec→List (List→Vec-length l |l|≡n) ≡ l
List→Vec→List {A} {0} [] _ = refl
List→Vec→List {A} {suc n} l@(x ∷ xs) |l|≡1+n = cong (_∷_ x) (List→Vec→List xs (suc-injective |l|≡1+n))

list-max-is-max2 : (l : List ℕ) → (i : ℕ) → (i<|l| : i < length l) → list-max l ≥ lookup< l i i<|l|
list-max-is-max2 [] _ ()
list-max-is-max2 l@(x ∷ xs) 0 0<|l| = m⊔n≥m x (list-max xs)
list-max-is-max2 l@(x ∷ xs) (suc n) 1+n<|l|@(s≤s n<|xs|) = begin
  lookup< l (1 + n) 1+n<|l|   ≡⟨ refl ⟩
  lookup< xs n n<|xs|         ≤⟨ list-max-is-max2 xs n n<|xs| ⟩
  list-max xs                 ≤⟨ m⊔n≥n x (list-max xs) ⟩
  list-max l                  ∎
  where
    open ≤-Reasoning


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

func-rep : {A : Set} → (A → A) → ℕ → A → A
func-rep f 0 = id
func-rep f (suc n) a = f (func-rep f n a)

List-ext : {i : Level} {A : Set i} {x y : A} {xs ys : List A} → x ≡ y → xs ≡ ys → _≡_ {i} {List A} (x ∷ xs) (y ∷ ys)
List-ext refl refl = refl


Vec-ext : {i : Level} {A : Set i} {n : ℕ} {x y : A} {xs ys : Vec A n} → x ≡ y → xs ≡ ys → _≡_ {i} {Vec A (1 + n)} (x ∷ xs) (y ∷ ys)
Vec-ext refl refl = refl

Vec-ext2 : {i : Level} {A : Set i} {n : ℕ} (xs : Vec A (1 + n)) → xs ≡ (Data.Vec.head xs) ∷ (Data.Vec.tail xs)
Vec-ext2 (x ∷ xs) = refl

Vec-empty : {i : Level} {A : Set i} → (xs : Vec A 0) → xs ≡ []
Vec-empty [] = refl

Vec1-ext : {i : Level} {A : Set i} → (xs : Vec A 1) → xs ≡ ((Data.Vec.head xs) ∷ [])
Vec1-ext (x ∷ []) = refl

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

flatten : {A : Set} → List (List A) → List A
flatten nested = foldr _++_ [] nested

data Fin< : ℕ → Set where
  mkfin : {m : ℕ} (n : ℕ) → .(n < m) → Fin< m

Fin<-Irrelevance : {m n : ℕ} → (hyp₁ hyp₂ : n < m) → mkfin {m} n hyp₁ ≡ mkfin {m} n hyp₂
Fin<-Irrelevance hyp₁ hyp₂ = refl

toℕ-inject-lemma : {m : ℕ} (n : ℕ) → (i : Fin m) → toℕ (inject+ n i) ≡ toℕ i
toℕ-inject-lemma {0}     n     ()
toℕ-inject-lemma {suc m} n zero = refl
toℕ-inject-lemma {suc m} n (suc i) = cong suc (toℕ-inject-lemma n i)
