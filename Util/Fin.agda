module Util.Fin where

open import Basic
open import Util.List

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


eq-Fin : {n : ℕ} → Fin n → Fin n → Bool
eq-Fin {n} m₁ m₂ = (toℕ m₁) eq (toℕ m₂)

Fin-lemma : (n : ℕ) → toℕ (fromℕ n) ≡ n
Fin-lemma 0 = refl
Fin-lemma (suc n) = cong suc (Fin-lemma n)

Fin-Map : {n : ℕ} {A : Set} → (f : Fin n → A) → (x : Fin n) → Vec A (suc (toℕ x))
Fin-Map {0} {A} f ()
Fin-Map {suc n} {A} f zero = (f zero) ∷ []
Fin-Map {suc n} {A} f (suc m) = (f (suc m)) ∷ (Fin-Map (f ∘ (raise 1)) m)

List-LEM : {A : Set} → (l : List A) → (l ≡ []) ⊎ (Σ[ x ∈ A ] (Σ[ xs ∈ List A ] (l ≡ (x ∷ xs))))
List-LEM [] = inj₁ refl
List-LEM (x ∷ xs) = inj₂ (x , (xs , refl))

¬Fin0 : ¬ (Fin 0)
¬Fin0 ()


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



Fin-finite : (x : ℕ) → Σ[ f ∈ ((Fin x) → (Fin x)) ] ((n : Fin x) → Σ[ i ∈ Fin x ] ((f i) ≡ n))
Fin-finite x = id , λ n → n , refl


data Fin< : ℕ → Set where
  mkfin : {m : ℕ} (n : ℕ) → .(n < m) → Fin< m

Fin<-Irrelevance : {m n : ℕ} → (hyp₁ hyp₂ : n < m) → mkfin {m} n hyp₁ ≡ mkfin {m} n hyp₂
Fin<-Irrelevance hyp₁ hyp₂ = refl

toℕ-inject-lemma : {m : ℕ} (n : ℕ) → (i : Fin m) → toℕ (inject+ n i) ≡ toℕ i
toℕ-inject-lemma {0}     n     ()
toℕ-inject-lemma {suc m} n zero = refl
toℕ-inject-lemma {suc m} n (suc i) = cong suc (toℕ-inject-lemma n i)


Fin-lt : {n : ℕ} → Fin n → ℕ → Bool
Fin-lt {0} ()
Fin-lt {suc n} f 0 = false
Fin-lt {suc n} zero (suc m) = true
Fin-lt {suc n} (suc f) (suc m) = Fin-lt f m

Finite : (A : Set) → Set
Finite A = Σ[ n ∈ ℕ ] (Σ[ f ∈ (A → Fin n)] (Bijective f))


