module Util.List.Properties where

open import Basic
open import Util.Arithmetic
open import Util.Bool
open import Util.BoolProp
open import Util.List



list-in : {A : Set} → (x : A) → (xs : List A) → Set
list-in x xs = Σ[ j ∈ ℕ ] (xs [ j ]? ≡ just x)


{-
 Predicates
-}
list-unique : {A : Set} → (l : List A) → Set
list-unique {A} l = (i₁ i₂ : ℕ) → i₁ < length l → i₂ < length l → l [ i₁ ]? ≡ l [ i₂ ]? → i₁ ≡ i₂










{-
  Proofs
-}
List-ext : {i : Level} {A : Set i} {x y : A} {xs ys : List A} → x ≡ y → xs ≡ ys → _≡_ {i} {List A} (x ∷ xs) (y ∷ ys)
List-ext refl refl = refl

List-LEM : {i : Level} {A : Set i} → (l : List A) → (l ≡ []) ⊎ (Σ[ x ∈ A ] (Σ[ xs ∈ List A ] (l ≡ (x ∷ xs))))
List-LEM [] = inj₁ refl
List-LEM (x ∷ xs) = inj₂ (x , (xs , refl))


index-map-lemma : {A B : Set} → (l : List A) → (n : ℕ) → n < length l → (f : A → B) → n < length (map f l)
index-map-lemma [] n ()
index-map-lemma (x ∷ xs) 0 (s≤s z≤n) f = (s≤s z≤n)
index-map-lemma (x ∷ xs) (suc n) (s≤s n<|xs|) f = s≤s (index-map-lemma xs n n<|xs| f)

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
    open ≡-Reasoning
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
    open ≡-Reasoning
    |l₁|+0<|l₁++l₂| = index-++-lemma₂ l₁ l₂ 0 0<|l₂|
    |xs|+0<|xs++l₂| = index-++-lemma₂ xs l₂ 0 0<|l₂|

lookup<-++-lemma₂ l₁@(x ∷ xs) l₂@(y ∷ ys) (suc n) 1+n<|l₂|@(s≤s n<|ys|) = -- l₂[1+n]≡l₁++l₂[|l₁|+1+n]
  lookup< l₂ (1 + n) 1+n<|l₂|
  
    ≡⟨ lookup<-++-lemma₂ xs l₂ (1 + n) 1+n<|l₂| ⟩
    
  lookup< (l₁ ++ l₂) (1 + ((length xs) + (1 + n))) (s≤s |xs|+1+n<|xs++l₂|)

    ≡⟨ lookup<-index-irrelevance (l₁ ++ l₂) (1 + ((length xs) + (1 + n))) ((length l₁) + (1 + n)) (+-assoc 1 (length xs) (1 + n)) (s≤s |xs|+1+n<|xs++l₂|) |l₁|+1+n<|l₁++l₂| ⟩

  lookup< (l₁ ++ l₂) ((length l₁) + (1 + n)) |l₁|+1+n<|l₁++l₂|      ∎
  where
    open ≡-Reasoning
    |xs|+1+n<|xs++l₂| = index-++-lemma₂ xs l₂ (1 + n) 1+n<|l₂|
    |l₁|+1+n<|l₁++l₂| = index-++-lemma₂ l₁ l₂ (1 + n) 1+n<|l₂|

++-subsetₗ : {A : Set} → (l₁ l₂ : List A) → list-subset l₁ (l₁ ++ l₂)
++-subsetₗ [] _ ()
++-subsetₗ l₁@(x ∷ xs) l₂ zero = zero , refl
++-subsetₗ l₁@(x ∷ xs) l₂ (suc i₁) = i₂ , proof
  where
    ind : Σ[ i₂ ∈ Fin (length (xs ++ l₂)) ] (lookup xs i₁ ≡ lookup (xs ++ l₂) i₂)
    ind = ++-subsetₗ xs l₂ i₁
    
    i₂ = suc (proj₁ ind)
    proof = proj₂ ind

{-
++-subsetᵣ : {A : Set} → (l₁ l₂ : List A) → list-subset l₂ (l₁ ++ l₂)
++-subsetᵣ []          _  i = i , refl
++-subsetᵣ l₁@(x ∷ xs) l₂ zero = raise (length l₁) zero 
-}


++-subset<ₗ : {A : Set} → (l₁ l₂ : List A) → list-subset< l₁ (l₁ ++ l₂)
++-subset<ₗ {A} [] _ _ ()
++-subset<ₗ {A} l₁@(x ∷ xs) l₂ 0 0<|l₁| = 0 , (index-++-lemma₁ l₁ l₂ 0 0<|l₁| , refl)
++-subset<ₗ {A} l₁@(x ∷ xs) l₂ (suc i) 1+i<|l₁|@(s≤s i<|xs|) = 1 + i' , (s≤s i'<|xs++l₂| , proof)
  where
    ind : Σ[ i' ∈ ℕ ] (Σ[ i'<|xs++l₂| ∈ i' < length (xs ++ l₂) ] (lookup< xs i i<|xs| ≡ lookup< (xs ++ l₂) i' i'<|xs++l₂|))
    ind = ++-subset<ₗ xs l₂ i i<|xs|

    i' = proj₁ ind
    i'<|xs++l₂| = proj₁ (proj₂ ind)

    proof = proj₂ (proj₂ ind)


pop-++-lemma : {A : Set} → (l₁ l₂ : List A) → (func-rep pop (length l₁)) (l₁ ++ l₂) ≡ l₂
pop-++-lemma [] l = refl
pop-++-lemma l₁@(x ∷ xs) l₂ =
  (func-rep pop (length l₁)) (l₁ ++ l₂)           ≡⟨ func-rep-lemma pop (length l₁) (l₁ ++ l₂) ⟩ 
  (func-rep-inner pop (length l₁)) (l₁ ++ l₂)     ≡⟨ refl ⟩
  (func-rep-inner pop (length xs)) (xs ++ l₂)     ≡⟨ ≡-sym (func-rep-lemma pop (length xs) (xs ++ l₂)) ⟩
  (func-rep pop (length xs)) (xs ++ l₂)           ≡⟨ pop-++-lemma xs l₂ ⟩ 
  l₂                                              ∎
  where
    open ≡-Reasoning

match-cons-lemma : {A : Set} (P : A → Bool) (x : A) (xs : List A) → match P (x ∷ xs) ≡ false → match P xs ≡ false
match-cons-lemma P x xs hyp = proj₂ (not-or-lemma (P x) (match P xs) hyp)

match-++-lemma₂ : {A : Set} → (P : A → Bool) → (l₁ l₂ : List A) → match P l₁ ≡ false → match P (l₁ ++ l₂) ≡ true → match P l₂ ≡ true
match-++-lemma₂ P [] l₂ _ hyp = hyp
match-++-lemma₂ P (x ∷ xs) l₂ hyp₁ hyp₂ = proof
  where
    lemma0 : P x ≡ false
    lemma0 = proj₁ (not-or-lemma (P x) (match P xs) hyp₁)
    
    lemma1 : match P xs ≡ false
    lemma1 = match-cons-lemma P x xs hyp₁

    lemma2 : match P (xs ++ l₂) ≡ true
    lemma2 = process-of-eliminationₗ hyp₂ lemma0

    proof = match-++-lemma₂ P xs l₂ lemma1 lemma2


length-range : (n : ℕ) → length (range n) ≡ n
length-range 0 = refl
length-range (suc n) = cong suc (length-range n)

range-index-lemma : {n x : ℕ} → x < n → x < length (range n)
range-index-lemma {n} {x} x<n = begin-strict
  x                  <⟨ x<n ⟩
  n                  ≡⟨ ≡-sym (length-range n) ⟩
  length (range n)   ∎
  where
    open ≤-Reasoning

range-lookup : {n x : ℕ} → (x<|n| : x < length (range n)) → lookup< (range n) x x<|n| ≡ n - (1 + x)
range-lookup {0} {_} ()
range-lookup {suc n} {0} x<1+n = refl
range-lookup {suc n} {suc x} (s≤s x<|n|) = range-lookup {n} {x} x<|n|

range-lookup? : {n x : ℕ} → (x<|n| : x < length (range n)) → (range n) [ x ]? ≡ just (n - (1 + x))
range-lookup? {0} {_} ()
range-lookup? {suc n} {0} x<1+n = refl
range-lookup? {suc n} {suc x} (s≤s x<|n|) = range-lookup? {n} {x} x<|n|



range-lookup?-end₁ : (n : ℕ) → (range (1 + n)) [ n ]? ≡ just 0
range-lookup?-end₁ 0       = refl
range-lookup?-end₁ (suc n) = range-lookup?-end₁ n


range-lookup?-end : {n x : ℕ} → (x<n : x < n) → (range n) [ (n - (1 + x)) ]? ≡ just x
range-lookup?-end {0}     {_}     ()
range-lookup?-end {suc n} {0}     _         = range-lookup?-end₁ (suc n)
range-lookup?-end {suc n} {suc x} (s≤s x<n) = cases (ℕ-LEM (n - (1 + x)))
  where
    cases : (n - (1 + x) ≡ 0) ⊎ (Σ[ y ∈ ℕ ] (n - (1 + x) ≡ 1 + y)) → (range (1 + n)) [ ((1 + n) - (2 + x)) ]? ≡ just (1 + x)
    cases (inj₁ n-[1+x]≡0) = 
      (range (1 + n)) [ (n - (1 + x)) ]?    ≡⟨ cong (λ z → (range (1 + n)) [ z ]?) n-[1+x]≡0 ⟩
      just n                                ≡⟨ cong just (sub≡-lemma x<n n-[1+x]≡0) ⟩
      just (1 + x)                          ∎
      where
        open ≡-Reasoning
    cases (inj₂ (y , n-[1+x]≡1+y)) =
      (range (1 + n)) [ (n - (1 + x)) ]?  ≡⟨ cong (λ z → (range (1 + n)) [ z ]?) n-[1+x]≡1+y ⟩
      (range (1 + n)) [ (1 + y) ]?        ≡⟨ refl ⟩
      (range n) [ y ]?                    ≡⟨ cong (λ z → (range n) [ z ]?) (≡-sym sublemma3) ⟩
      (range n) [ n - (2 + x) ]?          ≡⟨ range-lookup?-end {n} {suc x} 1+x<n ⟩
      just (1 + x)                        ∎
      where
        open ≡-Reasoning

        sublemma3 : n - (2 + x) ≡ y
        sublemma3 = sub≡-lemma2 {n} {1 + x} {y} n-[1+x]≡1+y

        1+x<n : 1 + x < n
        1+x<n = sub-suc-lemma2 n-[1+x]≡1+y


find-++-lemma : {A : Set} (P : A → Bool) → (l₁ l₂ : List A) → find P l₁ ≡ nothing → find P (l₁ ++ l₂) ≡ find P l₂
find-++-lemma P []          l₂ _    = refl
find-++-lemma P l₁@(x ∷ xs) l₂ hyp  =  proof
  where
    lemma1 : find P (l₁ ++ l₂) ≡ (if (P x) then (just x) else (find P (xs ++ l₂)))
    lemma1 = refl

    lemma2 : find P l₁ ≡ (if (P x) then (just x) else (find P xs))
    lemma2 = refl

    lemma3 : (find P l₁ ≡ just x) ⊎ (find P l₁ ≡ find P xs)
    lemma3 = if-lemma (P x) (just x) (find P xs)

    lemma4 : find P l₁ ≢ just x
    lemma4 hyp2 = subproof
      where
        nothing≡just : nothing ≡ just x
        nothing≡just = ≡-trans (≡-sym hyp) hyp2
        
        subproof = nothing≢just nothing≡just

    lemma5 : find P l₁ ≡ find P xs
    lemma5 = process-of-elimination lemma3 lemma4

    lemma6 : find P xs ≡ nothing
    lemma6 = ≡-trans (≡-sym lemma5) hyp

    lemma7 : find P (xs ++ l₂) ≡ find P l₂
    lemma7 = find-++-lemma P xs l₂ lemma6

    lemma8 : P x ≢ true
    lemma8 Px≡true = lemma4 (cong (λ w → if w then (just x) else (find P xs)) Px≡true)

    lemma9 : P x ≡ false
    lemma9 = ¬≡→≡¬ lemma8

    lemma10 : find P (l₁ ++ l₂) ≡ find P (xs ++ l₂)
    lemma10 = cong (λ w → if w then (just x) else (find P (xs ++ l₂))) lemma9

    proof = ≡-trans lemma10 lemma7


find-cons-lemma : {A : Set} (P : A → Bool) → (x : A) → (xs : List A) → find P (x ∷ xs) ≡ nothing → P x ≡ false
find-cons-lemma P x xs hyp = proof
  where
    lemma1 : find P (x ∷ xs) ≡ (if (P x) then (just x) else (find P xs))
    lemma1 = refl

    lemma2 : P x ≢ true
    lemma2 Px≡true = subproof
      where
        sublemma1 : find P (x ∷ xs) ≡ just x
        sublemma1 = cong (λ w → if w then (just x) else (find P xs)) Px≡true

        subproof = nothing≢just (≡-trans (≡-sym hyp) sublemma1)

    proof = ¬≡→≡¬ lemma2


find-match-lemma : {A : Set} (P : A → Bool) → (l : List A) → find P l ≡ nothing → match P l ≡ false
find-match-lemma _ []       _   = refl
find-match-lemma P l@(x ∷ xs) hyp = proof
  where
    lemma2 : P x ≡ false
    lemma2 = find-cons-lemma P x xs hyp

    lemma3 : find P l ≡ find P xs
    lemma3 = cong (λ w → if w then (just x) else (find P xs)) lemma2

    lemma4 : find P xs ≡ nothing
    lemma4 = ≡-trans (≡-sym lemma3) hyp

    lemma5 : match P xs ≡ false
    lemma5 = find-match-lemma P xs lemma4

    proof : match P l ≡ false
    proof = ≡-trans (cong (λ w → w or (match P xs)) lemma2) (cong (λ w → false or w) lemma5)





get-map-lemma : {A B : Set} (f : A → B) (l : List A) (i : ℕ) → (map f l) [ i ]? ≡ Maybe-map f (l [ i ]?)
get-map-lemma f [] _ = refl
get-map-lemma f (x ∷ xs) 0 = refl
get-map-lemma f l@(x ∷ xs) (suc i) = get-map-lemma f xs i

find-preserve : {A B : Set} (P₁ : A → Bool) (P₂ : B → Bool) (f : A → B) → ((a : A) → P₁ a ≡ P₂ (f a)) → (l : List A) → Maybe-map f (find P₁ l) ≡ find P₂ (map f l)
find-preserve         _  _  _  _   []       = refl
find-preserve {A} {B} P₁ P₂ f  hyp l@(x ∷ xs) = proof
  where
    ind : Maybe-map f (find P₁ xs) ≡ find P₂ (map f xs)
    ind = find-preserve P₁ P₂ f hyp xs
    
    lemma1 : (find P₁ l) ≡ (if (P₁ x) then (just x) else (find P₁ xs))
    lemma1 = refl

    lemma2 : (find P₂ (map f l)) ≡ (if (P₂ (f x)) then (just (f x)) else (find P₂ (map f xs)))
    lemma2 = refl

    case-false : P₁ x ≡ false → Maybe-map f (find P₁ l) ≡ find P₂ (map f l)
    case-false P₁x≡false = ≡-trans sublemma1 sublemma2
      where
        sublemma1 : Maybe-map f (find P₁ l) ≡ find P₂ (map f xs)
        sublemma1 = (≡-trans (cong (Maybe-map f) (cong (λ b → if b then (just x) else (find P₁ xs)) P₁x≡false)) ind)

        P₂fx≡false : P₂ (f x) ≡ false
        P₂fx≡false = ≡-trans (≡-sym (hyp x)) P₁x≡false
        
        sublemma2 : (find P₂ (map f xs)) ≡ (find P₂ (map f l))
        sublemma2 = ≡-sym (cong (λ b → if b then (just (f x)) else (find P₂ (map f xs))) P₂fx≡false)

    case-true : P₁ x ≡ true → Maybe-map f (find P₁ l) ≡ (find P₂ (map f l))
    case-true P₁x≡true = ≡-trans sublemma1 sublemma2
      where
        sublemma1 : Maybe-map f (find P₁ l) ≡ (just (f x))
        sublemma1 = cong (Maybe-map f) (cong (λ b → if b then (just x) else (find P₁ xs)) P₁x≡true)

        P₂fx≡true : P₂ (f x) ≡ true
        P₂fx≡true = ≡-trans (≡-sym (hyp x)) P₁x≡true

        sublemma2 : (just (f x)) ≡ (find P₂ (map f l))
        sublemma2 = ≡-sym (cong (λ b → if b then (just (f x)) else (find P₂ (map f xs))) P₂fx≡true)
    
    proof = ⊎-elim case-true case-false (Bool-LEM (P₁ x))

lookup<-lemma : {A : Set} (l₁ l₂ : List A) (x : ℕ) → (x < length l₁) → (l₁ ++ l₂) [ x ]? ≡ l₁ [ x ]?
lookup<-lemma []          _  _    ()
lookup<-lemma (x ∷ xs)    _  0    _             = refl
lookup<-lemma (x ∷ xs) l₂ (suc n) (s≤s n<|xs|)  = lookup<-lemma xs l₂ n n<|xs|

lookup-map-lemma : {A B : Set} (f : A → B) (l : List A) (n : ℕ) → Maybe-map f (l [ n ]?) ≡ (map f l) [ n ]?
lookup-map-lemma f []       _       = refl
lookup-map-lemma f (x ∷ xs) 0       = refl
lookup-map-lemma f l@(x ∷ xs) (suc n) = lookup-map-lemma f xs n

lookup+-lemma : {A : Set} (l₁ l₂ : List A) (n : ℕ) → (l₁ ++ l₂) [ ((length l₁) + n) ]? ≡ l₂ [ n ]?
lookup+-lemma []       l₂ n = refl
lookup+-lemma (x ∷ xs) l₂ n = lookup+-lemma xs l₂ n


filter-index-lemma : {A : Set} (P : A → Bool) (l : List A) (i : ℕ) (a : A) → l [ i ]? ≡ just a → P a ≡ true → Σ[ j ∈ ℕ ] ((filter P l) [ j ]? ≡ just a)
filter-index-lemma _ []       i _ ()
filter-index-lemma P l@(x ∷ xs) 0 a l[0]≡a Pa≡true = 0 , proof
  where
    lemma1 : P x ≡ true
    lemma1 = ≡-trans (cong P (just-injective {- x a -} l[0]≡a)) Pa≡true

    lemma2 : filter P l ≡ (x ∷ (filter P xs))
    lemma2 = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) lemma1

    lemma3 : (filter P l) [ 0 ]? ≡ (just x)
    lemma3 = cong (λ w → w [ 0 ]?) lemma2
    
    proof = ≡-trans lemma3 l[0]≡a
filter-index-lemma P l@(x ∷ xs) (suc i) a l[1+i]≡a Pa≡true = proof
  where
    l[1+i]≡xs[i] : l [ (1 + i) ]? ≡ xs [ i ]?
    l[1+i]≡xs[i] = refl

    xs[i]≡a : xs [ i ]? ≡ just a
    xs[i]≡a = ≡-trans (≡-sym l[1+i]≡xs[i]) l[1+i]≡a

    case-true : P x ≡ true → Σ[ j ∈ ℕ ] ((filter P l) [ j ]? ≡ just a)
    case-true Px≡true = subproof
      where
        sublemma1 : filter P l ≡ (x ∷ (filter P xs))
        sublemma1 = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡true

        sublemma4 : Σ[ j' ∈ ℕ ] ((filter P xs) [ j' ]? ≡ just a)
        sublemma4 = filter-index-lemma P xs i a xs[i]≡a Pa≡true

        j' =  proj₁ sublemma4
        
        sublemma5 : (filter P xs) [ j' ]? ≡ just a
        sublemma5 = proj₂ sublemma4

        sublemma6 : (x ∷ (filter P xs)) [ (1 + j') ]? ≡ (filter P xs) [ j' ]?
        sublemma6 = refl

        sublemma7 : (filter P l) [ (1 + j') ]? ≡ (x ∷ (filter P xs)) [ (1 + j') ]?
        sublemma7 = cong (λ w → w [ (1 + j') ]?) sublemma1
        
        subproof = 1 + j' , ≡-trans sublemma7 (≡-trans sublemma6 sublemma5)

    case-false : P x ≡ false → Σ[ j ∈ ℕ ] ((filter P l) [ j ]? ≡ just a)
    case-false Px≡false = subproof
      where
        sublemma1 : filter P l ≡ filter P xs
        sublemma1 = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡false

        sublemma2 : Σ[ j' ∈ ℕ ] ((filter P xs) [ j' ]? ≡ just a)
        sublemma2 = filter-index-lemma P xs i a xs[i]≡a Pa≡true

        j' = proj₁ sublemma2

        sublemma3 : (filter P xs) [ j' ]? ≡ just a
        sublemma3 = proj₂ sublemma2

        sublemma4 : (filter P l) [ j' ]? ≡ (filter P xs) [ j' ]?
        sublemma4 = cong (λ w → w [ j' ]?) sublemma1

        subproof = j' , ≡-trans sublemma4 sublemma3
    proof = ⊎-elim case-true case-false (Bool-LEM (P x))


lookup-length-lemma : {A : Set} → (l : List A) (a : A) (i : ℕ) → l [ i ]? ≡ just a → i < length l
lookup-length-lemma [] _ _ ()
lookup-length-lemma l@(x ∷ xs) a 0 _ = (s≤s z≤n)
lookup-length-lemma l@(x ∷ xs) a (suc i) l[1+i]≡a = 1+i<|l|
  where
    xs[i]≡a = l[1+i]≡a
    i<|xs| = lookup-length-lemma xs a i xs[i]≡a
    1+i<|l| = s≤s i<|xs|


-- filter preserves uniqueness

uncons-preserves-uniqueness : {A : Set} (x : A) (xs : List A) → list-unique (x ∷ xs) → list-unique xs
uncons-preserves-uniqueness x xs hyp i₁ i₂ i₁<|xs| i₂<|xs| xs[i₁]≡xs[i₂] = i₁≡i₂
  where
    l = x ∷ xs
    l[1+i₁]≡l[1+i₂] : l [ 1 + i₁ ]? ≡ l [ 1 + i₂ ]?
    l[1+i₁]≡l[1+i₂] = xs[i₁]≡xs[i₂]

    1+i₁≡1+i₂ : 1 + i₁ ≡ 1 + i₂
    1+i₁≡1+i₂ = hyp (1 + i₁) (1 + i₂) (s≤s i₁<|xs|) (s≤s i₂<|xs|) l[1+i₁]≡l[1+i₂]
    
    i₁≡i₂ = suc-injective 1+i₁≡1+i₂

[]?<-lemma : {A : Set} → (l : List A) → (i : ℕ) → i < length l → Σ[ x ∈ A ] (l [ i ]? ≡ just x)
[]?<-lemma {A} [] _ ()
[]?<-lemma {A} (x ∷ xs) 0 _ = x , refl
[]?<-lemma {A} (x ∷ xs) (suc i) (s≤s i<|xs|) = []?<-lemma xs i i<|xs|


injective-map-preserves-uniqueness : {A B : Set} (f : A → B) → Injective f → (l : List A) → list-unique l → list-unique (map f l)
injective-map-preserves-uniqueness f f-inj l hyp i₁ i₂ i₁<|l'| i₂<|l'| l'[i₁]≡l'[i₂] = i₁≡i₂
  where
    l' = map f l
    
    i₁<|l| : i₁ < length l
    i₁<|l| = begin-strict
      i₁        <⟨ i₁<|l'| ⟩
      length l' ≡⟨ length-map f l ⟩
      length l  ∎
      where
        open ≤-Reasoning
        
    i₂<|l| : i₂ < length l
    i₂<|l| = begin-strict
      i₂        <⟨ i₂<|l'| ⟩
      length l' ≡⟨ length-map f l ⟩
      length l  ∎
      where
        open ≤-Reasoning

    x₁ = proj₁ ([]?<-lemma l i₁ i₁<|l|)
    l[i₁]≡x₁ = proj₂ ([]?<-lemma l i₁ i₁<|l|)
    
    x₂ = proj₁ ([]?<-lemma l i₂ i₂<|l|)
    l[i₂]≡x₂ = proj₂ ([]?<-lemma l i₂ i₂<|l|)

    l'[i₁]≡fx₁ : l' [ i₁ ]? ≡ just (f x₁)
    l'[i₁]≡fx₁ = ≡-trans (get-map-lemma f l i₁) (cong (Maybe-map f) l[i₁]≡x₁)

    l'[i₂]≡fx₂ : l' [ i₂ ]? ≡ just (f x₂)
    l'[i₂]≡fx₂ = ≡-trans (get-map-lemma f l i₂) (cong (Maybe-map f) l[i₂]≡x₂)

    just-fx₁≡fx₂ : just (f x₁) ≡ just (f x₂)
    just-fx₁≡fx₂ =
      just (f x₁)  ≡⟨ ≡-sym l'[i₁]≡fx₁ ⟩
      l' [ i₁ ]?   ≡⟨ l'[i₁]≡l'[i₂] ⟩
      l' [ i₂ ]?   ≡⟨ l'[i₂]≡fx₂ ⟩
      just (f x₂)  ∎
      where
        open ≡-Reasoning

    fx₁≡fx₂ : f x₁ ≡ f x₂
    fx₁≡fx₂ = just-injective just-fx₁≡fx₂

    x₁≡x₂ : x₁ ≡ x₂
    x₁≡x₂ = f-inj fx₁≡fx₂

    just-x₁≡x₂ : just x₁ ≡ just x₂
    just-x₁≡x₂ = cong just x₁≡x₂

    l[i₁]≡l[i₂] : l [ i₁ ]? ≡ l [ i₂ ]?
    l[i₁]≡l[i₂] = ≡-trans l[i₁]≡x₁ (≡-trans just-x₁≡x₂ (≡-sym l[i₂]≡x₂))

    i₁≡i₂ = hyp i₁ i₂ i₁<|l| i₂<|l| l[i₁]≡l[i₂]



{-
-- This is false because they're not necessarily in the same order

subset-cons : {A : Set} (x y : A) → (xs ys : List A) → list-subset? (x ∷ xs) (y ∷ ys) → list-subset? xs ys
subset-cons x y xs ys [x∷xs]⊆[y∷ys] = xs⊆ys
  where
    xs⊆ys : list-subset? xs ys
    xs⊆ys i z xs[i]≡z = proof
      where
        x∷xs[1+i]≡z : (x ∷ xs) [ 1 + i ]? ≡ just z
        x∷xs[1+i]≡z = xs[i]≡z

        sublemma : Σ[ j ∈ ℕ ] ((y ∷ ys) [ j ]? ≡ just z)
        sublemma = [x∷xs]⊆[y∷ys] (1 + i) z {- x∷xs[1+i]≡z -} xs[i]≡z

        j = proj₁ sublemma

        y∷ys[j]≡z : (y ∷ ys) [ j ]? ≡ just z
        y∷ys[j]≡z = proj₂ ([x∷xs]⊆[y∷ys] (i + 1) z x∷xs[1+i]≡z)
        
        proof
-}
{-
-- This is false because the "subsets" can have enough repetitions to be longer
subset-length : {A : Set} (l₁ l₂ : List A) → list-subset? l₁ l₂ → length l₁ ≤ length l₂
subset-length [] [] _ = z≤n
subset-length [] (x ∷ xs) _ = z≤n
subset-length l@(x ∷ xs) [] l⊆[] = ⊥-elim contradiction
  where
    x∈[] : Σ[ j ∈ ℕ ] ([] [ j ]? ≡ just x)
    x∈[] = l⊆[] 0 x refl

    contradiction = nothing≢just (proj₂ x∈[])
subset-length l₁@(x ∷ xs) l₂@(y ∷ ys) l₁⊆l₂ = |l₁|≤|l₂|
  where
    
    |l₁|≤|l₂|
-}
{-
-- This is false because the subsets can have repetitions even if the superset doesn't
subset-preserves-uniqueness : {A : Set} (l₁ l₂ : List A) → list-subset? l₁ l₂ → list-unique l₂ → list-unique l₁
subset-preserves-uniqueness {A} l₁ l₂ l₁⊆l₂ l₂-unique i₁ i₂ i₁<|l₁| i₂<|l₂| l₁[i₁]≡l₁[i₂] = i₁≡i₂
  where
    
    i₁≡i₂
-}

filter-subset : {A : Set} (P : A → Bool) (l : List A) (i : ℕ) (x : A) → (filter P l) [ i ]? ≡ just x → Σ[ j ∈ ℕ ] (l [ j ]? ≡ just x)
filter-subset _ [] _ _ ()
filter-subset P l@(x ∷ xs) 0 y l'[0]≡y = proof
  where
    l' = filter P l

    sublemma : (filter P l) ≡ (if (P x) then (x ∷ (filter P xs)) else (filter P xs))
    sublemma = refl

    l[0]≡x : l [ 0 ]? ≡ just x
    l[0]≡x = refl

    cases : (P x ≡ true) ⊎ (P x ≡ false) → Σ[ j ∈ ℕ ] (l [ j ]? ≡ just y)
    cases (inj₁ Px≡true) = 0 , 
      (l [ 0 ]?  ≡⟨ l[0]≡x ⟩
      just x    ≡⟨ ≡-sym subsublemma2 ⟩
      l' [ 0 ]? ≡⟨ l'[0]≡y ⟩
      just y    ∎)
      where
        open ≡-Reasoning
        subsublemma : (filter P l) ≡ (x ∷ (filter P xs))
        subsublemma = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡true

        subsublemma2 : (filter P l) [ 0 ]? ≡ just x
        subsublemma2 = cong (λ w → w [ 0 ]?) subsublemma
    cases (inj₂ Px≡false) = 1 + j , xs[j]≡y
      where
        subsublemma : filter P l ≡ filter P xs
        subsublemma = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡false
        
        subsublemma2 : (filter P xs) [ 0 ]? ≡ just y
        subsublemma2 = ≡-trans (cong (λ w → w [ 0 ]?) (≡-sym subsublemma)) l'[0]≡y

        ind = filter-subset P xs 0 y subsublemma2
        j = proj₁ ind
        xs[j]≡y = proj₂ ind
    
    proof = cases (Bool-LEM (P x))
filter-subset P l@(x ∷ xs) (suc i) y l'[1+i]≡y = proof
  where
    l' = filter P l

    cases : (P x ≡ true) ⊎ (P x ≡ false) → Σ[ j ∈ ℕ ] (l [ j ]? ≡ just y)
    cases (inj₁ Px≡true) = proof
      where
        sublemma : (filter P l) ≡ (x ∷ (filter P xs))
        sublemma = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡true

        sublemma2 : (filter P l) [ 1 + i ]? ≡ (filter P xs) [ i ]?
        sublemma2 = cong (λ w → w [ 1 + i ]?) sublemma

        sublemma3 : (filter P xs) [ i ]? ≡ just y
        sublemma3 = ≡-trans (≡-sym sublemma2) l'[1+i]≡y

        sublemma4 : Σ[ j ∈ ℕ ] (xs [ j ]? ≡ just y)
        sublemma4 = filter-subset P xs i y sublemma3

        j = proj₁ sublemma4
        xs[j]≡y = proj₂ sublemma4
        proof = 1 + j , xs[j]≡y
    cases (inj₂ Px≡false) = proof
      where
        sublemma : filter P l ≡ filter P xs
        sublemma = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡false
        
        sublemma2 : (filter P xs) [ 1 + i ]? ≡ just y
        sublemma2 = ≡-trans (cong (λ w → w [ 1 + i ]?) (≡-sym sublemma)) l'[1+i]≡y

        sublemma3 : Σ[ j ∈ ℕ ] (xs [ j ]? ≡ just y)
        sublemma3 = filter-subset P xs (1 + i) y sublemma2

        j = proj₁ sublemma3
        xs[j]≡y = proj₂ sublemma3
        proof = 1 + j , xs[j]≡y
        
    proof = cases (Bool-LEM (P x))

filter-ordered-subset :  {A : Set} (P : A → Bool) (l : List A) → list-ordered-subset? (filter P l) l
filter-ordered-subset _ [] _ _ ()
filter-ordered-subset P l@(x ∷ xs) 0 y l'[0]≡y = proof
  where
    l' = filter P l

    sublemma : (filter P l) ≡ (if (P x) then (x ∷ (filter P xs)) else (filter P xs))
    sublemma = refl

    l[0]≡x : l [ 0 ]? ≡ just x
    l[0]≡x = refl

    cases : (P x ≡ true) ⊎ (P x ≡ false) → Σ[ j ∈ ℕ ] (0 ≤ j × (l [ j ]? ≡ just y))
    cases (inj₁ Px≡true) = 0 , (z≤n , 
      (l [ 0 ]?  ≡⟨ l[0]≡x ⟩
      just x    ≡⟨ ≡-sym subsublemma2 ⟩
      l' [ 0 ]? ≡⟨ l'[0]≡y ⟩
      just y    ∎))
      where
        open ≡-Reasoning
        subsublemma : (filter P l) ≡ (x ∷ (filter P xs))
        subsublemma = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡true

        subsublemma2 : (filter P l) [ 0 ]? ≡ just x
        subsublemma2 = cong (λ w → w [ 0 ]?) subsublemma
    cases (inj₂ Px≡false) = 1 + j , (z≤n , xs[j]≡y)
      where
        subsublemma : filter P l ≡ filter P xs
        subsublemma = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡false
        
        subsublemma2 : (filter P xs) [ 0 ]? ≡ just y
        subsublemma2 = ≡-trans (cong (λ w → w [ 0 ]?) (≡-sym subsublemma)) l'[0]≡y

        ind = filter-subset P xs 0 y subsublemma2
        j = proj₁ ind
        xs[j]≡y = proj₂ ind
    
    proof = cases (Bool-LEM (P x))
filter-ordered-subset P l@(x ∷ xs) (suc i) y l'[1+i]≡y = proof
  where
    l' = filter P l

    cases : (P x ≡ true) ⊎ (P x ≡ false) → Σ[ j ∈ ℕ ] ((1 + i ≤ j) × (l [ j ]? ≡ just y))
    cases (inj₁ Px≡true) = proof
      where
        sublemma : (filter P l) ≡ (x ∷ (filter P xs))
        sublemma = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡true

        sublemma2 : (filter P l) [ 1 + i ]? ≡ (filter P xs) [ i ]?
        sublemma2 = cong (λ w → w [ 1 + i ]?) sublemma

        sublemma3 : (filter P xs) [ i ]? ≡ just y
        sublemma3 = ≡-trans (≡-sym sublemma2) l'[1+i]≡y

        sublemma4 : Σ[ j ∈ ℕ ] ((i ≤ j) × (xs [ j ]? ≡ just y))
        sublemma4 = filter-ordered-subset P xs i y sublemma3

        j = proj₁ sublemma4
        i≤j = proj₁ (proj₂ sublemma4)
        xs[j]≡y = proj₂ (proj₂ sublemma4)
        proof = 1 + j , ((s≤s i≤j) , xs[j]≡y)
    cases (inj₂ Px≡false) = proof
      where
        sublemma : filter P l ≡ filter P xs
        sublemma = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡false
        
        sublemma2 : (filter P xs) [ 1 + i ]? ≡ just y
        sublemma2 = ≡-trans (cong (λ w → w [ 1 + i ]?) (≡-sym sublemma)) l'[1+i]≡y

        sublemma3 : Σ[ j ∈ ℕ ] ((1 + i ≤ j) × (xs [ j ]? ≡ just y))
        sublemma3 = filter-ordered-subset P xs (1 + i) y sublemma2

        j = proj₁ sublemma3
        1+i≤j = proj₁ (proj₂ sublemma3)
        xs[j]≡y = proj₂ (proj₂ sublemma3)
        proof = 1 + j , ((≤-trans 1+i≤j (n≤1+n j)) , xs[j]≡y)
        
    proof = cases (Bool-LEM (P x))


{-
filter-preserves-uniqueness : {A : Set} (P : A → Bool) (l : List A) → list-unique l → list-unique (filter P l)
filter-preserves-uniqueness P [] hyp = hyp
filter-preserves-uniqueness P l@(x ∷ xs) hyp = proof
  where
    xs-unique : list-unique xs
    xs-unique = uncons-preserves-uniqueness x xs hyp

    filter-xs-unique : list-unique (filter P xs)
    filter-xs-unique = filter-preserves-uniqueness P xs xs-unique

    sublemma : filter P l ≡ (if (P x) then (x ∷ (filter P xs)) else (filter P xs))
    sublemma = refl

    case-false : P x ≡ false → list-unique (filter P l)
    case-false Px≡false = subproof
      where
        subsublemma : filter P l ≡ filter P xs
        subsublemma = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡false

        subproof = resp (λ w → list-unique w) (≡-sym subsublemma) filter-xs-unique

    case-true : P x ≡ true → list-unique (filter P l)
    case-true Px≡true = subproof
      where
        subsublemma : filter P l ≡ x ∷ (filter P xs)
        subsublemma = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡true

        subproof {-: list-unique (filter P l)
        subproof i₁ i₂ i₁<|l'| i₂<|l'| l'[i₁]≡l'[i₂] = i₁≡i₂
          where
            i₁≡i₂
        -}
    proof
-}
