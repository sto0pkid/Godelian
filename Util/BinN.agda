module Util.BinN where

open import Basic
open import Data.Vec using (_∷_)
open import Relation.Binary.PropositionalEquality as PropEq
open import Util.Arithmetic
open import Util.List
open import Util.List.Properties

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
