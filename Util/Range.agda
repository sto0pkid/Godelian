module Util.Range where

open import Basic
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary.Decidable.Core using (False)
open import Util.Arithmetic
open import Util.List
open import Util.List.Properties

list-product-length : (n m : ℕ) → length (list-product (range n) (range m)) ≡ n * m
list-product-length 0 _ = refl
list-product-length (suc n) m = -- proof
  length (list-product (range (1 + n)) (range m))

    ≡⟨ refl ⟩
    
  length (((map (λ x → n , x)) (range m)) ++ (list-product (range n) (range m)))

    ≡⟨ length-++ ((map (λ x → n , x)) (range m)) ⟩
    
  length  ((map (λ x → n , x)) (range m)) + length (list-product (range n) (range m))

    ≡⟨ cong (λ y → y + length (list-product (range n) (range m))) (≡-trans (length-map (λ x → n , x) (range m)) (length-range m)) ⟩

  m + length (list-product (range n) (range m))

    ≡⟨ cong (λ y → m + y) (list-product-length n m) ⟩
    
  m + (n * m)

    ≡⟨ refl ⟩
    
  (1 + n) * m

    ∎
  where
    open ≡-Reasoning


product-index-lemma : {n m x y : ℕ} → x < n → y < m → y + (x * m) < length (list-product (range n) (range m))
product-index-lemma {n} {m} {x} {y} x<n y<m = begin-strict
  y + (x * m)                                 <⟨ offset-lemma n m x y x<n y<m ⟩
  n * m                                       ≡⟨ ≡-sym (list-product-length n m) ⟩
  length (list-product (range n) (range m))   ∎
  where
    open ≤-Reasoning


product-lookup : {n m x y : ℕ} → (x<n : x < n) → (y<m : y < m) → ((range n) ⊗ (range m)) [ (y + (x * m)) ]? ≡ just (n - (1 + x) , m - (1 + y))
product-lookup {n = 0} ()
product-lookup {n = suc n} {m = 0} _ ()
product-lookup {suc n} {suc m} {0} {0} 0<1+n 0<1+m = refl
product-lookup {suc n} {suc m} {0} {suc y} 0<1+n 1+y<1+m = proof
  where
    lemma : (1 + y) < (length (map (λ x → n , x) (range (1 + m))))
    lemma = begin-strict
      1 + y                                          <⟨ 1+y<1+m ⟩
      1 + m                                          ≡⟨ ≡-sym (length-range (1 + m)) ⟩
      length (range (1 + m))                         ≡⟨ ≡-sym (length-map (λ x → n , x) (range (1 + m))) ⟩
      (length (map (λ x → n , x) (range (1 + m))))  ∎
      where
        open ≤-Reasoning

    lemma2 : (1 + y) < (length (range (1 + m)))
    lemma2 = begin-strict
      1 + y                     <⟨ 1+y<1+m ⟩
      1 + m                     ≡⟨ ≡-sym (length-range (1 + m)) ⟩
      length (range (1 + m))    ∎
      where
        open ≤-Reasoning


    proof : ((range (1 + n)) ⊗ (range (1 + m))) [ ((1 + y) + (0 * m)) ]? ≡ just (n , ((1 + m) - (2 + y)))
    proof =
      ((range (1 + n)) ⊗ (range (1 + m))) [ ((1 + y) + (0 * m)) ]?

        ≡⟨ cong (λ z → ((range (1 + n)) ⊗ (range (1 + m))) [ z ]?) (+-identityʳ (1 + y)) ⟩

      ((range (1 + n)) ⊗ (range (1 + m))) [ (1 + y) ]?

        ≡⟨ lookup<-lemma (map (λ x → n , x) (range (1 + m))) ((range n) ⊗ (range (1 + m))) (1 + y) lemma ⟩

      ((map (λ x → n , x) (range (1 + m))) [ (1 + y) ]?)

        ≡⟨ ≡-sym (lookup-map-lemma (λ x → n , x) (range (1 + m)) (1 + y)) ⟩

      Maybe-map (λ x → n , x) ((range (1 + m)) [ (1 + y) ]?)

        ≡⟨ cong (Maybe-map (λ x → n , x)) (range-lookup? {1 + m} {1 + y} lemma2) ⟩

      just (n , ((1 + m) - (2 + y)))

        ∎
      where
        open ≡-Reasoning
product-lookup {suc n} {suc m} {suc x} {0} 1+x<1+n@(s≤s x<n) 0<1+m = proof
  where
    length-lemma : (1 + m) ≡ length (map (λ x → n , x) (range (1 + m)))
    length-lemma =
      1 + m                                        ≡⟨ ≡-sym (length-range (1 + m)) ⟩
      length (range (1 + m))                       ≡⟨ ≡-sym (length-map (λ x → n , x) (range (1 + m))) ⟩
      length (map (λ x → n , x) (range (1 + m)))  ∎
      where
        open ≡-Reasoning

    proof :
        ((range (1 + n)) ⊗ (range (1 + m))) [ 0 + ((1 + x) * (1 + m)) ]?
      ≡ (just ((1 + n) - (2 + x) , (1 + m) - 1))
    proof =
      ((range (1 + n)) ⊗ (range (1 + m))) [ 0 + ((1 + x) * (1 + m)) ]?

        ≡⟨ cong (λ z → ((map (λ x → n , x) (range (1 + m))) ++ ((range n) ⊗ (range (1 + m)))) [ z + x * (1 + m) ]?) length-lemma ⟩ 

      ((map (λ x → n , x) (range (1 + m))) ++ ((range n) ⊗ (range (1 + m)))) [ (length (map (λ x → n , x) (range (1 + m)))) + x * (1 + m) ]?

        ≡⟨ lookup+-lemma (map (λ x → n , x) (range (1 + m))) ((range n) ⊗ (range (1 + m))) (x * (1 + m)) ⟩
        
      ((range n) ⊗ (range (1 + m))) [ x * (1 + m) ]?

        ≡⟨ product-lookup {n} {1 + m} {x} {0} x<n 0<1+m ⟩

      (just ((1 + n) - (2 + x) , (1 + m) - 1))
      
        ∎
        where
          open ≡-Reasoning
product-lookup {suc n} {suc m} {suc x} {suc y} 1+x<1+n@(s≤s x<n) 1+y<1+m = proof
  where
    length-lemma : (1 + m) ≡ length (map (λ x → n , x) (range (1 + m)))
    length-lemma =
      1 + m                                        ≡⟨ ≡-sym (length-range (1 + m)) ⟩
      length (range (1 + m))                       ≡⟨ ≡-sym (length-map (λ x → n , x) (range (1 + m))) ⟩
      length (map (λ x → n , x) (range (1 + m)))  ∎
      where
        open ≡-Reasoning


    index-lemma :
        (1 + y) + ((1 + x) * (1 + m))
      ≡ (1 + m) + ((1 + y) + (x * (1 + m)))
    index-lemma =
      (1 + y) + ((1 + x) * (1 + m))         ≡⟨ refl ⟩
      (1 + y) + ((1 + m) + (x * (1 + m)))   ≡⟨ ≡-sym (+-assoc (1 + y) (1 + m) (x * (1 + m))) ⟩
      ((1 + y) + (1 + m)) + (x * (1 + m))   ≡⟨ cong (λ z → z + (x * (1 + m))) (+-comm (1 + y) (1 + m)) ⟩
      ((1 + m) + (1 + y)) + (x * (1 + m))   ≡⟨ +-assoc (1 + m) (1 + y) (x * (1 + m)) ⟩
      (1 + m) + ((1 + y) + (x * (1 + m)))   ∎
      where
        open ≡-Reasoning
        
    proof :
        ((range (1 + n)) ⊗ (range (1 + m))) [ (1 + y) + ((1 + x) * (1 + m)) ]?
      ≡ just (n - (1 + x) , (1 + m) - (2 + y))
    proof =
      ((range (1 + n)) ⊗ (range (1 + m))) [ (1 + y) + ((1 + x) * (1 + m)) ]?

        ≡⟨ cong (λ z → ((range (1 + n)) ⊗ (range (1 + m))) [ z ]?) index-lemma ⟩ 

      ((range (1 + n)) ⊗ (range (1 + m))) [ (1 + m) + ((1 + y) + (x * (1 + m))) ]?

        ≡⟨ cong (λ z → ((range (1 + n)) ⊗ (range (1 + m))) [ z + ((1 + y) + (x * (1 + m))) ]?) length-lemma ⟩

      ((range (1 + n)) ⊗ (range (1 + m))) [ (length (map (λ x → n , x) (range (1 + m)))) + ((1 + y) + (x * (1 + m))) ]?

        ≡⟨ lookup+-lemma (map (λ x → n , x) (range (1 + m))) ((range n) ⊗ (range (1 + m))) ((1 + y) + (x * (1 + m)))  ⟩ 

      ((range n) ⊗ (range (1 + m))) [ (1 + y) + (x * (1 + m)) ]?

        ≡⟨ product-lookup {n} {1 + m} {x} {1 + y} x<n 1+y<1+m ⟩

      just (n - (1 + x) , (1 + m) - (2 + y))
      
        ∎
      where
        open ≡-Reasoning


product-lookup2 :  {n m x y : ℕ} → (x<n : x < n) → (y<m : y < m) → ((range n) ⊗ (range m)) [ ((m - (1 + y)) + ((n - (1 + x)) * m)) ]? ≡ just (x , y)
product-lookup2 {n} {m} {x} {y} x<n y<m = proof
  where
    n-[1+x]<n : n - (1 + x) < n
    n-[1+x]<n = sub<-lemma2 x<n

    m-[1+y]<m : m - (1 + y) < m
    m-[1+y]<m = sub<-lemma2 y<m

    lemma1 : ((range n) ⊗ (range m)) [ ((m - (1 + y)) + ((n - (1 + x)) * m)) ]? ≡ just (n - (1 + (n - (1 + x))) , m - (1 + (m - (1 + y))))
    lemma1 = product-lookup {n} {m} {n - (1 + x)} {m - (1 + y)} n-[1+x]<n m-[1+y]<m

    

    lemma2 : (a b : ℕ) → a < b → b - (1 + (b - (1 + a))) ≡ a
    lemma2 a b a<b =
      b - (1 + (b - (1 + a)))  ≡⟨ sub-assoc b 1 (b - (1 + a)) ⟩
      (b - 1) - (b - (1 + a))  ≡⟨ cong (λ w → (b - 1) - w) (sub-assoc b 1 a) ⟩
      (b - 1) - ((b - 1) - a)  ≡⟨ sub-assoc2 (b - 1) (b - 1) a (pred≤-lemma a<b) ≤-refl ⟩
      ((b - 1) - (b - 1)) + a  ≡⟨ cong (λ w → w + a) (x-x≡0 (b - 1)) ⟩
      0 + a                    ≡⟨ refl ⟩
      a                        ∎
      where
        open ≡-Reasoning

    lemma3 : just (n - (1 + (n - (1 + x))) , m - (1 + (m - (1 + y)))) ≡ just (x , y)
    lemma3 =
      just (n - (1 + (n - (1 + x))) , m - (1 + (m - (1 + y))))   ≡⟨ cong (λ w → just (w , (m - (1 + (m - (1 + y)))))) (lemma2 x n x<n) ⟩ 
      just (x , m - (1 + (m - (1 + y))))                         ≡⟨ cong (λ w → just (x , w)) (lemma2 y m y<m) ⟩
      just (x , y)                                               ∎
      where
        open ≡-Reasoning

    proof = ≡-trans lemma1 lemma3

product-complete : {n m x y : ℕ} → (x < n) → (y < m) → Σ[ i ∈ ℕ ] (((range n) ⊗ (range m)) [ i ]? ≡ just (x , y))
product-complete {n} {m} {x} {y} x<n y<m = ((m - (1 + y)) + ((n - (1 + x)) * m)) , product-lookup2 x<n y<m




product-uniqueness3 :
  (n m i : ℕ) →
  (i<n*[1+m] : i < n * (1 + m)) →
  ((range n) ⊗ (range (1 + m))) [ i ]? ≡ just (n - (1 + (i / (1 + m))) , (1 + m) - (1 + (i % (1 + m))))
product-uniqueness3 n m i i<n*m = proof
  where
    sublemma : i ≡ (i % (1 + m)) + (i / (1 + m)) * (1 + m)
    sublemma = m≡m%n+[m/n]*n i m

    i%[1+m]<1+m : i % (1 + m) < (1 + m)
    i%[1+m]<1+m = m%n<n i m


    i/[1+m]<n : i / (1 + m) < n
    i/[1+m]<n = *<-lemma i n (1 + m) i<n*m
   
    sublemma2 : ((range n) ⊗ (range (1 + m))) [ ((i % (1 + m)) + ((i / (1 + m)) * (1 + m))) ]? ≡ just (n - (1 + (i / (1 + m))) , (1 + m) - (1 + (i % (1 + m))))
    sublemma2 = product-lookup i/[1+m]<n i%[1+m]<1+m

    sublemma3 : ((range n) ⊗ (range (1 + m))) [ i ]? ≡ ((range n) ⊗ (range (1 + m))) [ ((i % (1 + m)) + ((i / (1 + m)) * (1 + m))) ]?
    sublemma3 = cong (λ w → ((range n) ⊗ (range (1 + m))) [ w ]?) sublemma

    proof = ≡-trans sublemma3 sublemma2


product-uniqueness : {n m x y : ℕ} → x < n → y < m → (i : ℕ) → ((range n) ⊗ (range m)) [ i ]? ≡ just (x , y) → i ≡ (m - (1 + y)) + ((n - (1 + x)) * m)
product-uniqueness {n} {0}       {x} {y} _   ()
product-uniqueness {n} {(suc m)} {x} {y} x<n y<1+m i hyp = proof
  where
    v  = ((1 + m) - (1 + y)) + ((n - (1 + x)) * (1 + m))

    n⊗1+m = (range n) ⊗ (range (1 + m))

    sublemma-range : n⊗1+m [ i ]? ≡ n⊗1+m [ v ]?
    sublemma-range =
      n⊗1+m [ i ]?   ≡⟨ hyp ⟩
      just (x , y)   ≡⟨ ≡-sym (product-lookup2 x<n y<1+m) ⟩
      n⊗1+m [ v ]?   ∎
      where
        open ≡-Reasoning

    1+m-[1+y]<1+m : (1 + m) - (1 + y) < (1 + m)
    1+m-[1+y]<1+m = sub<-lemma2 y<1+m

    i<n*[1+m] : i < n * (1 + m)
    i<n*[1+m] = begin-strict
      i                 <⟨ lookup-length-lemma n⊗1+m (x , y) i hyp ⟩
      length n⊗1+m      ≡⟨ list-product-length n (1 + m) ⟩
      n * (1 + m)       ∎
      where
        open ≤-Reasoning

    [1+m]-[1+y]<1+m : (1 + m) - (1 + y) < (1 + m)
    [1+m]-[1+y]<1+m = sub<-lemma2 y<1+m

    n-[1+x]<n : n - (1 + x) < n
    n-[1+x]<n = sub<-lemma2 x<n

    v<n*[1+m] : v < n * (1 + m)
    v<n*[1+m] = *<-lemma2 n-[1+x]<n [1+m]-[1+y]<1+m

    %-sublemma : ((1 + m) - (1 + y)) % (1 + m) ≡ ((1 + m) - (1 + y))
    %-sublemma = m≤n⇒m%n≡m (sub-suc-lemma5 ((1 + m) - (1 + y)) m 1+m-[1+y]<1+m)

    v%-sublemma1 : v % (1 + m) ≡ ((1 + m) - (1 + y)) % (1 + m)
    v%-sublemma1 = [m+kn]%n≡m%n ((1 + m) - (1 + y)) (n - (1 + x)) m

    v%-sublemma : v % (1 + m) ≡ ((1 + m) - (1 + y))
    v%-sublemma = ≡-trans v%-sublemma1 %-sublemma

    1+i%[1+m]≤1+m : 1 + (i % (1 + m)) ≤ 1 + m
    1+i%[1+m]≤1+m =  m%n<n i m

    1+v%[1+m]≤1+m : 1 + (v % (1 + m)) ≤ 1 + m
    1+v%[1+m]≤1+m =  m%n<n v m

    1+i/[1+m]≤n : 1 + (i / (1 + m)) ≤ n
    1+i/[1+m]≤n = *<-lemma i n (1 + m) i<n*[1+m]
    
    1+v/[1+m]≤n : 1 + (v / (1 + m)) ≤ n
    1+v/[1+m]≤n = *<-lemma v n (1 + m) v<n*[1+m]

    ¬¬i≡v : ¬ (¬ (i ≡ v))
    ¬¬i≡v ¬i≡v = contradiction
      where
        -- if i ≢ v then
        subsublemma : (i % (1 + m) ≢ v % (1 + m)) ⊎ (i / (1 + m) ≢ v / (1 + m))
        subsublemma = divmod-uniqueness2< i v (1 + m) {-(x≢0→x≠0 m (m<n⇒n≢0 y<1+m))-} tt ¬i≡v

        subsublemma2 : ((i % (1 + m) ≢ v % (1 + m)) ⊎ (i / (1 + m) ≢ v / (1 + m))) → (((range n) ⊗ (range (1 + m))) [ i ]? ≢ ((range n) ⊗ (range (1 + m))) [ v ]?) 
        subsublemma2 (inj₁ i%1+m≢v%1+m) hyp2 = subcontradiction
          where
            subsubsublemma1 : n⊗1+m [ i ]? ≡  just (n - (1 + (i / (1 + m))) , (1 + m) - (1 + (i % (1 + m))))
            subsubsublemma1 = product-uniqueness3 n m i i<n*[1+m]

            subsubsublemma2 : n⊗1+m [ v ]? ≡ just (n - (1 + (v / (1 + m))) , (1 + m) - (1 + (v % (1 + m))))
            subsubsublemma2 = product-uniqueness3 n m v v<n*[1+m]

            subsubsublemma3 :
              just (n - (1 + (i / (1 + m))) , (1 + m) - (1 + (i % (1 + m))))
              ≡ just (n - (1 + (v / (1 + m))) , (1 + m) - (1 + (v % (1 + m))))
            subsubsublemma3 = ≡-trans (≡-sym subsubsublemma1) (≡-trans hyp2 subsubsublemma2)

            subsubsublemma4 :
              (n - (1 + (i / (1 + m))) , (1 + m) - (1 + (i % (1 + m))))
              ≡ (n - (1 + (v / (1 + m))) , (1 + m) - (1 + (v % (1 + m))))
            subsubsublemma4 = just-injective subsubsublemma3

            subsubsublemma5 :
              (1 + m) - (1 + (i % (1 + m)))
              ≡ (1 + m) - (1 + (v % (1 + m)))
            subsubsublemma5 = proj₂ (×-ext₂ subsubsublemma4)

            subsubsublemma6 :
              (1 + (i % (1 + m)))
              ≡ (1 + (v % (1 + m)))
            subsubsublemma6 = sub≤-lemma 1+i%[1+m]≤1+m 1+v%[1+m]≤1+m subsubsublemma5

            subsubsublemma7 : i % (1 + m) ≡ v % (1 + m)
            subsubsublemma7 = suc-injective subsubsublemma6
            subcontradiction =  i%1+m≢v%1+m subsubsublemma7
        subsublemma2 (inj₂ i/1+m≢v/1+m) hyp2 = subcontradiction
          where
            subsubsublemma1 : n⊗1+m [ i ]? ≡  just (n - (1 + (i / (1 + m))) , (1 + m) - (1 + (i % (1 + m))))
            subsubsublemma1 = product-uniqueness3 n m i i<n*[1+m]

            subsubsublemma2 : n⊗1+m [ v ]? ≡ just (n - (1 + (v / (1 + m))) , (1 + m) - (1 + (v % (1 + m))))
            subsubsublemma2 = product-uniqueness3 n m v v<n*[1+m]

            subsubsublemma3 :
              just (n - (1 + (i / (1 + m))) , (1 + m) - (1 + (i % (1 + m))))
              ≡ just (n - (1 + (v / (1 + m))) , (1 + m) - (1 + (v % (1 + m))))
            subsubsublemma3 = ≡-trans (≡-sym subsubsublemma1) (≡-trans hyp2 subsubsublemma2)

            subsubsublemma4 :
              (n - (1 + (i / (1 + m))) , (1 + m) - (1 + (i % (1 + m))))
              ≡ (n - (1 + (v / (1 + m))) , (1 + m) - (1 + (v % (1 + m))))
            subsubsublemma4 = just-injective subsubsublemma3

            subsubsublemma5 :
              n - (1 + (i / (1 + m)))
              ≡ n - (1 + (v / (1 + m)))
            subsubsublemma5 = proj₁ (×-ext₂ subsubsublemma4)

            subsubsublemma6 : 1 + (i / (1 + m)) ≡ 1 + (v / (1 + m))
            subsubsublemma6 =  sub≤-lemma 1+i/[1+m]≤n 1+v/[1+m]≤n subsubsublemma5

            subsubsublemma7 : i / (1 + m) ≡ v / (1 + m)
            subsubsublemma7 = suc-injective subsubsublemma6
 
            subcontradiction = i/1+m≢v/1+m subsubsublemma7
          
        contradiction = (subsublemma2 subsublemma) sublemma-range
    
    

    proof = ℕ-¬¬ i v ¬¬i≡v
