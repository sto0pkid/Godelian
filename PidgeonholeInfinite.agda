module PidgeonholeInfinite where

open import Basic renaming (lookup to _[_]) hiding ([_])

{-
func-min : (f : ℕ → ℕ) → Σ[ x ∈ ℕ ] ((x' : ℕ) → (f x') ≥ (f x))
func-min f = proof
  where
    proof
-}

{-
pidgeonhole-infinite : (f : ℕ → ℕ) → Injective f → (m : ℕ) → Σ[ n ∈ ℕ ] ((x : ℕ) → (x > n) → (f x > m))
pidgeonhole-infinite f f-inj 0 = proof
  where
    proof
-}

{-
pidgeonhole-infinite2 : (f : ℕ → ℕ) → Injective f → 
-}

-- essentially stating that any bijective function ℕ → ℕ is asymptotically monotonic
pidgeonhole-infinite : (f : ℕ → ℕ) → Bijective f → (m : ℕ) → Σ[ n ∈ ℕ ] ((x : ℕ) → (x > n) → (f x > m))
{-
  For the 0 case:

  Choose n = f⁻¹ 0 , which can be found by surjectivity
  Any x different from n will have (f x) ≢ 0 , due to injectivity.
  If (f x) ≢ 0 then f x > 0, QED.
-}
pidgeonhole-infinite f (f-inj , f-surj) 0 = n , proof
  where
    n = proj₁ (f-surj 0)
    proof : (x : ℕ) → (x > n) → (f x > 0)
    proof x x>n = subproof
      where
        x≢n : x ≢ n
        x≢n = >⇒≢ x>n

        fx≢fn : (f x) ≢ (f n)
        fx≢fn fx≡fn = contradiction
          where
            x≡n : x ≡ n
            x≡n = f-inj fx≡fn
            contradiction = x≢n x≡n
            
        fn≡0 = proj₂ (f-surj 0)
        fx≢0 : (f x) ≢ 0
        fx≢0 fx≡0 = contradiction
          where
            fx≡fn = ≡-trans fx≡0 (≡-sym fn≡0)
            contradiction = fx≢fn fx≡fn
        subproof = n≢0⇒n>0 fx≢0
{-
  For the (suc m) case:

  By induction, there is some n' such that for all x > n', f x > m
  Choose n = max (f⁻¹ (1+m)) n' ; f⁻¹ (1+m) can be found by surjectivity.
  If x > n then:
    * x > n' and so f x > m, by the inductive hypothesis, and so f x ≥ 1+m
    * x > (f⁻¹ (1+m)) and so f x ≢ 1+m, by injectivity
  Since f x ≥ 1+m and f x ≢ 1+m then f x > 1+m, QED.
-}
pidgeonhole-infinite f (f-inj , f-surj) (suc m) = n , proof
  where
    ind : Σ[ n' ∈ ℕ ] ((x : ℕ) → (x > n') → (f x > m))
    ind = pidgeonhole-infinite f (f-inj , f-surj) m

    n' = proj₁ ind
    f⁻¹[1+m] = proj₁ (f-surj (suc m))

    n = max f⁻¹[1+m] n'

    n≥n' : n ≥ n'
    n≥n' = m⊔n≥n f⁻¹[1+m] n'

    n≥f⁻¹[1+m] : n ≥ f⁻¹[1+m]
    n≥f⁻¹[1+m] = m⊔n≥m f⁻¹[1+m] n'

    f[f⁻¹[1+m]]≡1+m : (f f⁻¹[1+m]) ≡ (suc m)
    f[f⁻¹[1+m]]≡1+m = proj₂ (f-surj (suc m))

    proof : (x : ℕ) → (x > n) → (f x > (suc m))
    proof x x>n = fx>1+m
      where
        x>n' : x > n'
        x>n' = <-transʳ n≥n' x>n

        fx>m : (f x) > m
        fx>m = (proj₂ ind) x x>n'

        x>f⁻¹[1+m] : x > f⁻¹[1+m]
        x>f⁻¹[1+m] = <-transʳ n≥f⁻¹[1+m] x>n

        x≢f⁻¹[1+m] : x ≢ f⁻¹[1+m]
        x≢f⁻¹[1+m] = >⇒≢ x>f⁻¹[1+m]

        fx≢1+m : (f x) ≢ (suc m)
        fx≢1+m fx≡1+m = contradiction
          where
            fx≡f[f⁻¹[1+m]] : (f x) ≡ (f f⁻¹[1+m])
            fx≡f[f⁻¹[1+m]] = ≡-trans fx≡1+m (≡-sym f[f⁻¹[1+m]]≡1+m)
            
            x≡f⁻¹[1+m] : x ≡ f⁻¹[1+m]
            x≡f⁻¹[1+m] = f-inj fx≡f[f⁻¹[1+m]]
            
            contradiction = x≢f⁻¹[1+m] x≡f⁻¹[1+m]

        fx≥1+m : (f x) ≥ (suc m)
        fx≥1+m = fx>m

        fx>1+m = ≤∧≢⇒< fx≥1+m (≢-sym fx≢1+m)




{-
  If for every element x you can construct a List ℕ that contains the indexes of all appearances of x in the sequence,
  then the sequence always grows arbitrarily large.
-}
-- something something homotopy fibers... ?
pidgeonhole-infinite2 :
  (f : ℕ → ℕ) →
  (appearances : ℕ → List ℕ) →
  (appearances-criteria2 : (a x : ℕ) → (f x) ≡ a → Σ[ i ∈ (Fin (length (appearances a))) ] (((appearances a) [ i ]) ≡ x)) →
  (m : ℕ) →
  Σ[ n ∈ ℕ ] ((x : ℕ) → (x > n) → (f x > m))
pidgeonhole-infinite2 f appearances appearances-criteria 0 = n , proof
  where
    l = appearances 0
    n = list-max l
    
    proof : (x : ℕ) → (x > n) → (f x > 0)
    proof x x>n = fx>0
      where
        fx≢0 : (f x) ≢ 0
        fx≢0 fx≡0 = contradiction
          where
            x∈appearances : Σ[ i ∈ (Fin (length l)) ] ((l [ i ]) ≡ x)
            x∈appearances = appearances-criteria 0 x fx≡0

            i = proj₁ x∈appearances

            n≥l[i] : n ≥ (l [ i ])
            n≥l[i] = list-max-is-max l i

            n≥x : n ≥ x
            n≥x = resp (λ y → n ≥ y) (proj₂ x∈appearances) n≥l[i]
            
            contradiction = <⇒≱ x>n n≥x
            
        fx>0 =  n≢0⇒n>0 fx≢0
pidgeonhole-infinite2 f appearances appearances-criteria (suc m) = n , proof
  where
    ind : Σ[ n' ∈ ℕ ] ((x : ℕ) → (x > n') → (f x > m))
    ind = pidgeonhole-infinite2 f appearances appearances-criteria m

    n' = proj₁ ind
    
    l = appearances (suc m)
    n = max (list-max l) n'
  
    proof : (x : ℕ) → (x > n) → (f x > (suc m))
    proof x x>n = fx>m+1
      where
        n≥n' : n ≥ n'
        n≥n' = m⊔n≥n (list-max l) n'

        x>n' : x > n'
        x>n' = <-transʳ n≥n' x>n
        
        fx>m : (f x) > m
        fx>m = (proj₂ ind) x x>n'

        fx≢m+1 : (f x) ≢ (suc m)
        fx≢m+1 fx≡m+1 = contradiction
          where
            x∈l : Σ[ i ∈ (Fin (length l)) ] ((l [ i ]) ≡ x)
            x∈l = appearances-criteria (suc m) x (fx≡m+1)

            i = proj₁ x∈l

            n≥lmax-l : n ≥ (list-max l)
            n≥lmax-l = m⊔n≥m (list-max l) n'

            lmax-l≥l[i] : (list-max l) ≥ (l [ i ])
            lmax-l≥l[i] = list-max-is-max l i

            lmax-l≥x : (list-max l) ≥ x
            lmax-l≥x = resp (λ y → (list-max l) ≥ y) (proj₂ x∈l) lmax-l≥l[i]

            n≥x : n ≥ x
            n≥x = ≤-trans lmax-l≥x n≥lmax-l
            contradiction =  <⇒≱ x>n n≥x

        fx≥m+1 : (f x) ≥ (suc m)
        fx≥m+1 = fx>m
        
        fx>m+1 = ≤∧≢⇒< fx≥m+1 (≢-sym fx≢m+1)


{-
  If for every x you can select an index greater than or equal to the index of any appearance of x in the sequence,
  then the sequence always grows arbitrarily large.
-}
pidgeonhole-infinite3 :
  (f : ℕ → ℕ) →
  (max-appearance : (a : ℕ) → Σ[ i ∈ ℕ ] ((i' : ℕ) → (f i' ≡ a) → i ≥ i')) →
  (m : ℕ) →
  Σ[ n ∈ ℕ ] ((x : ℕ) → (x > n) → ((f x) > m))
pidgeonhole-infinite3 f max-appearance 0 = n , proof
  where
    n = proj₁ (max-appearance 0)
    proof : (x : ℕ) → (x > n) → f x > 0
    proof x x>n = fx>0
      where
        fx≢0 : f x ≢ 0
        fx≢0 fx≡0 = contradiction
          where
            n≥x : n ≥ x
            n≥x = (proj₂ (max-appearance 0)) x fx≡0
            
            contradiction =  <⇒≱ x>n n≥x
        fx>0 = n≢0⇒n>0 fx≢0
pidgeonhole-infinite3 f max-appearance (suc m) = n , proof
  where
    ind : Σ[ n' ∈ ℕ ] ((x : ℕ) → (x > n') → ((f x) > m))
    ind = pidgeonhole-infinite3 f max-appearance m

    n' = proj₁ ind
    i = proj₁ (max-appearance (suc m))
    n = max i n'
    
    proof : (x : ℕ) → (x > n) → f x > (suc m)
    proof x x>n = fx>1+m
      where
        n≥n' = m⊔n≥n i n'
        x>n' = <-transʳ n≥n' x>n
        n≥i = m⊔n≥m i n'
        x>i = <-transʳ n≥i x>n
        fx>m = (proj₂ ind) x x>n'
        fx≥1+m = fx>m
        
        fx≢1+m : f x ≢ (suc m)
        fx≢1+m fx≡1+m = contradiction
          where
            i≥x : i ≥ x
            i≥x = (proj₂ (max-appearance (suc m))) x fx≡1+m
            contradiction = <⇒≱ x>i i≥x
        fx>1+m = ≤∧≢⇒< fx≥1+m (≢-sym fx≢1+m)

pidgeonhole-infinite4 :
  (f : ℕ → ℕ) →
  (epsilon-delta : (m : ℕ) → Σ[ n ∈ ℕ ] ((x : ℕ) → (x > n) → ((f x) > m))) →
  (a : ℕ) → Σ[ i ∈ ℕ ] ((i' : ℕ) → (f i' ≡ a) → i ≥ i')
pidgeonhole-infinite4 f epsilon-delta a = i , proof
  where
    i = proj₁ (epsilon-delta a)
    proof : (i' : ℕ) → (f i' ≡ a) → i ≥ i'
    proof i' fi'≡a = i≥i'
      where
        i≮i' : ¬ (i < i')
        i≮i' i<i' = contradiction
          where
            fi'>a : f i' > a
            fi'>a = (proj₂ (epsilon-delta a)) i' i<i'
            contradiction = >⇒≢ fi'>a fi'≡a
        i≥i' = ≮⇒≥ i≮i'
