module PidgeonholeInfinite where

open import Basic

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
    proof x x>n = subproof
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

        subproof = ≤∧≢⇒< fx≥1+m (≢-sym fx≢1+m)
