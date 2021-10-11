module MuRecursive.HaltingProblem where

open import Basic
open import Data.Vec using (head)
open import MuRecursive
open import MuRecursive.Properties
open import MuRecursive.Examples.HaltExample
open import MuRecursive.Examples.LoopExample2
open import Util.Vec

{-
  This is to help construct the "diagonalization gadget" K for proving the undecidability of the halting problem
  Intuitively it has the semantics that it will halt on input 0 and loop on any other input
-}
μR-K-helper : μR 1
μR-K-helper = prim-rec μR-halt-example μR-loop-example2

μR-K-helper-halts-on-0 : μR-K-helper [ (0 ∷ []) ]= 0
μR-K-helper-halts-on-0 = μR-halt-example-halts

μR-K-helper-loops-on-1 : ¬ (μR-Halting μR-K-helper (1 ∷ []))
μR-K-helper-loops-on-1 (y , f[1]≡y) = μR-loop-example2-loops (1 ∷ (proj₁ f[1]≡y) ∷ []) (y , (proj₂ (proj₂ f[1]≡y)))


{-
Proof that the halting problem for μ-recursive functions is undecidable (by μ-recursive functions)
-}

μR-halting-undecidable :
  ¬(
    Σ[ e ∈ (μR 1 → ℕ) ] (
      Σ[ H ∈ μR 2 ] (
        (P : μR 1) → 
        (x : Vec ℕ 1) →
          ((H [ ((e P) ∷ x) ]= 0) ⊎ (H [ ((e P) ∷ x) ]= 1))
        × ((H [ ((e P) ∷ x) ]= 1) ↔ (Σ[ y ∈ ℕ ] (P [ x ]= y)))
      )
    )
  )
μR-halting-undecidable (e , (H , H-def)) = contradiction
  where
    {-
      Intuitively, on input x, K runs H[x,x].
      If H[x,x] returns 0 indicating that x loops on input x, then K halts
      If H[x,x] returns 1 indicating that x halts on input x, then K loops
    -}

    K' = μR-K-helper
    
    K'[0]≡0 : K' [ (0 ∷ []) ]= 0
    K'[0]≡0 = μR-K-helper-halts-on-0
    
    ¬Defined[K'[1]] = μR-K-helper-loops-on-1

    π₀ = proj 1 zero
    
    K : μR 1
    K = comp K' (comp H (π₀ ∷ π₀ ∷ []) ∷ [])

    ϕ = e K
    H[ϕ,ϕ] = H [ (ϕ ∷ ϕ ∷ []) ]= 1
    ¬H[ϕ,ϕ] = H [ (ϕ ∷ ϕ ∷ []) ]= 0

    {-
      By definition, H always terminates with output either 0 or 1
    -}
    LEM[H[ϕ,ϕ]] : ¬H[ϕ,ϕ] ⊎ H[ϕ,ϕ]
    LEM[H[ϕ,ϕ]] = proj₁ (H-def K (ϕ ∷ []))

    {-
      By definition, H terminates with 1 on input pair (ϕ₁, ϕ₂) exactly when ϕ₁ = e P where P is a μ-recursive function and P is defined on input ϕ₂ 
    -}
    H[ϕ,ϕ]→Defined[K[ϕ]] : H[ϕ,ϕ] → μR-Defined K (ϕ ∷ [])
    H[ϕ,ϕ]→Defined[K[ϕ]] = proj₁ (proj₂ (H-def K (ϕ ∷ [])))

    Defined[K[ϕ]]→H[ϕ,ϕ] : μR-Defined K (ϕ ∷ []) → H[ϕ,ϕ]
    Defined[K[ϕ]]→H[ϕ,ϕ] = proj₂ (proj₂ (H-def K (ϕ ∷ [])))

    

    {-
      K is not defined on input ϕ, because then H[ϕ,ϕ] ≡ 1, and then K' must be defined on 1 otherwise K would be undefined on ϕ, but K' is not defined on 1
    -}
    ¬Defined[K[ϕ]] : ¬ (μR-Defined K (ϕ ∷ []))
    ¬Defined[K[ϕ]] Defined[K[ϕ]]@(y , K[ϕ]≡y) = contradiction
      where
        H[ϕ,ϕ]≡1 : H [ (ϕ ∷ ϕ ∷ []) ]= 1
        H[ϕ,ϕ]≡1 = Defined[K[ϕ]]→H[ϕ,ϕ] Defined[K[ϕ]]

        {-
          If K(ϕ) ≡ y then there must be some v such that <H∘<π₀,π₀>>[ϕ] ≡ v and K'(v) ≡ y
        -}

        ∃v,[H[ϕ,ϕ]≡v]×[K'[v]≡y] : Σ[ v ∈ Vec ℕ 1 ] ((fold[ (comp H (π₀ ∷ π₀ ∷ []) ∷ []) , (ϕ ∷ []) ]= v) × K' [ v ]= y)
        ∃v,[H[ϕ,ϕ]≡v]×[K'[v]≡y] = K[ϕ]≡y

        {-
          All of this to establish that v ≡ (x ∷ [])
        -}
        v : Vec ℕ 1
        v = proj₁ K[ϕ]≡y
      
        x : ℕ
        x = head v

        v≡x∷[] : v ≡ (x ∷ [])
        v≡x∷[] = Vec1-ext v


        <H∘<π₀,π₀>>[ϕ]≡v : fold[ (comp H (π₀ ∷ π₀ ∷ []) ∷ []) , (ϕ ∷ []) ]= v
        <H∘<π₀,π₀>>[ϕ]≡v = proj₁ (proj₂ K[ϕ]≡y)

        <H∘<π₀,π₀>>[ϕ]≡[x] : fold[ (comp H (π₀ ∷ π₀ ∷ []) ∷ []) , (ϕ ∷ []) ]= (x ∷ [])
        <H∘<π₀,π₀>>[ϕ]≡[x] = resp (λ r → fold[ (comp H (π₀ ∷ π₀ ∷ []) ∷ []) , (ϕ ∷ []) ]= r) v≡x∷[] <H∘<π₀,π₀>>[ϕ]≡v

        H∘<π₀,π₀>[ϕ]≡x :  (comp H (π₀ ∷ π₀ ∷ [])) [ (ϕ ∷ []) ]= x
                       -- Σ[ v₂ ∈ Vec ℕ 2 ] ((fold[ (π₀ ∷ π₀ ∷ []) , (ϕ ∷ []) ]= v₂ ) × (H [ v₂ ]= x))
        H∘<π₀,π₀>[ϕ]≡x = proj₁ <H∘<π₀,π₀>>[ϕ]≡[x]


        {-
          If H∘<π₀,π₀>(ϕ) ≡ x then there must exist v₂ such that <π₀,π₀>(ϕ) ≡ v₂ and H(v₂) ≡ x
        -}
        v₂ : Vec ℕ 2
        v₂ = proj₁ H∘<π₀,π₀>[ϕ]≡x

        <π₀,π₀>[ϕ]≡v₂ : fold[ (π₀ ∷ π₀ ∷ []) , (ϕ ∷ []) ]= v₂
        <π₀,π₀>[ϕ]≡v₂ = proj₁ (proj₂ H∘<π₀,π₀>[ϕ]≡x)

        {-
          But <π₀,π₀>(ϕ) ≡ (ϕ ∷ ϕ ∷ []), so because μ-recursive functions are functional, v₂ ≡ (ϕ ∷ ϕ ∷ [])
        -}
        <π₀,π₀>[ϕ]≡[ϕ,ϕ] : fold[ (π₀ ∷ π₀ ∷ []) , (ϕ ∷ []) ]= (ϕ ∷ ϕ ∷ [])
        <π₀,π₀>[ϕ]≡[ϕ,ϕ] = (refl , (refl , unit))

        v₂≡[ϕ,ϕ] : v₂ ≡ (ϕ ∷ ϕ ∷ [])
        v₂≡[ϕ,ϕ] = μR-functional-vec (π₀ ∷ π₀ ∷ []) (ϕ ∷ []) v₂ (ϕ ∷ ϕ ∷ []) <π₀,π₀>[ϕ]≡v₂ <π₀,π₀>[ϕ]≡[ϕ,ϕ]


        {-
          Because H(v₂) ≡ x and v₂ ≡ [ϕ,ϕ], it must be the case that H(ϕ,ϕ) ≡ x
        -}
        H[v₂]≡x : H [ v₂ ]= x
        H[v₂]≡x = proj₂ (proj₂ H∘<π₀,π₀>[ϕ]≡x)

        H[ϕ,ϕ]≡x : H [ (ϕ ∷ ϕ ∷ []) ]= x
        H[ϕ,ϕ]≡x = resp (λ r → H [ r ]= x) v₂≡[ϕ,ϕ] H[v₂]≡x

        x≡1 : x ≡ 1
        x≡1 = μR-functional H (ϕ ∷ ϕ ∷ []) x 1 H[ϕ,ϕ]≡x H[ϕ,ϕ]≡1

        x∷[]≡1∷[] : (x ∷ []) ≡ (1 ∷ [])
        x∷[]≡1∷[] = cong (λ r → r ∷ []) x≡1

        v≡1∷[] : v ≡ (1 ∷ [])
        v≡1∷[] = ≡-trans v≡x∷[] x∷[]≡1∷[]

        K'[v]≡y : K' [ v ]= y
        K'[v]≡y = proj₂ (proj₂ ∃v,[H[ϕ,ϕ]≡v]×[K'[v]≡y])

        K'[1]≡y : K' [ (1 ∷ []) ]= y
        K'[1]≡y = resp (λ r → K' [ r ]= y) v≡1∷[] K'[v]≡y

        Defined[K'[1]] = y , K'[1]≡y

        contradiction = ¬Defined[K'[1]] Defined[K'[1]]

    {-
      H(ϕ,ϕ) ≢ 1 because H(ϕ,ϕ) → K is defined on ϕ, by definition of H, but K is not defined on ϕ
    -}
    H[ϕ,ϕ]≢1 : ¬ (H [ (ϕ ∷ ϕ ∷ []) ]= 1)
    H[ϕ,ϕ]≢1 H[ϕ,ϕ]≡1 = ¬Defined[K[ϕ]] (H[ϕ,ϕ]→Defined[K[ϕ]] H[ϕ,ϕ]≡1)

    {-
      H(ϕ,ϕ) ≢ 0 because ¬H(ϕ,ϕ) → K is defined on ϕ, by definition of K (note K'[0] ≡ 0), but K is not defined on ϕ
    -}
    H[ϕ,ϕ]≢0 : ¬ (H [ (ϕ ∷ ϕ ∷ []) ]= 0)
    H[ϕ,ϕ]≢0 H[ϕ,ϕ]≡0 = contradiction
      where
        K[ϕ]≡0 : K [ (ϕ ∷ []) ]= 0
        K[ϕ]≡0 = subsubproof
          where
            <π₀,π₀>[ϕ]≡[ϕ,ϕ] : fold[ (π₀ ∷ π₀ ∷ []) , (ϕ ∷ []) ]= (ϕ ∷ ϕ ∷ [])
            <π₀,π₀>[ϕ]≡[ϕ,ϕ] = refl , (refl , unit)

            <H∘<π₀,π₀>>[ϕ]≡0 : fold[ (comp H (π₀ ∷ π₀ ∷ []) ∷ []) , (ϕ ∷ []) ]= (0 ∷ [])
            <H∘<π₀,π₀>>[ϕ]≡0 = ((ϕ ∷ ϕ ∷ []) , (<π₀,π₀>[ϕ]≡[ϕ,ϕ] , H[ϕ,ϕ]≡0)) , unit
            
            subsubproof = (0 ∷ []) , (<H∘<π₀,π₀>>[ϕ]≡0 , K'[0]≡0)
            
        Defined[K[ϕ]] : μR-Defined K (ϕ ∷ [])
        Defined[K[ϕ]] = 0 , K[ϕ]≡0
        
        contradiction = ¬Defined[K[ϕ]] Defined[K[ϕ]]

    ¬LEM[H[ϕ,ϕ]] : ¬ (¬H[ϕ,ϕ] ⊎ H[ϕ,ϕ])
    ¬LEM[H[ϕ,ϕ]] (inj₁ H[ϕ,ϕ]≡0) = H[ϕ,ϕ]≢0 H[ϕ,ϕ]≡0
    ¬LEM[H[ϕ,ϕ]] (inj₂ H[ϕ,ϕ]≡1) = H[ϕ,ϕ]≢1 H[ϕ,ϕ]≡1
    
    contradiction = ¬LEM[H[ϕ,ϕ]] LEM[H[ϕ,ϕ]]
