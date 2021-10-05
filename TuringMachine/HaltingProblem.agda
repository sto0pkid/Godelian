module TuringMachine.HaltingProblem where

open import Basic renaming (ℕ to Nat)
open import TuringMachine3
open import TuringMachine.Properties


{-
derelativize by actually defining K:
 * Given 3 Turing machine M and input i, run M on input i,
   if it ever halts with output 0, halt
   if it ever halts with output 1, loop
need a UTM for such a construction, but there are possibly other constructions
-}
record HaltingProblem : Set where
  field
    n : Nat
    m : Nat
    H : TM (suc n) (suc (suc m))
    e₁ : {n' m' : Nat} → TM n' m' → List (Fin m') → List (Fin (suc (suc m)))
    e₂ : {n' m' m'' : Nat} → TM n' m' → List (Fin m'')
    H-semantics :
      {n' m' : Nat} →
      (M : TM (suc n') m') →
      (i : List (Fin m')) →
      Σ[ output ∈ List (Fin (suc (suc m))) ] (
          (TM-outputs H (e₁ M i) output)
        × ((output [ 0 ]? ≡ just zero) ⊎ (output [ 0 ]? ≡ just (suc zero)))
        × ((output [ 0 ]? ≡ just (suc zero)) ↔ TM-halts M i)
        × ((output [ 0 ]? ≡ just zero) ↔ TM-loops M i)
      )
    K : TM (suc n) (suc (suc m))
    K-semantics :
      {n' m' : Nat} →
      (M : TM (suc n') m') →
      ((Σ[ output ∈ List (Fin (suc (suc m))) ] (
        (TM-outputs H (e₁ M (e₂ M)) output)
        × (output [ 0 ]? ≡ just (suc zero))
      )) ↔ TM-loops K (e₂ M))
      × ((Σ[ output ∈ List (Fin (suc (suc m))) ] (
        (TM-outputs H (e₁ M (e₂ M)) output)
        × (output [ 0 ]? ≡ just zero)
      )) ↔ TM-halts K (e₂ M))
    

HaltingProblem-undecidable : ¬ HaltingProblem
HaltingProblem-undecidable R = proof
  where
    open HaltingProblem R

    problem = K-semantics K

    H-output : Σ[ output ∈ List (Fin (suc (suc m))) ] (
          (TM-outputs H (e₁ K (e₂ K)) output)
        × ((output [ 0 ]? ≡ just zero) ⊎ (output [ 0 ]? ≡ just (suc zero)))
        × ((output [ 0 ]? ≡ just (suc zero)) ↔ TM-halts K (e₂ K))
        × ((output [ 0 ]? ≡ just zero) ↔ TM-loops K (e₂ K))
      )
    H-output = H-semantics K (e₂ K)

    H-output-tape : List (Fin (suc (suc m)))
    H-output-tape = proj₁ H-output

    H-outputs-output : TM-outputs H (e₁ K (e₂ K)) H-output-tape
    H-outputs-output = proj₁ (proj₂ H-output)
    
    H-decided : (H-output-tape [ 0 ]? ≡ just zero) ⊎ (H-output-tape [ 0 ]? ≡ just (suc zero))
    H-decided = proj₁ (proj₂ (proj₂ H-output))

    K-halts-if-true : (H-output-tape [ 0 ]? ≡ just (suc zero)) → TM-halts K (e₂ K)
    K-halts-if-true = proj₁ (proj₁ (proj₂ (proj₂ (proj₂ H-output))))

    K-loops-if-false : (H-output-tape [ 0 ]? ≡ just zero) → TM-loops K (e₂ K)
    K-loops-if-false = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ H-output))))

    K-loops-if-true :
     Σ[ output ∈ List (Fin (suc (suc m))) ] (
         (TM-outputs H (e₁ K (e₂ K)) output)
       × (output [ 0 ]? ≡ just (suc zero))
     ) → TM-loops K (e₂ K)
    K-loops-if-true hyp = (proj₁ (proj₁ problem)) hyp

    K-halts-if-false :
     Σ[ output ∈ List (Fin (suc (suc m))) ] (
         (TM-outputs H (e₁ K (e₂ K)) output)
       × (output [ 0 ]? ≡ just zero)
     ) → TM-halts K (e₂ K)
    K-halts-if-false hyp = (proj₁ (proj₂ problem)) hyp

    ¬output-false : ¬ (H-output-tape [ 0 ]? ≡ just zero)
    ¬output-false hyp = K-loops K-halts
      where
        K-loops : TM-loops K (e₂ K)
        K-loops = K-loops-if-false hyp

        K-halts : TM-halts K (e₂ K)
        K-halts = K-halts-if-false  (H-output-tape , (H-outputs-output  , hyp))

    ¬output-true : ¬ (H-output-tape [ 0 ]? ≡ just (suc zero))
    ¬output-true hyp = K-loops K-halts
      where
        K-loops : TM-loops K (e₂ K)
        K-loops = K-loops-if-true (H-output-tape , (H-outputs-output , hyp))

        K-halts : TM-halts K (e₂ K)
        K-halts = K-halts-if-true hyp

    ¬H-decided : ¬ ((H-output-tape [ 0 ]? ≡ just zero) ⊎ (H-output-tape [ 0 ]? ≡ just (suc zero)))
    ¬H-decided (inj₁ hyp) = ¬output-false hyp
    ¬H-decided (inj₂ hyp) = ¬output-true hyp

    proof = ¬H-decided H-decided



K-helper : List (TM-δ 3 3)
K-helper =
  -- if 0, halt immediately
    (δ q₀ s₀ q₂ s₀ L)
  -- if 1, loop forever
  ∷ (δ q₀ s₁ q₁ s₁ R)
  ∷ (δ q₁ b  q₁ b  R)
  ∷ (δ q₁ s₀ q₁ s₀ R)
  ∷ (δ q₁ s₁ q₁ s₁ R)
  ∷ []
  where
    q₀ = zero
    q₁ = suc zero
    q₂ = suc (suc zero)
    
    b = zero
    s₀ = suc zero
    s₁ = suc (suc zero)

    L = false
    R = true


K-helper-halts-on-0 :
  let
    s₀ = suc zero
  in
    TM-halts (TM-from-table K-helper) (s₀ ∷ [])
K-helper-halts-on-0 = 2 , refl

K-helper-loops-on-1 :
  let
    s₁ = suc (suc zero)
  in
    TM-loops (TM-from-table K-helper) (s₁ ∷ [])
K-helper-loops-on-1 (0 , ())
K-helper-loops-on-1 ((suc steps) , halted) = proof
  where
    q₁ = suc zero

    s₁ = suc (suc zero)

    R = true
 
    K = (TM-from-table K-helper)

    tape = (s₁ ∷ [])

    lemma1 : (s : Fin 3) → K (q₁ , s) ≡ just (q₁ , (s , R)) 
    lemma1 zero = refl
    lemma1 (suc zero) = refl
    lemma1 (suc (suc zero)) = refl

    lemma2 : (n : Nat) → TM-state.state (TM-run n K tape) ≡ q₁ → (TM-state.state (TM-run (suc n) K tape) ≡ q₁) × (TM-state.halted (TM-run (suc n) K tape) ≡ false)
    lemma2 n hyp = subproof
      where
        config = TM-run n K tape
        q = TM-state.state config
        t = TM-state.tape config
        p = TM-state.pos config
        s = (get-default zero t p)
        condition = (q , (t , p))

        sublemma1a : fold (TM-start-state K tape) (TM-step-state K) n ≡ TM-run n K tape
        sublemma1a = refl

        sublemma1 : (TM-run (suc n) K tape) ≡ (TM-step-state K (TM-run n K tape))
        sublemma1 = cong (λ state → TM-step-state K state) sublemma1a

        sublemma2 :
            (TM-step-state K (TM-run n K tape)) ≡
            (TM-apply-step config (TM-step K condition))
        sublemma2 = refl

        sublemma3 :
            (TM-step K condition) ≡
            (TM-apply-δ condition (K (q , s)))
        sublemma3 = refl

        sublemma4 :
            (K (q , s)) ≡ 
            (K (q₁ , s))
        sublemma4 = cong (λ x → K (x , s)) hyp
        
        sublemma5 :
            (K (q₁ , s)) ≡
            (just (q₁ , (s , R)))
        sublemma5 = lemma1 s
        
        sublemma6 :
          (TM-apply-δ condition (K (q , s))) ≡
          (TM-apply-δ condition (just (q₁ , (s , R))))
        sublemma6 = cong (λ x → TM-apply-δ condition x) (≡-trans sublemma4 sublemma5)

        sublemma7 :
          (TM-apply-δ condition (just (q₁ , (s , R)))) ≡
          (inj₁ (TM-apply-transition condition (q₁ , (s , R))))
        sublemma7 = refl

        sublemma8 :
          (TM-step K condition) ≡
          (TM-apply-δ condition (just (q₁ , (s , R))))
        sublemma8 = ≡-trans sublemma3 sublemma6

        sublemma9 :
          (TM-step K condition) ≡
          (inj₁ (TM-apply-transition condition (q₁ , (s , R))))
        sublemma9 = ≡-trans sublemma8 sublemma7

        sublemma10 :
           (TM-apply-step config (TM-step K condition)) ≡
           (TM-apply-step config (inj₁ (TM-apply-transition condition (q₁ , (s , R)))))
        sublemma10 = cong (λ x → TM-apply-step config x) sublemma9

        sublemma11 :
          TM-state.state (TM-apply-step config (inj₁ (TM-apply-transition condition (q₁ , (s , R)))))
          ≡ (proj₁ (TM-apply-transition condition (q₁ , (s , R))))
        sublemma11 = refl

        sublemma12 :
          (proj₁ (TM-apply-transition condition (q₁ , (s , R))))
          ≡ q₁
        sublemma12 = refl

        sublemma13 :
          (TM-run (suc n) K tape) ≡ 
          (TM-apply-step config (inj₁ (TM-apply-transition condition (q₁ , (s , R)))))
        sublemma13 = (≡-trans sublemma1 (≡-trans sublemma2 sublemma10))
        
        sublemma14 :
          TM-state.state (TM-run (suc n) K tape) ≡
          TM-state.state (TM-apply-step config (inj₁ (TM-apply-transition condition (q₁ , (s , R)))))
        sublemma14 = cong (λ x → TM-state.state x) sublemma13
      
        sublemma15 :
          TM-state.state (TM-run (suc n) K tape) ≡
          q₁
        sublemma15 = ≡-trans sublemma14 (≡-trans sublemma11 sublemma12)

        sublemma16 :
          TM-state.halted (TM-apply-step config (inj₁ (TM-apply-transition condition (q₁ , (s , R))))) ≡ false
        sublemma16 = refl

        sublemma17 :
          TM-state.halted (TM-run (suc n) K tape) ≡
          TM-state.halted (TM-apply-step config (inj₁ (TM-apply-transition condition (q₁ , (s , R)))))
        sublemma17 = cong (λ x → TM-state.halted x) sublemma13

        sublemma18 :
          TM-state.halted (TM-run (suc n) K tape) ≡
          false
        sublemma18 = ≡-trans sublemma17 sublemma16
        subproof = sublemma15 , sublemma18
        
    lemma3 : (n : Nat) → (TM-state.state (TM-run (suc n) K (s₁ ∷ [])) ≡ q₁) × (TM-state.halted (TM-run (suc n) K (s₁ ∷ [])) ≡ false)
    lemma3 0 = refl , refl
    lemma3 (suc n) = subproof
      where
        prev-state-is-q₁ : TM-state.state (TM-run (suc n) K (s₁ ∷ [])) ≡ q₁
        prev-state-is-q₁ = proj₁ (lemma3 n)
        
        subproof = lemma2 (suc n) prev-state-is-q₁

    true=false : true ≡ false
    true=false = ≡-trans (≡-sym halted) (proj₂ (lemma3 steps))

    proof = true≠false true=false
