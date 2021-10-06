module TuringMachine.Properties where

open import Basic renaming (ℕ to Nat ; ℕ-LEM to Nat-LEM)
open import Relation.Binary.PropositionalEquality as PropEq
open import TuringMachine3 hiding (δ)

TM-state-halted : {n m : Nat} → TM-state (suc n) m → Set
TM-state-halted state = halted ≡ true
  where
    open TM-state state


{-
  Statement that a given TM and input eventually halts
-}
TM-halts : {n m : Nat} → TM (suc n) m → List (Fin m) → Set
TM-halts {n} {m} tm input = Σ[ steps ∈ Nat ] (TM-state-halted (TM-run steps tm input))



{-
  Statement that a given TM and input loops forever
-}
TM-loops : {n m : Nat} → TM (suc n) m → List (Fin m) → Set
TM-loops tm input = ¬ (TM-halts tm input)




{-
  NOTE:
  The following 5 lemmas, halting-transition-theorems 1-5, are building up to the main:
  
  halting-transition-theorem:
   * Which states that if there is an input for which a TM eventually halts, then there is a (state , symbol) pair
     for which the action of that TM is halting
    
  looping-transition-theorem
   * If there is no (state , symbol) pair for which the action of TM is to halt, then the TM never halts on any input

  The latter is just the contrapositive of the former
-}

{-
  PROOF: Applying a halting action to a TM configuration results in the current tape
-}
halting-transition-theorem1 :
  {n m : Nat}
  (tm : TM (1 + n) (1 + m))
  (config : TM-δ-config (1 + n) (1 + m)) →
  TM-apply-δ config nothing ≡ inj₂ (proj₁ (proj₂ config))
halting-transition-theorem1 tm (_ , (tape , _)) = refl


{-
  PROOF: Applying a transition action to a TM configuration applies the transition to get a new configuration
-}
halting-transition-theorem2 :
  {n m : Nat}
  (tm : TM (1 + n) (1 + m))
  (config : TM-δ-config (1 + n) (1 + m))
  (δ : TM-transition (1 + n) (1 + m)) →
  TM-apply-δ config (just δ) ≡ inj₁ (TM-apply-transition config δ)
halting-transition-theorem2 tm (_ , (_ , _)) δ = refl


{-
  PROOF: If the result of applying an action to a TM configuration is an output tape, then the action is a halting action
-}
halting-transition-theorem3 :
  {n m : Nat}
  (tm : TM (1 + n) (1 + m))
  (condition : TM-δ-config (1 + n) (1 + m)) →
  (output : Σ[ tape ∈ (List (Fin (suc m))) ] (
    (TM-step tm condition) ≡ (inj₂ tape)
  )) →
  let
    state = proj₁ condition
    tape = proj₁ (proj₂ condition)
    pos = proj₂ (proj₂ condition)
  in
    (tm (state , (get-default zero tape pos))) ≡ nothing
halting-transition-theorem3 {n} {m} tm condition@(state , (tape , pos)) (out-tape , output-condition) = proof
  where
    δ = tm (state , (get-default zero tape pos))


    ∨-lemma : {A B : Set} → (a : A) → (b : B) → (mk-inl A B a) ≢ (mk-inr A B b)
    ∨-lemma _ _ ()

    δ-lemma1 : (δ ≡ nothing) ⊎ (Σ[ x ∈ TM-transition (1 + n) (1 + m) ] (δ ≡ just x))
    δ-lemma1 = Maybe-LEM δ

    δ-lemma2 : ¬ (Σ[ x ∈ TM-transition (1 + n) (1 + m) ] (δ ≡ just x))
    δ-lemma2 (x , δ=just-x) = subproof
      where
        -- NOTE: memory issues... how does an inj₁ equal an inj₂ ?
        sublemma : inj₁ (TM-apply-transition condition x) ≡ inj₂ out-tape
        sublemma =
          inj₁ (TM-apply-transition condition x) ≡⟨ ≡-sym (halting-transition-theorem2 tm condition x) ⟩
          TM-apply-δ condition (just x)          ≡⟨ ≡-sym (cong (TM-apply-δ condition) δ=just-x) ⟩
          TM-apply-δ condition δ                 ≡⟨ output-condition ⟩
          inj₂ out-tape                          ∎
          where
            open PropEq.≡-Reasoning

        subproof = ∨-lemma (TM-apply-transition condition x) out-tape sublemma --5

    δ-lemma3 : δ ≡ nothing
    δ-lemma3 = process-of-elimination-r δ-lemma1 δ-lemma2

    proof = δ-lemma3




{-
  PROOF:
  If TM-step-state applied to a configuration results in a halted configuration,
  then TM-step applied to that configuration results in an output tape
-}
halting-transition-theorem4 :
  {n m : Nat}
  (tm : TM (1 + n) (1 + m))
  (config1 : TM-state (1 + n) (1 + m))
  (config2 : TM-state (1 + n) (1 + m)) →
  TM-step-state tm config1 ≡ config2 →
  let
    in-state = TM-state.state config1
    in-tape = TM-state.tape config1
    in-pos = TM-state.pos config1
    
    halted = TM-state.halted config2
  in
    (halted ≡ true) →
    Σ[ tape ∈ (List (Fin (1 + m))) ] (
      (TM-step tm (in-state , (in-tape , in-pos))) ≡ (inj₂ tape)
    )
halting-transition-theorem4 {n} {m} tm config1 config2 hyp1 config2-halted = proof
  where
    open TM-state config1

    condition = state , (tape , pos)
    step = TM-step tm condition

    step-lemma1 :
      (Σ[ new-condition ∈ TM-δ-config (1 + n) (1 + m) ] (step ≡ inj₁ new-condition))
      ⊎ (Σ[ out-tape ∈ (List (Fin (suc m))) ] (step ≡ inj₂ out-tape))
    step-lemma1 = ⊎-LEM step

    apply-lemma-l :
      (some-config : TM-state (suc n) (suc m)) →
      (some-condition : TM-δ-config (1 + n) (1 + m) ) →
      let
        some-state = proj₁ some-condition
        some-tape = proj₁ (proj₂ some-condition)
        some-pos = proj₂ (proj₂ some-condition)
      in
        TM-state.halted (TM-apply-step some-config (inj₁ (some-state , (some-tape , some-pos)))) ≡ false
    apply-lemma-l _ _ = refl

    step-lemma2 : ¬ (
      Σ[ new-condition ∈ TM-δ-config (1 + n) (1 + m) ]
        (step ≡ inj₁ new-condition)
      )
    step-lemma2 ((new-state , (new-tape , new-pos)) , hyp) = subproof
      where
        sublemma1 : TM-state.halted (TM-apply-step config1 step) ≡ false
        sublemma1 = resp (λ some-step → TM-state.halted (TM-apply-step config1 some-step) ≡ false) (≡-sym hyp) (apply-lemma-l config1 (new-state , (new-tape , new-pos)))

        sublemma2 : TM-state.halted (TM-apply-step config1 step) ≡ TM-state.halted config2
        sublemma2 = cong TM-state.halted hyp1

        sublemma3 : TM-state.halted (TM-apply-step config1 step) ≡ true
        sublemma3 = ≡-trans sublemma2 config2-halted

        true==false : true ≡ false
        true==false = ≡-trans (≡-sym sublemma3) sublemma1
        subproof = ⊥-elim (true≠false true==false)
    

    step-lemma3 : (Σ[ out-tape ∈ (List (Fin (suc m))) ] (step ≡ inj₂ out-tape))
    step-lemma3 = process-of-elimination step-lemma1 step-lemma2

    proof = step-lemma3




{-
  PROOF:
  If TM-step-state applied to a configuration config1 results in a halted configuration,
  then the TM transition function applied to the (state , symbol) pair of config1 is a halting action.
-}
halting-transition-theorem5 :
  {n m : Nat}
  (tm : TM (suc n) (suc m))
  (config1 : TM-state (suc n) (suc m))
  (config2 : TM-state (suc n) (suc m)) →
  TM-step-state tm config1 ≡ config2 →
  let
    state = TM-state.state config1
    tape = TM-state.tape config1
    pos = TM-state.pos config1
    
    halted = TM-state.halted config2
  in
    (halted ≡ true) →
    (tm (state , (get-default zero tape pos))) ≡ nothing
halting-transition-theorem5 {n} {m} tm config1 config2 hyp1 config2-halted = proof
  where
    open TM-state config1

    condition = state , (tape , pos)
    
    lemma1 :
      Σ[ some-tape ∈ (List (Fin (suc m))) ] (
        (TM-step tm condition) ≡ (inj₂ some-tape)
      )
    lemma1 = halting-transition-theorem4 tm config1 config2 hyp1 config2-halted

    proof : (tm (state , (get-default zero tape pos))) ≡ nothing
    proof = halting-transition-theorem3 tm condition lemma1



{-
  PROOF:
  If there is an input for which M halts, then there is a (state , symbol) pair for which M halts
-}
halting-transition-theorem :
  {n m : Nat}
  (tm : TM (suc n) (suc m))
  (tape : List (Fin (suc m))) →
  TM-halts tm tape →
  Σ[ condition ∈ ((Fin (suc n)) × (Fin (suc m))) ] (
    tm condition ≡ nothing
  )
halting-transition-theorem {n} {m} tm tape halts = proof
  where
    steps = proj₁ halts
    final-config = TM-run steps tm tape
    
    halted : TM-state.halted final-config ≡ true
    halted = proj₂ halts

    start-config = TM-start-state tm tape
    ¬start-config-halted : TM-state.halted start-config ≡ false
    ¬start-config-halted = refl

    final-config≠start-config : final-config ≢ start-config 
    final-config≠start-config hyp = subproof
      where
        true=false : true ≡ false
        true=false = ≡-trans (≡-sym halted) (≡-trans (cong TM-state.halted hyp) ¬start-config-halted)
        subproof = ⊥-elim (true≠false true=false)

    steps-lemma1 : (steps ≡ 0) → final-config ≡ start-config
    steps-lemma1 steps=0 = cong (λ x → TM-run x tm tape) steps=0

    steps-lemma2 : steps ≢ 0
    steps-lemma2 steps=0 = final-config≠start-config (steps-lemma1 steps=0)

    steps-lemma3 : (steps ≡ 0) ⊎ (Σ[ m ∈ Nat ] (steps ≡ suc m))
    steps-lemma3 = Nat-LEM steps

    steps=sm : Σ[ m ∈ Nat ] (steps ≡ suc m)
    steps=sm = process-of-elimination steps-lemma3 steps-lemma2

    steps-1 = proj₁ steps=sm

    pre-final-config : TM-state (suc n) (suc m)
    pre-final-config = TM-run steps-1 tm tape

    config-lemma1 :
      (some-tm : TM (suc n) (suc m))
      (some-tape : List (Fin (suc m)))
      (some-steps : Nat) →
      TM-run some-steps some-tm some-tape ≡ (fold (TM-start-state some-tm some-tape) (TM-step-state some-tm) some-steps)
    config-lemma1 some-tm some-tape some-steps = refl
   
    config-lemma2 :
      (some-tm : TM (suc n) (suc m))
      (some-tape : List (Fin (suc m)))
      (some-steps : Nat) →
      (TM-step-state some-tm) (TM-run some-steps some-tm some-tape) ≡ TM-run (suc some-steps) some-tm some-tape
    config-lemma2 some-tm some-tape some-staps = refl

    config-lemma3 : TM-step-state tm pre-final-config ≡ final-config
    config-lemma3 = cong (λ x → TM-run x tm tape) (≡-sym (proj₂ steps=sm))

    condition : Fin (suc n) × Fin (suc m)
    condition = pre-final-state , pre-final-symbol
      where
        pre-final-state = TM-state.state pre-final-config
        pre-final-tape = TM-state.tape pre-final-config
        pre-final-pos = TM-state.pos pre-final-config
        pre-final-symbol = get-default zero pre-final-tape pre-final-pos

    δ : TM-action (1 + n) (1 + m)
    δ = tm condition

    δ=nothing : δ ≡ nothing
    δ=nothing = halting-transition-theorem5 tm pre-final-config final-config config-lemma3 halted
    
    proof = condition , δ=nothing



{-
  PROOF: 
  If there is no (state , symbol) pair for which M halts, then M loops on all inputs
-}
looping-transition-theorem :
  {n m : Nat}
  (tm : TM (suc n) (suc m))
  (tape : List (Fin (suc m))) →
  ¬ (Σ[ condition ∈ ((Fin (suc n)) × (Fin (suc m))) ] (
    tm condition ≡ nothing
  )) →
  TM-loops tm tape
looping-transition-theorem tm tape = contrapositive (halting-transition-theorem tm tape)




{-
  Statement that a TM-state is a halted state with a given output
-}
TM-state-outputs : {n m : Nat} → TM-state (suc n) m → List (Fin m) → Set
TM-state-outputs state output = (halted ≡ true) × (tape ≡ output)
  where
    open TM-state state



{-
  Statement that a TM eventually halts with a given output
-}
TM-outputs : {n m : Nat} → TM (suc n) m → List (Fin m) → List (Fin m) → Set
TM-outputs tm input output = Σ[ steps ∈ Nat ] (TM-state-outputs (TM-run steps tm input) output)

_[_]=_ : {n m : Nat} → TM (suc n) m → List (Fin m) → List (Fin m) → Set
M [ input ]= output = TM-outputs M input output




{-
  Definition of what it means for a TM to be universal.

  NOTE: this is potentially too strong a definition, it requires exact symbol-wise equality of the outputs.
-}
TM-is-UTM : {n m : Nat} → TM (suc n) m → Set
TM-is-UTM {n} {m} M =
  Σ[ G ∈ (TM (suc n) m × List (Fin m) → List (Fin m)) ] (
    (M' : TM (suc n) m) →
    (input output : List (Fin m)) →
    ((M' [ input ]= output) ↔ (M [ (G (M' , input)) ]= output))
  )


{-
  The Kolmogorov complexity of a string s, represented by a List (Fin m), relative to a program-interpreter machine M, 
  is the length of the smallest program for which M outputs s.

  NOTE:
   * because the Kolmogorov complexity is defined relative to arbitrary TMs, a particular string might not have
     a Kolmogorov complexity for a particular TM, if there is no input for which the TM outputs that string. 
-}
TM-Kolmogorov : {n m : Nat} → TM (suc n) m → List (Fin m) → Nat → Set
TM-Kolmogorov {n} {m} M s x = min-Nat (λ x' → (Σ[ p ∈ (List (Fin m)) ] ((M [ p ]= s) × ((length p) ≡ x')))) x




-- at any step, it's either halted or it hasn't
TM-step-LEM :
  {n m : Nat} →
  (tm : TM (suc n) m) →
  (tape : List (Fin m)) →
  (steps : Nat) →
  let
    halted = TM-state.halted (TM-run steps tm tape)
  in
    (halted ≡ true) ⊎ (halted ≡ false)
TM-step-LEM tm tape steps = Bool-LEM (TM-state.halted (TM-run steps tm tape))




{-
  It's (constructively) not false that a TM either halts or loops

  NOTE:
   * this is just an instance of the statement that the double-negation of LEM is
     constructively true at any type, i.e. ¬ (¬ (A ⊎ ¬A)), where A = (TM-halts tm tape)
-}
¬¬TM-LEM :
  {n m : Nat} →
  (tm : TM (suc n) m) →
  (tape : List (Fin m)) →
  ¬ (¬ (TM-halts tm tape ⊎ TM-loops tm tape))
¬¬TM-LEM {n} {m} tm tape ¬TM-LEM = ¬¬halts ¬halts
  where
    ¬halts : ¬ (TM-halts tm tape)
    ¬halts halts = ¬TM-LEM (inj₁ halts)

    ¬¬halts : ¬ (¬ (TM-halts tm tape))
    ¬¬halts ¬halts = ¬TM-LEM (inj₂ ¬halts)


Fin-add : {n : Nat} → (n' : Nat) → Fin n → Fin (n' + n)
Fin-add 0 m = m
Fin-add (suc n) m = suc (Fin-add n m)
