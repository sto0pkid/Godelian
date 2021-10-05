module TuringMachine.Properties where

open import Basic renaming (ℕ to Nat ; ℕ-LEM to Nat-LEM)
open import TuringMachine3 hiding (δ)

TM-state-halted : {n m : Nat} → TM-state (suc n) m → Set
TM-state-halted state = halted ≡ true
  where
    open TM-state state

TM-halts : {n m : Nat} → TM (suc n) m → List (Fin m) → Set
TM-halts {n} {m} tm input = Σ[ steps ∈ Nat ] (TM-state-halted (TM-run steps tm input))

TM-loops : {n m : Nat} → TM (suc n) m → List (Fin m) → Set
TM-loops tm input = ¬ (TM-halts tm input)


halting-transition-theorem1 :
  {n m : Nat}
  (tm : TM (suc n) (suc m))
  (condition : ((Fin (suc n)) × ((List (Fin (suc m))) × Nat))) →
  TM-apply-δ condition nothing ≡ inj₂ (proj₁ (proj₂ condition))
halting-transition-theorem1 tm (_ , (tape , _)) = refl

halting-transition-theorem2 :
  {n m : Nat}
  (tm : TM (suc n) (suc m))
  (condition : ((Fin (suc n)) × ((List (Fin (suc m))) × Nat)))
  (δ : ((Fin (suc n)) × ((Fin (suc m)) × Bool))) →
  TM-apply-δ condition (just δ) ≡ inj₁ (TM-apply-δ-just condition δ)
halting-transition-theorem2 tm (_ , (_ , _)) δ = refl

halting-transition-theorem3 :
  {n m : Nat}
  (tm : TM (suc n) (suc m))
  (condition : ((Fin (suc n)) × ((List (Fin (suc m))) × Nat))) →
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

    δ-lemma1 : (δ ≡ nothing) ⊎ (Σ[ x ∈ ((Fin (suc n)) × ((Fin (suc m)) × Bool)) ] (δ ≡ just x))
    δ-lemma1 = Maybe-LEM δ

    δ-lemma2 : ¬ (Σ[ x ∈ ((Fin (suc n)) × ((Fin (suc m)) × Bool)) ] (δ ≡ just x))
    δ-lemma2 (x , δ=just-x) = subproof
      where
        sublemma1 : (TM-apply-δ condition δ) ≡ (TM-apply-δ condition (just x))
        sublemma1 = cong (TM-apply-δ condition) δ=just-x

        sublemma2 : (TM-apply-δ condition (just x)) ≡ inj₁ (TM-apply-δ-just condition x)
        sublemma2 = halting-transition-theorem2 tm condition x

        sublemma3 : (TM-apply-δ condition δ) ≡ inj₁ (TM-apply-δ-just condition x)
        sublemma3 = ≡-trans sublemma1 sublemma2

        sublemma4 : (TM-apply-δ condition δ) ≡ inj₂ out-tape
        sublemma4 = output-condition

        sublemma5 : inj₁ (TM-apply-δ-just condition x) ≡ inj₂ out-tape
        sublemma5 = ≡-trans (≡-sym sublemma3) sublemma4

        subproof = ∨-lemma (TM-apply-δ-just condition x) out-tape sublemma5

    δ-lemma3 : δ ≡ nothing
    δ-lemma3 = process-of-elimination-r δ-lemma1 δ-lemma2

    proof = δ-lemma3



halting-transition-theorem4 :
  {n m : Nat}
  (tm : TM (suc n) (suc m))
  (config1 : TM-state (suc n) (suc m))
  (config2 : TM-state (suc n) (suc m)) →
  TM-step-state tm config1 ≡ config2 →
  let
    in-state = TM-state.state config1
    in-tape = TM-state.tape config1
    in-pos = TM-state.pos config1
    
    halted = TM-state.halted config2
  in
    (halted ≡ true) →
    Σ[ tape ∈ (List (Fin (suc m))) ] (
      (TM-step tm (in-state , (in-tape , in-pos))) ≡ (inj₂ tape)
    )
halting-transition-theorem4 {n} {m} tm config1 config2 hyp1 config2-halted = proof
  where
    open TM-state config1

    condition = state , (tape , pos)
    step = TM-step tm condition

    step-lemma1 :
      (Σ[ new-condition ∈ ((Fin (suc n)) × ((List (Fin (suc m))) × Nat)) ] (step ≡ inj₁ new-condition))
      ⊎ (Σ[ out-tape ∈ (List (Fin (suc m))) ] (step ≡ inj₂ out-tape))
    step-lemma1 = ⊎-LEM step

    apply-lemma-l :
      (some-config : TM-state (suc n) (suc m)) →
      (some-condition : ((Fin (suc n)) × ((List (Fin (suc m))) × Nat))) →
      let
        some-state = proj₁ some-condition
        some-tape = proj₁ (proj₂ some-condition)
        some-pos = proj₂ (proj₂ some-condition)
      in
        TM-state.halted (TM-apply-step some-config (inj₁ (some-state , (some-tape , some-pos)))) ≡ false
    apply-lemma-l _ _ = refl

    step-lemma2 : ¬ (
      Σ[ new-condition ∈ ((Fin (suc n)) × ((List (Fin (suc m))) × Nat)) ]
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
        (TM-step tm (state , (tape , pos))) ≡ (inj₂ some-tape)
      )
    lemma1 = halting-transition-theorem4 tm config1 config2 hyp1 config2-halted

    lemma2 : (tm (state , (get-default zero tape pos))) ≡ nothing
    lemma2 = halting-transition-theorem3 tm condition lemma1
    
    proof = lemma2


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
    lemma1 :  Σ[ steps ∈ Nat ] (TM-state-halted (TM-run steps tm tape))
    lemma1 = halts

    steps = proj₁ lemma1
    final-config = TM-run steps tm tape
    
    halted : TM-state.halted final-config ≡ true
    halted = proj₂ lemma1

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
    config-lemma3 = subproof
      where
        sublemma1 : TM-step-state tm pre-final-config ≡ TM-run (suc steps-1) tm tape
        sublemma1 = refl

        sublemma2 : TM-run (suc steps-1) tm tape ≡ TM-run steps tm tape
        sublemma2 = cong (λ x → TM-run x tm tape) (≡-sym (proj₂ steps=sm))

        sublemma3 : TM-run steps tm tape ≡ final-config
        sublemma3 = refl
        
        subproof = sublemma2

    condition : Fin (suc n) × Fin (suc m)
    condition = pre-final-state , pre-final-symbol
      where
        pre-final-state = TM-state.state pre-final-config
        pre-final-tape = TM-state.tape pre-final-config
        pre-final-pos = TM-state.pos pre-final-config
        pre-final-symbol = get-default zero pre-final-tape pre-final-pos

    δ : Maybe ((Fin (suc n)) × ((Fin (suc m)) × Bool))
    δ = tm condition

    δ=nothing : δ ≡ nothing
    δ=nothing = halting-transition-theorem5 tm pre-final-config final-config config-lemma3 halted
    
    proof = condition , δ=nothing

looping-transition-theorem :
  {n m : Nat}
  (tm : TM (suc n) (suc m))
  (tape : List (Fin (suc m))) →
  ¬ (Σ[ condition ∈ ((Fin (suc n)) × (Fin (suc m))) ] (
    tm condition ≡ nothing
  )) →
  TM-loops tm tape
looping-transition-theorem tm tape = contrapositive (halting-transition-theorem tm tape)


TM-state-outputs : {n m : Nat} → TM-state (suc n) m → List (Fin m) → Set
TM-state-outputs state output = (halted ≡ true) × (tape ≡ output)
  where
    open TM-state state

TM-outputs : {n m : Nat} → TM (suc n) m → List (Fin m) → List (Fin m) → Set
TM-outputs tm input output = Σ[ steps ∈ Nat ] (TM-state-outputs (TM-run steps tm input) output)

TM-is-UTM : {n m : Nat} → TM (suc n) m → Set
TM-is-UTM {n} {m} M =
  Σ[ G ∈ (TM (suc n) m × List (Fin m) → List (Fin m)) ] (
    (M' : TM (suc n) m) →
    (input output : List (Fin m)) →
    ((TM-outputs M' input output) ↔ (TM-outputs M (G (M' , input)) output))
  )

TM-Kolmogorov : {n m : Nat} → TM (suc n) m → List (Fin m) → Nat → Set
TM-Kolmogorov {n} {m} M s x = min-Nat (λ x' → (Σ[ p ∈ (List (Fin m)) ] ((TM-outputs M p s) × ((length p) ≡ x')))) x


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

