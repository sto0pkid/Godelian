module TuringMachine3 where

open import Basic renaming (ℕ to Nat ; ℕ-LEM to Nat-LEM)

TM : (n m : Nat) → Set
TM n m = (Fin n) × (Fin m) → Maybe ((Fin n) × ((Fin m) × Bool))

TM-0,m : (m : Nat) → TM 0 m
TM-0,m m (() , _)

TM-0,0 : TM 0 0
TM-0,0 = TM-0,m 0

TM-δ-config : (n m : Nat) → Set
TM-δ-config n m = (Fin n) × ((List (Fin m)) × Nat)

TM-δ-output : (n m : Nat) → Set
TM-δ-output n m = ((Fin n) × ((List (Fin m)) × Nat)) ⊎ (List (Fin m))



record TM-state (n m : Nat) : Set where
  field
    state : Fin n
    tape : List (Fin m)
    pos : Nat
    halted : Bool

TM-apply-δ-just : {n m : Nat} → TM-δ-config n (suc m) → (Fin n) × ((Fin (suc m)) × Bool) → TM-δ-config n (suc m)
TM-apply-δ-just (_ , (tape , pos)) (new-state , (write , LR)) = (new-state , (new-tape , new-pos))
  where
     new-pos = if LR then (suc pos) else (pred pos)
     new-tape =
       if (pos ge (length tape)) then
         (write ∷ tape)
       else
         (set tape pos write)


TM-apply-δ : {n m : Nat} → (Fin n) × ((List (Fin (suc m))) × Nat) → Maybe ((Fin n) × ((Fin (suc m)) × Bool)) → ((Fin n) × ((List (Fin (suc m))) × Nat)) ⊎ (List (Fin (suc m)))
TM-apply-δ (_ , (tape , _))  nothing = inj₂ tape
TM-apply-δ condition (just δ) = inj₁ (TM-apply-δ-just condition δ)


TM-step : {n m : Nat} → TM n m → (Fin n) × ((List (Fin m)) × Nat) → ((Fin n) × ((List (Fin m)) × Nat)) ⊎ (List (Fin m))
TM-step {n} {0} tm (state , ([] , pos)) = inj₁ (state , ([] , pos))
TM-step {n} {suc m} tm condition = TM-apply-δ condition δ 
  where
    state = proj₁ condition
    tape = proj₁ (proj₂ condition)
    pos = proj₂ (proj₂ condition)
    δ = tm (state , (get-default zero tape pos))
    {-
    get-results : Maybe ((Fin n) × ((Fin (suc m)) × Bool)) → ((Fin n) × ((List (Fin (suc m))) × Nat)) ∨ (List (Fin (suc m)))
    get-results nothing = inr tape
    get-results (just (new-state , (write , LR))) = inl (new-state , (new-tape , new-pos))
      where
        new-pos = if LR then (suc pos) else (pred pos)
        new-tape =
          if (pos ge (length tape)) then
            (write ∷ tape)
          else
            (set tape pos write)
    -}

TM-apply-step : {n m : Nat} → TM-state n m → TM-δ-output n m → TM-state n m
TM-apply-step {n} {m} s₁ (inj₁ (new-state , (new-tape , new-pos))) =
      record {
        state = new-state ;
        tape = new-tape ;
        pos = new-pos ;
        halted = false
      }
TM-apply-step {n} {m} s₁ (inj₂ x) = output
  where
    open TM-state s₁
    output = record {
        state = state ;
        tape = x ;
        pos = pos ;
        halted = true
      }

TM-step-state : {n m : Nat} → TM n m → TM-state n m → TM-state n m
TM-step-state {n} {m} tm s₁ = TM-apply-step s₁ δ
  where
    open TM-state s₁
    δ = TM-step tm (state , (tape , pos))
    
TM-start-state : {n m : Nat} → TM (suc n) m → List (Fin m) → TM-state (suc n) m
TM-start-state tm tape =
  record {
    state = zero ;
    tape = tape ;
    pos = 0 ;
    halted = false
  }

TM-run : {n m : Nat} → Nat → TM (suc n) m → List (Fin m) → TM-state (suc n) m
TM-run steps M tape = fold (TM-start-state M tape) (TM-step-state M) steps

TM-state-halted : {n m : Nat} → TM-state (suc n) m → Set
TM-state-halted state = halted ≡ true
  where
    open TM-state state

TM-state-outputs : {n m : Nat} → TM-state (suc n) m → List (Fin m) → Set
TM-state-outputs state output = (halted ≡ true) × (tape ≡ output)
  where
    open TM-state state

TM-outputs : {n m : Nat} → TM (suc n) m → List (Fin m) → List (Fin m) → Set
TM-outputs tm input output = Σ[ steps ∈ Nat ] (TM-state-outputs (TM-run steps tm input) output)

TM-halts : {n m : Nat} → TM (suc n) m → List (Fin m) → Set
TM-halts {n} {m} tm input = Σ[ steps ∈ Nat ] (TM-state-halted (TM-run steps tm input))

TM-loops : {n m : Nat} → TM (suc n) m → List (Fin m) → Set
TM-loops tm input = ¬ (TM-halts tm input)

TM-is-UTM : {n m : Nat} → TM (suc n) m → Set
TM-is-UTM {n} {m} M =
  Σ[ G ∈ (TM (suc n) m × List (Fin m) → List (Fin m)) ] (
    (M' : TM (suc n) m) →
    (input output : List (Fin m)) →
    ((TM-outputs M' input output) ↔ (TM-outputs M (G (M' , input)) output))
  )

TM-Kolmogorov : {n m : Nat} → TM (suc n) m → List (Fin m) → Nat → Set
TM-Kolmogorov {n} {m} M s x = min-Nat (λ x' → (Σ[ p ∈ (List (Fin m)) ] ((TM-outputs M p s) × ((length p) ≡ x')))) x

-- There are (1 + n*m*2)^(n*m)  Turing machines with n states, m symbols
-- 1-state, 1-symbol: 3^1 = 3
-- 1-state, 2-symbol: 5^2 = 25
-- 1-state, 3-symbol: 7^3 = 343
-- 2-state, 2-symbol: 9^4 = 6561
-- ...

-- these 3 are the only 1-state, 1-symbol Turing machines
-- loops, writing 0s across the whole tape 
tm-1,1-1 : TM 1 1
tm-1,1-1 (zero , zero) = just (zero , (zero , true))

-- loops in place
tm-1,1-2 : TM 1 1
tm-1,1-2 (zero , zero) = just (zero , (zero , false))

-- halts immediately
tm-1,1-3 : TM 1 1
tm-1,1-3 (zero , zero) = nothing


-- loops, rewriting all input to 0
tm-1,2-1 : TM 1 2
tm-1,2-1 (zero , zero) = just (zero , (zero , true))
tm-1,2-1 (zero , (suc zero)) = just (zero , (zero , true))

-- loops, preserving input
tm-1,2-2 : TM 1 2
tm-1,2-2 (zero , zero) = just (zero , (zero , true))
tm-1,2-2 (zero , (suc zero)) = just (zero , ((suc zero) , true))

-- loops, rewriting all input to 1
tm-1,2-3 : TM 1 2
tm-1,2-3 (zero , zero) = just (zero , ((suc zero) , true))
tm-1,2-3 (zero , (suc zero)) = just (zero , ((suc zero) , true))

-- loops, negating inputs
tm-1,2-4 : TM 1 2
tm-1,2-4 (zero , zero) = just (zero , ((suc zero) , true))
tm-1,2-4 (zero , (suc zero)) = just (zero , (zero , true))

-- loops until it finds a 0, preserving input
tm-1,2-5 : TM 1 2
tm-1,2-5 (zero , zero) = nothing
tm-1,2-5 (zero , (suc zero)) = just (zero , ((suc zero) , true))


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
halting-transition-theorem3 {n} {m} tm condition (out-tape , output-condition) = proof
  where
    state = proj₁ condition
    tape = proj₁ (proj₂ condition)
    pos = proj₂ (proj₂ condition)
    
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


-- tm₃-1,1-1 loops on all inputs
-- nice & easy proof, just listing cases.
tm-1,1-1-loops : (tape : List (Fin 1)) → TM-loops tm-1,1-1 tape
tm-1,1-1-loops tape = proof
  where
    -- show there's no halting condition by cases:
    sublemma1 :
      ¬ (Σ[ condition ∈ ((Fin 1) × (Fin 1)) ] (
              tm-1,1-1 condition ≡ nothing
      ))
    sublemma1 ((zero , zero) , ())

    -- no halting condition implies no halting
    proof = looping-transition-theorem tm-1,1-1 tape sublemma1



-- tm₃-1,1-3 halts on all inputs
tm-1,1-3-halts : (tape : List (Fin 1)) → TM-halts tm-1,1-3 tape
tm-1,1-3-halts [] = 1 , refl
tm-1,1-3-halts (zero ∷ xs) = 1 , proof
  where
    M = tm-1,1-3
    input = (zero ∷ xs)
    
    start-config = TM-start-state M input
    open TM-state start-config

    final-config = TM-step-state M start-config

    config-lemma1 : TM-run 1 M input ≡ final-config
    config-lemma1 = refl

    Fin1-lemma : (x : Fin 1) → x ≡ zero
    Fin1-lemma zero = refl

    symbol-lemma1 : get-default zero input pos ≡ zero
    symbol-lemma1 = Fin1-lemma (get-default zero input pos)

    tm-step : ((Fin 1) × ((List (Fin 1)) × Nat)) ⊎ (List (Fin 1))
    tm-step = TM-step M (state , (input , pos))

    tm-step-lemma1 : tm-step ≡ TM-apply-δ (state , (input , pos)) (M (zero ,  get-default zero input pos))
    tm-step-lemma1 = refl

    tm-step-lemma2 : tm-step ≡ TM-apply-δ (state , (input , pos)) (M (zero , zero))
    tm-step-lemma2 = cong (λ x → TM-apply-δ (state , (input , pos)) (M (zero , x))) symbol-lemma1

    tm-step-lemma3 : tm-step ≡ inj₂ input
    tm-step-lemma3 = tm-step-lemma2

    config-lemma2 : final-config ≡ TM-apply-step start-config tm-step
    config-lemma2 = refl

    config-lemma3 : TM-state.halted (TM-apply-step start-config (inj₂ input)) ≡ true
    config-lemma3 = refl

    config-lemma4 : TM-state.halted final-config ≡ true
    config-lemma4 = resp (λ x → TM-state.halted (TM-apply-step start-config x) ≡ true) (≡-sym tm-step-lemma3) config-lemma3
    
    proof = config-lemma4

data TM-δ (n m : Nat) : Set where
  δ : Fin n → Fin m → Fin n → Fin m → Bool → TM-δ n m



TM-get-δ : {n m : Nat} → TM n m → Fin n → Fin m → Maybe (TM-δ n m)
TM-get-δ {n} {m} M x y = Maybe-map extract (M (x , y))
  where
    extract : (Fin n) × ((Fin m) × Bool) → TM-δ n m
    extract (x' , (y' , d)) = δ x y x' y' d


TM-get-table-group : {n m : Nat} → TM (suc n) (suc m) → List (TM-δ (suc n) (suc m))
TM-get-table-group {n} {m} M = subproof
  where
    subproof : List (TM-δ (suc n) (suc m))
    subproof =
      Fin-filter (λ y →
        TM-get-δ M zero y
      ) (fromℕ m)

TM-get-table-nested : {n m : Nat} → TM (suc n) (suc m) → List (List (TM-δ (suc n) (suc m)))
TM-get-table-nested {n} {m} M = subproof
  where
    subproof : List (List (TM-δ (suc n) (suc m)))
    subproof =
      Fin-map-list (λ x → 
        Fin-filter (λ y →
          TM-get-δ M x y
        ) (fromℕ m)
      ) (fromℕ n)


TM-to-table : {n m : Nat} → TM (suc n) (suc m) → List (TM-δ (suc n) (suc m))
TM-to-table M = foldr _++_ [] (TM-get-table-nested M)


TM-run-table-δ : {n m : Nat} → TM-δ n m → (Fin n) × ((Fin m) × Bool)
TM-run-table-δ (δ x y x' y' d) = x' , (y' , d)

TM-from-table : {n m : Nat} → List (TM-δ (suc n) (suc m)) → TM (suc n) (suc m)
TM-from-table {n} {m} table (x , y) = Maybe-map TM-run-table-δ (List-find match-input table)
  where
    match-input : TM-δ (suc n) (suc m) → Bool
    match-input (δ x' y' _ _ _) = eq-∧ (eq-Fin {suc n}) (eq-Fin {suc m}) (x , y) (x' , y')

{-
Should compute 2n if n is odd, 2n+1 if n is even
-}

tm-table-1,1-1 : List (TM-δ 1 1)
tm-table-1,1-1 =
    (δ zero zero zero zero true)
  ∷ []


tm-table-1,2-4 : List (TM-δ 1 2)
tm-table-1,2-4 =
    (δ q₀ s₀ q₀ s₁ true)
  ∷ (δ q₀ s₁ q₀ s₀ true)
  ∷ []
  where
    q₀ = zero
    s₀ = zero
    s₁ = suc zero

{-
supposed to compute 2n if n is odd, 2n+1 if n is even
http://www.inf.ed.ac.uk/teaching/courses/ci/documents/slides05.pdf
{
  (q0,  0, q1,  0, R),
  (q0,  1, q2,  1, R),
  (q0, ̄b, q3, ̄b, R),
  (q1,  0, q1,  0, R),
  (q1,  1, q2,  1, R),
  (q1, ̄b, q3,  1, L),
  (q2,  0, q1,  0, R),
  (q2,  1, q2,  1, R),
  (q2, ̄b, q3,  0, L)
}
least significant digit is at the end of the tape rather than the start
intuitively:
  q₀ = start state
  q₁ = last read symbol was 0
  q₂ = last read symbol was 1
  q₃ = last read symbol was blank, halt

read out to the end of the tape (i.e. until encountering a blank symbol)
if the last read digit was 0 then it's even, print 1 after the end of the tape = 2n+1
if the last read digit was 1 then it's odd, print 0 after the end of the tape  = 2n

-}
tm-table-4,3-even-odd : List (TM-δ 4 3)
tm-table-4,3-even-odd =
    (δ q₀ s₀ q₁ s₀ R)
  ∷ (δ q₀ s₁ q₂ s₁ R)
  ∷ (δ q₀ b  q₃ b  R)
  ∷ (δ q₁ s₀ q₁ s₀ R)
  ∷ (δ q₁ s₁ q₂ s₁ R)
  ∷ (δ q₁ b  q₃ s₁ L)
  ∷ (δ q₂ s₀ q₁ s₀ R)
  ∷ (δ q₂ s₁ q₂ s₁ R)
  ∷ (δ q₂ b  q₃ s₀ L)
  ∷ []
  where
    q₀ = zero
    q₁ = suc zero
    q₂ = suc (suc zero)
    q₃ = suc (suc (suc zero))
    b = zero
    s₀ = suc zero
    s₁ = suc (suc zero)
    R = true
    L = false

tm-table-1,3-strip : List (TM-δ 1 3)
tm-table-1,3-strip =
    (δ q₀ s₀ q₀ b R)
  ∷ []
  where
    q₀ = zero
    b = zero
    s₀ = suc zero
    R = true

tm-table-5,4-move-bit : List (TM-δ 5 4)
tm-table-5,4-move-bit =
    (δ q₀ b  q₁ sₓ R)
  ∷ (δ q₁ b  q₁ b R)
  ∷ (δ q₁ s₀ q₂ b L)
  ∷ (δ q₁ s₁ q₃ b L)
  ∷ (δ q₂ b  q₂ b L)
  ∷ (δ q₂ sₓ q₄ s₀ L)
  ∷ (δ q₃ b  q₃ b L)
  ∷ (δ q₃ sₓ q₄ s₁ L)
  ∷ []
  where
    q₀ = zero
    q₁ = suc zero
    q₂ = suc (suc zero)
    q₃ = suc (suc (suc zero))
    q₄ = suc (suc (suc (suc zero)))
    b = zero
    s₀ = suc zero
    s₁ = suc (suc zero)
    sₓ = suc (suc (suc zero))
    R = true
    L = false

{-
  shifts the first string of bits to the beginning of the tape, ex:
  bbbb1010bbb --> 1010bbbbbbb
-}
tm-table-10,5-move-bits : List (TM-δ 10 5)
tm-table-10,5-move-bits =
    (δ q₀ b  q₁ sₓ R)
  ∷ (δ q₁ b  q₁ b R)
  ∷ (δ q₁ s₀ q₂ s₀ R)
  ∷ (δ q₁ s₁ q₂ s₁ R)
  ∷ (δ q₂ s₀ q₂ s₀ R)
  ∷ (δ q₂ s₁ q₂ s₁ R)
  ∷ (δ q₂ b  q₃ t  L)
  ∷ (δ q₃ s₀ q₃ s₀ L)
  ∷ (δ q₃ s₁ q₃ s₁ L)
  ∷ (δ q₃ b  q₄ b  R)
  ∷ (δ q₃ sₓ q₄ sₓ R)
  ∷ (δ q₄ b  q₄ b R)
  ∷ (δ q₄ s₀ q₅ b L)
  ∷ (δ q₄ s₁ q₆ b L)
  ∷ (δ q₄ t  q₈ b L)
  ∷ (δ q₅ b  q₅ b L)
  ∷ (δ q₅ sₓ q₇ s₀ R)
  ∷ (δ q₆ b  q₆ b L)
  ∷ (δ q₆ sₓ q₇ s₁ R)
  ∷ (δ q₇ b  q₄ sₓ R)
  ∷ (δ q₈ b  q₈ b L)
  ∷ (δ q₈ sₓ q₈ b L)
  ∷ []
  where
    q₀ = zero
    q₁ = suc zero
    q₂ = suc (suc zero)
    q₃ = suc (suc (suc zero))
    q₄ = suc (suc (suc (suc zero)))
    q₅ = suc (suc (suc (suc (suc zero))))
    q₆ = suc (suc (suc (suc (suc (suc zero)))))
    q₇ = suc (suc (suc (suc (suc (suc (suc zero))))))
    q₈ = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
    
    b = zero
    s₀ = suc zero
    s₁ = suc (suc zero)
    sₓ = suc (suc (suc zero))
    t = suc (suc (suc (suc zero)))
    
    R = true
    L = false


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
-- probably can't prove this because Agda is constructive and the halting problem is undecidable
TM-LEM :
  {n m : Nat} →
  (tm : TM (suc n) m) →
  (tape : List (Fin m)) →
  TM-halts tm tape ⊎ TM-loops tm tape
TM-LEM tm tape = proof
  where
    proof

-}


-- derelativize by actually defining K
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
