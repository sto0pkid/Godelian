module TuringMachine3 where

open import Basic hiding (raise) renaming (ℕ to Nat ; ℕ-LEM to Nat-LEM ; Fin-raise' to raise)

TM : (n m : Nat) → Set
TM n m = (Fin n) × (Fin m) → Maybe ((Fin n) × ((Fin m) × Bool))

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
TM-step {n} {suc m} tm condition@(state , (tape , pos)) = TM-apply-δ condition δ 
  where
    δ = tm (state , (get-default zero tape pos))

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


data TM-δ (n m : Nat) : Set where
  δ : Fin n → Fin m → Fin n → Fin m → Bool → TM-δ n m



TM-get-δ : {n m : Nat} → TM n m → Fin n → Fin m → Maybe (TM-δ n m)
TM-get-δ {n} {m} M x y = Maybe-map extract (M (x , y))
  where
    extract : (Fin n) × ((Fin m) × Bool) → TM-δ n m
    extract (x' , (y' , d)) = δ x y x' y' d

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

TM-raise : {n m : Nat} → (n' : Nat) → TM n m → TM (n' + n) m
TM-raise {n} {m} n' M (q , s) = 
  (dite
    {λ b → Maybe ((Fin (n' + n) × (Fin m × Bool)))}
    ((toℕ q) lt n)
    (λ case-true →
      fix (M (fromℕ< (lt→< case-true) , s))
    )
    (λ _ → nothing))
  where
    fix : Maybe (Fin n × (Fin m × Bool)) → Maybe (Fin (n' + n) × (Fin m × Bool))
    fix nothing = nothing
    fix (just (q' , (s' , d))) = just ((raise n' q') , (s' , d))


TM-raise+ : {n m : Nat} → (n' : Nat) → TM n m → TM (n' + n) m
TM-raise+ {0} {m} 0 M (() , s)
TM-raise+ {0} {m} (suc n') M (q , s) = nothing
TM-raise+ {suc n} {m} 0 M (q , s)  = M (q , s)
TM-raise+ {suc n} {m} (suc n') M (q , s) = output
  where
    qₙ' : (Fin (((1 + n') + (1 + n)) - (1 + n')))
    qₙ' = Fin-sub q (1 + n') (m<m+1+n (1 + n') n)

    qₙ : Fin (1 + n)
    qₙ = coerce (cong (λ x → Fin x) (x+y-x=y (1 + n') (1 + n))) qₙ'
    
    M-out : Maybe (Fin (1 + n) × (Fin m × Bool))
    M-out = M (qₙ , s)
    
    get-results : Maybe (Fin (1 + n) × (Fin m × Bool)) → Maybe (Fin ((1 + n') + (1 + n)) × (Fin m × Bool))
    get-results nothing = nothing
    get-results (just (q' , (s' , d))) = just ((raise (suc n') q') , (s' , d))
    
    output = get-results M-out

seq : {n n' m : Nat} → (M₁ : TM n m) → (M₂ : TM (1 + n') m) → TM ((1 + n') + n) m
seq {n} {n'} {m} M₁ M₂ = M₁,₂
  where
    fix-M₁ : TM (1 + n' + n) m
    fix-M₁ = TM-raise (1 + n') M₁

    fix-M₂ : TM (1 + n' + n) m
    fix-M₂ = coerce (cong (λ x → TM x m) (+-comm n (1 + n'))) (TM-raise+ n M₂)

    switch : Fin m → Maybe (Fin (1 + n' + n) × Fin m × Bool) → Fin (1 + n' + n) × Fin m × Bool
    switch s nothing = (fromℕ< (m<1+n+m n n')) , (s , true)
    switch s (just output) = output

    M₁,₂ : TM (1 + n' + n) m
    M₁,₂ (q , s) =
      if (Fin-lt q n) then
        just (switch s (fix-M₁ (q , s)))
      else
        fix-M₂ (q , s)
