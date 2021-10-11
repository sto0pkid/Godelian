module TuringMachine4 where

open import Basic hiding (_^_ ; raise) renaming (func-rep to _^_)
open import Util.Arithmetic
open import Util.Bool
open import Util.BoolProp
open import Util.List
open import Util.List.Properties


{-
  Should really be using some kind of standard dict-like interface / associative array
  rather than this ad hoc thing..
-}
data TM-δ : Set where
  δ : ℕ → ℕ → ℕ → ℕ → Bool → TM-δ

TM : Set
TM = List TM-δ

{-
  should be something more like "with default 0 , get l x"
-}
read : ℕ → List ℕ → ℕ
read x l = get-default 0 l x

δ-match : ℕ → ℕ → TM-δ → Bool
δ-match state symbol (δ x y _ _ _) = (state eq x) and (symbol eq y)


record TM-configuration : Set where
  field
    state : ℕ
    tape : List ℕ
    pos : ℕ
    halted : Bool

apply-δ : TM-configuration → Maybe TM-δ → TM-configuration
apply-δ config nothing =
  record{
    state  = state
  ; tape   = tape
  ; pos    = pos
  ; halted = true
  }
  where
    open TM-configuration config
apply-δ config (just (δ _ _ new-state symbol lr)) =
  record{
    state  = new-state
  ; tape   = new-tape
  ; pos    = new-pos
  ; halted = halted
  }
  where
    open TM-configuration config

    new-tape = set tape pos symbol
    new-pos = if lr then (suc pos) else (pred pos)

step : TM → TM-configuration → TM-configuration
step M config = apply-δ config (find (δ-match state (read pos tape)) M)
  where
    open TM-configuration config

start-state : List ℕ → TM-configuration
start-state tape =
  record{
    state  = 0
  ; tape   = tape
  ; pos    = 0
  ; halted = false
  }

run : TM → ℕ → List ℕ → TM-configuration
run M n tape = ((step M) ^ n) (start-state tape)

raise-δ : ℕ → TM-δ → TM-δ
raise-δ n (δ in-state in-symbol out-state out-symbol lr) = δ (n + in-state) in-symbol (n + out-state) out-symbol lr

raise : ℕ → TM → TM
raise n M = map (raise-δ n) M


max-state : TM → ℕ
max-state M = list-max (map f M)
  where
    f : TM-δ → ℕ
    f (δ in-state _ out-state _ _) = max in-state out-state

max-symbol : TM → ℕ
max-symbol M = list-max (map f M)
  where
    f : TM-δ → ℕ
    f (δ _ in-symbol _ out-symbol _) = max in-symbol out-symbol


make-switch : ℕ → ℕ × ℕ → TM-δ
make-switch n (state , symbol) = δ state symbol n symbol true

δ-filter : TM → ℕ × ℕ → Bool
δ-filter M (state , symbol) = not (match (δ-match state symbol) M)


fix : TM → TM
fix M = M ++ (map (make-switch #states) (filter (δ-filter M) inputs))
  where
    #states = 1 + (max-state M)
    #symbols = 1 + (max-symbol M)
    
    states = range #states
    symbols = range #symbols

    inputs : List (ℕ × ℕ)
    inputs = list-product states symbols


{-
  Sequences the actions of two Turing machines

  Each state s in M₁ will correspond to the state s in seq M₁ M₂
  Each state s in M₂ will correspond to the state (1 + (max-state M₁) + s)  in seq M₁ M₂

  In particular state 0 in M₂, the start state of M₂, will correspond to the state (1 + (max-state M₁)) in seq M₁ M₂

  For any (state , symbol) pair for which M₁ would halt, a transition (state , symbol) -> ((1 + (max-state M₁)) , symbol , R) will be added
  
  NOTE:
   * for any input tape for which M₁ loops, seq M₁ M₂ will loop and in particular the action corresponding to M₂ will never run, but
     this is expected behavior.
   * in particular, if there are no (state , symbol) input pairs for which M₁ halts, then the action corresponding to M₂ will never run
     on any input, and all the states corresponding to states of M₂ will be inaccessible. This is still the intended semantics.
  
-}
seq : TM → TM → TM
seq M₁ M₂ = (fix M₁) ++ (raise (1 + (max-state M₁)) M₂)

example1 : TM
example1 =
    (δ 0 0 0 0 true)
  ∷ (δ 1 0 1 0 true)
  ∷ (δ 1 0 0 1 true)
  ∷ []

raise-config : (n : ℕ) → TM-configuration → TM-configuration
raise-config n config =
  record{
    state = n + state
  ; pos = pos
  ; tape = tape
  ; halted = halted
  }
  where
    open TM-configuration config



raise-δ-lemma : (n state symbol : ℕ) (transition : TM-δ) → δ-match state symbol transition ≡ δ-match (n + state) symbol (raise-δ n transition)
raise-δ-lemma 0 _ _ (δ _ _ _ _ _) = refl
raise-δ-lemma (suc n) state symbol transition@(δ a b c d e) = raise-δ-lemma n state symbol transition


raise-find-lemma : (M : TM) (n state symbol : ℕ) → Maybe-map (raise-δ n) (find (δ-match state symbol) M) ≡ find (δ-match (n + state) symbol) (raise n M)
raise-find-lemma M n state symbol = find-preserve (δ-match state symbol) (δ-match (n + state) symbol) (raise-δ n) (raise-δ-lemma n state symbol) M



raise-apply-lemma : (config : TM-configuration) (action : Maybe TM-δ) (n : ℕ) → raise-config n (apply-δ config action) ≡ apply-δ (raise-config n config) (Maybe-map (raise-δ n) action)
raise-apply-lemma _ nothing _ = refl
raise-apply-lemma _ (just (δ _ _ _ _ _)) n = refl

raise-tape-lemma : (config : TM-configuration) (n : ℕ) → TM-configuration.tape (raise-config n config) ≡ TM-configuration.tape config
raise-tape-lemma config n = refl


raise-step-lemma : (M : TM) (n : ℕ) (config : TM-configuration) → raise-config n (step M config) ≡ step (raise n M) (raise-config n config)
raise-step-lemma M n config =
  raise-config n (step M config)

    ≡⟨ cong (raise-config n) refl ⟩
    
  raise-config n (apply-δ config (find (δ-match state (read pos tape)) M))

    ≡⟨ raise-apply-lemma config (find (δ-match state (read pos tape)) M) n ⟩

  apply-δ (raise-config n config) (Maybe-map (raise-δ n) (find (δ-match state (read pos tape)) M))

    ≡⟨ cong (apply-δ (raise-config n config)) (raise-find-lemma M n state (read pos tape)) ⟩

  step (raise n M) (raise-config n config)

    ∎
  where
    open TM-configuration config
    open ≡-Reasoning


raise-equivalence : (M : TM) (n : ℕ) (config : TM-configuration) (steps : ℕ) → raise-config n (((step M) ^ steps) config) ≡ ((step (raise n M)) ^ steps) (raise-config n config)
raise-equivalence M n config 0 = refl
raise-equivalence M n config (suc s) =
  raise-config n (((step M) ^ (1 + s)) config)                        ≡⟨  refl ⟩
  raise-config n ((step M) (((step M) ^ s) config))                   ≡⟨ raise-step-lemma M n (((step M) ^ s) config) ⟩
  step (raise n M) (raise-config n (((step M) ^ s) config))           ≡⟨ cong (step (raise n M)) (raise-equivalence M n config s) ⟩
  step (raise n M) (((step (raise n M)) ^ s) (raise-config n config)) ≡⟨ refl ⟩
  ((step (raise n M)) ^ (1 + s)) (raise-config n config)              ∎
  where
    open ≡-Reasoning














  
{-
fix-match-lemma1 :
  (M : TM) →
  (state symbol : ℕ) →
  (state ≤ max-state M) →
  (symbol ≤ max-symbol M) →
  find (δ-match state symbol) M ≡ nothing → 
  find (δ-match state symbol) (fix M) ≡ just (δ state symbol (1 + (max-state M)) symbol true)
fix-match-lemma1 M state symbol state≤max-states symbol≤max-symbols no-match = proof
  where
    #states = 1 + (max-state M)
    #symbols = 1 + (max-symbol M)

    state<#states : state < #states
    state<#states = begin-strict
      state               ≤⟨ state≤max-states ⟩ 
      max-state M         <⟨ n<1+n (max-state M) ⟩
      1 + (max-state M)   ∎
      where
        open ≤-Reasoning

    symbol<#symbols : symbol < #symbols
    symbol<#symbols = begin-strict
      symbol               ≤⟨ symbol≤max-symbols ⟩
      max-symbol M         <⟨ n<1+n (max-symbol M) ⟩
      1 + (max-symbol M)   ∎
      where
        open ≤-Reasoning
    
    states = range #states
    symbols = range #symbols

    inputs = list-product states symbols

    lemma1 : (fix M) ≡ M ++ (map (make-switch #states) (filter (δ-filter M) inputs))
    lemma1 = refl

    lemma2 :
        find (δ-match state symbol) (fix M)
      ≡ find (δ-match state symbol) (map (make-switch #states) (filter (δ-filter M) inputs))
    lemma2 = find-++-lemma (δ-match state symbol) M (map (make-switch #states) (filter (δ-filter M) inputs)) no-match


    lemma3 : not (match (δ-match state symbol) M) ≡ true
    lemma3 = cong not (find-match-lemma (δ-match state symbol) M no-match)

    lemma4 : Σ[ i ∈ ℕ ] (inputs [ i ]? ≡ just (state , symbol))
    lemma4 = product-complete state<#states symbol<#symbols

    i = proj₁ lemma4
    
    inputs[i]≡[state,symbol] = proj₂ lemma4

    lemma5 : δ-filter M (state , symbol) ≡ true
    lemma5 = lemma3

    lemma6 : Σ[ j ∈ ℕ ] ((filter (δ-filter M) inputs) [ j ]? ≡ just (state , symbol))
    lemma6 = filter-index-lemma (δ-filter M) inputs i (state , symbol) inputs[i]≡[state,symbol] lemma5

    j = proj₁ lemma6

    lemma7 : (filter (δ-filter M) inputs) [ j ]? ≡ just (state , symbol)
    lemma7 = proj₂ lemma6

    lemma8 : (map (make-switch #states) (filter (δ-filter M) inputs)) [ j ]? ≡ Maybe-map (make-switch #states) ((filter (δ-filter M) inputs) [ j ]?)
    lemma8 = get-map-lemma (make-switch #states) (filter (δ-filter M) inputs) j

    lemma9 : Maybe-map (make-switch #states) ((filter (δ-filter M) inputs) [ j ]?) ≡ just (δ state symbol #states symbol true)
    lemma9 = cong (Maybe-map (make-switch #states)) lemma7

    lemma10 : i ≡ (#symbols - (1 + symbol)) + ((#states - (1 + state)) * #symbols)
    lemma10 = product-uniqueness state<#states symbol<#symbols i inputs[i]≡[state,symbol]
    
    proof
-}
{-
fix-match-lemma2 :
  (M : TM) →
  (state symbol : ℕ) →
  (state ≤ max-state M) →
  (symbol ≤ max-symbol M) → 
  (transition : TM-δ) →
  find (δ-match state symbol) M ≡ just transition →
  find (δ-match state symbol) (fix M) ≡ just transition

-}
