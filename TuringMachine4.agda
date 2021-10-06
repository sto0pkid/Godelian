module TuringMachine4 where

open import Basic hiding (_^_) renaming (func-rep to _^_)

data TM-δ : Set where
  δ : ℕ → ℕ → ℕ → ℕ → Bool → TM-δ

TM : Set
TM = List TM-δ

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
