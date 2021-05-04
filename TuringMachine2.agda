module TuringMachine2 where

open import Basic renaming (ℕ to Nat)
open import Base2

{-
  set of states is Fin (n+1)
  starting state is 0
  Maybe Bool :
    nothing represents blank symbol
    just x represents tape symbol x
  might not be able to be universal with such a restricted definition,
  i.e. might need more symbols
-}
record TuringMachine₂ {n : Nat} : Set where
  field
    δ : (Fin (suc n)) × (Maybe Bool) → Maybe ((Fin (suc n)) × (Bool × Bool))


run₁-bool : {n : Nat} → TuringMachine₂ {n} → Fin (suc n) → Nat → List Bool → (Fin (suc n) × (Nat × (List Bool))) ⊎ (List Bool)
run₁-bool {n} tm state position tape = out
  where
    δ = TuringMachine₂.δ tm
    δ₁ = δ (state , (get tape position))
    get-results : Maybe (Fin (suc n) × (Bool × Bool)) → (Fin (suc n) × (Nat × (List Bool))) ⊎ (List Bool)
    get-results nothing = inj₂ tape
    get-results (just (new_state , (write , LR))) = inj₁ (new_state , (new_position , new_tape))
      where
        new_position = if ((position eq 0) and (not LR)) then 0 else (suc position)
        new_tape =
          if (position gt (length tape)) then
            (write ∷ tape)
          else
            (set tape position write)
    out = get-results δ₁

run-bool-helper : {n : Nat} → TuringMachine₂ {n} → List Bool → Nat → (Fin (suc n) × (Nat × (List Bool))) ⊎ (List Bool)
run-bool-helper {n} tm tape 0 = inj₂ tape
run-bool-helper {n} tm tape 1 = run₁-bool tm zero 0 tape
run-bool-helper {n} tm tape (suc (suc m)) = get-next (run-bool-helper tm tape (suc m))
  where
    get-next : (Fin (suc n) × (Nat × (List Bool))) ⊎ (List Bool) → (Fin (suc n) × (Nat × (List Bool))) ⊎ (List Bool)
    get-next (inj₁ (current-state , (current-position , current-tape))) = run₁-bool tm current-state current-position current-tape
    get-next (inj₂ tape) = inj₂ tape
    -- output = get-next (run-bool-helper tm tape (suc m))


run-bool : {n : Nat} → TuringMachine₂ {n} → List Bool → Nat → List Bool
run-bool {n} tm tape k = get-results (run-bool-helper tm tape k)
  where
    get-results : (Fin (suc n) × (Nat × (List Bool))) ⊎ (List Bool) → List Bool
    get-results (inj₁ (_ , (_ , tape))) = tape
    get-results (inj₂ tape) = tape

δ₁ : Fin 2 × (Maybe Bool) → Maybe (Fin 2 × (Bool × Bool))
δ₁ (zero , nothing) = just ((suc zero) , (false , true))
δ₁ (zero , just _) = nothing
δ₁ ((suc zero) , nothing) = just (zero , (true , false))
δ₁ ((suc zero) , just _) = nothing

tm₁ : TuringMachine₂ {1}
tm₁ = record {δ = δ₁}

run-nat : {n : Nat} → TuringMachine₂ {n} → Nat → Nat → Nat
run-nat {n} tm tape steps = base2→unary (run-bool tm (unary→base2 tape) steps)
