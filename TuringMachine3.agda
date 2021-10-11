module TuringMachine3 where

open import Basic hiding (raise) renaming (ℕ to Nat)
open import Util.Arithmetic
open import Util.BoolProp
open import Util.DependentIf
open import Util.Fin renaming (Fin-raise' to raise)
open import Util.List

{-
  This represents the instructions for an individual transition
   * next state           : Fin states
   * symbol to write      : Fin symbols
   * move left or right   : Bool
-}
TM-transition : (states symbols : Nat) → Set
TM-transition states symbols = Fin states × (Fin symbols × Bool)




{-
  This represents the actions that can result from an input (state , symbol) pair
  
  Either:
   * `just` the transition to take in the case of non-halting
  OR
   * `nothing` to represent halting
-}
TM-action : (states symbols : Nat) → Set
TM-action states symbols = Maybe (TM-transition states symbols)





{-
  This represents a full transition function:

  Input:
    * state               : Fin states
    * symbol              : Fin symbols
  Output:
    * next state          : Fin states
    * symbol to write     : Fin symbols
    * move left or right  : Bool
  
  If there is no transition for a given (state , symbol) pair then the function returns `nothing`,
  which represents that the machine halts.
-}
TM : (states symbols : Nat) → Set
TM states symbols = (Fin states) × (Fin symbols) → TM-action states symbols





{-
  This represents a particular configuration of the machine
  n = # of states
  m = # of symbols

  * state        : Fin n
  * tape         : List (Fin m)  -- cells beyond the end of the list are implicitly blank
  * position     : Nat

-}
TM-δ-config : (n m : Nat) → Set
TM-δ-config n m = (Fin n) × ((List (Fin m)) × Nat)




{-
  This represents the outputs that can result from a particular transition
  n = # of states
  m = # of symbols

  if there is a transition for a (state , symbol) pair then the transition results in:
   * next state          : Fin n
   * resulting tape      : List (Fin m)
   * next position       : Nat

  otherwise the transition just returns the current tape : List (Fin m)
-}
TM-δ-output : (n m : Nat) → Set
TM-δ-output n m = (TM-δ-config n m) ⊎ (List (Fin m))






{-
  This represents a particular configuration of the machine
-}
record TM-state (n m : Nat) : Set where
  field
    state : Fin n
    tape : List (Fin m)
    pos : Nat
    halted : Bool






{-
  This applies a TM-transition to a configuration to get a new configuration
  n = # states
  1 + m = # symbols

  Inputs:
   * current configuration   : TM-δ-config n (1 + m)
   * action to apply         : TM-action n (1 + m)

  Output:
   * resulting configuration : TM-δ-config n (1 + m)

  TODO: does the # of symbols have to be nonzero?
-}
TM-apply-transition : {n m : Nat} → TM-δ-config n (1 + m) → TM-transition n (1 + m) → TM-δ-config n (1 + m)
TM-apply-transition (_ , (tape , pos)) (new-state , (write , LR)) = (new-state , (new-tape , new-pos))
  where
     new-pos = if LR then (suc pos) else (pred pos)
     new-tape =
       if (pos ge (length tape)) then
         (write ∷ tape)
       else
         (set tape pos write)



{-
  This applies a TM-action to a configuration to get a new configuration or output tape in the case
  that there is no TM-transition

  n = # of states
  1 + m = # of symbols

  Inputs:
   * current configuration                  : TM-δ-config n (1 + m)
   * possible action                        : Maybe (TM-action n (1 + m)) 

  Outputs either:
   * resulting configuration                : TM-δ-config n (1 + m)
  OR
   * output tape                            : List (Fin (1 + m))
-}
TM-apply-δ : {n m : Nat} → TM-δ-config n (1 + m) → TM-action n (1 + m) → TM-δ-output n (1 + m)
TM-apply-δ (_ , (tape , _))  nothing = inj₂ tape
TM-apply-δ condition (just δ) = inj₁ (TM-apply-transition condition δ)




{-
  This runs a TM for one step on a particular configuration to get a new configuration or output tape in the
  case of halting.

  n = # of states
  m = # of symbols

  Inputs:
   * the Turing machine to run             : TM n m
   * current configuration                 : TM-δ-config n m

  Outputs either:
   * resulting configuration               : TM-δ-config n m
  OR
   * output tape                           : List (Fin (1 + m))
-}
TM-step : {n m : Nat} → TM n m → TM-δ-config n m → TM-δ-output n m
TM-step {n} {0} tm (state , ([] , pos)) = inj₁ (state , ([] , pos))
TM-step {n} {suc m} tm condition@(state , (tape , pos)) = TM-apply-δ condition δ 
  where
    δ = tm (state , (get-default zero tape pos))




{-
  This updates a TM-state with the results of a TM-action to get a new TM-state
  
  n = # of states
  m = # of symbols

  Inputs:
   * current state     : TM-state n m
   * action output     : TM-δ-output n m

  Outputs:
   * new state         : TM-state n m
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



{-
  This runs a TM for one step on a TM-state to get a new TM-state
  n = # of states
  m = # of symbols

  Inputs:
   * Turing machine      : TM n m
   * current state       : TM-state n m

  Outputs:
   * next state          : TM-state n m
-}
TM-step-state : {n m : Nat} → TM n m → TM-state n m → TM-state n m
TM-step-state {n} {m} tm s₁ = TM-apply-step s₁ δ
  where
    open TM-state s₁
    δ = TM-step tm (state , (tape , pos))




{-
  This creates a starting TM-state from a Turing machine and an input tape
  1 + n = # of states
  m = # of symbols

  Inputs:
   * Turing machine      : TM (1 + n) m
   * starting tape       : List (Fin m)

  Outputs:
   * starting state      : TM (1 + n) m

  NOTE:
   * the Turing machine is only really needed to get the # of (internal) states;
     this could be supplied explicitly, and maybe it should be
-}
TM-start-state : {n m : Nat} → TM (suc n) m → List (Fin m) → TM-state (suc n) m
TM-start-state tm tape =
  record {
    state = zero ;
    tape = tape ;
    pos = 0 ;
    halted = false
  }






{-
  This runs a TM for a given # of steps on an input tape to get a resulting TM-state
  1 + n = # of states
  m = # of symbols

  Inputs:
   * # of steps to run       : Nat
   * Turing machine          : TM (1 + n) m
 
  Outputs:
   * resulting TM-state      : TM-state (1 + n) m
-}
TM-run : {n m : Nat} → Nat → TM (suc n) m → List (Fin m) → TM-state (suc n) m
TM-run steps M tape = fold (TM-start-state M tape) (TM-step-state M) steps





{-
  This represents the input (state , symbol) pair,
  and resulting instructions (new-state , write-symbol , move left/right) triple for an individual transition.
  n = # of states
  m = # of symbols

   * current state          : Fin n
   * symbol read            : Fin m
   * next state             : Fin n
   * symbol to write        : Fin m
   * move left/right        : Bool

  NOTE:
   * this is so that the TM can be represented as a List of transitions rather than as a function
     to make them somewhat easier to analyze and manipulate
-}
data TM-δ (n m : Nat) : Set where
  δ : Fin n → Fin m → Fin n → Fin m → Bool → TM-δ n m





{-
  This extracts the TM-δ transition from a TM for a given (state , symbol) input pair, or `nothing` if there is
  no transition for that input

  n = # of states
  m = # of symbols

  Inputs:
   * Turing machine transition function    : TM n m
   * state                                 : Fin n
   * symbol                                : Fin m

  Outputs:
   * the transition table row              : TM-δ n m
  OR
   * `nothing`, if no transition exists
-}
TM-get-δ : {n m : Nat} → TM n m → Fin n → Fin m → Maybe (TM-δ n m)
TM-get-δ {n} {m} M x y = Maybe-map extract (M (x , y))
  where
    extract : (Fin n) × ((Fin m) × Bool) → TM-δ n m
    extract (x' , (y' , d)) = δ x y x' y' d




{-
  This extracts a full TM transition from a TM transition function
  1 + n = # of states
  1 + m = # of symbols

  Input:
   * transition function        : TM (1 + n) (1 + m)

  Output:
   * transition table           : List (TM-δ (1 + n) (1 + m))
-}
TM-to-table : {n m : Nat} → TM (suc n) (suc m) → List (TM-δ (suc n) (suc m))
TM-to-table {n} {m} M = 
  flatten (
    Fin-map-list (λ x → 
      Fin-filter (λ y →
        TM-get-δ M x y
      ) (fromℕ m)
    ) (fromℕ n)
  )




{-
  This extracts the TM-transition instruction from a transition table row

  Input:
   * transition table row       : TM-δ n m
  
  Output:
   * transition instructions    : TM-transition n m
-}
TM-run-table-δ : {n m : Nat} → TM-δ n m → TM-transition n m
TM-run-table-δ (δ x y x' y' d) = x' , (y' , d)






{-
  This translates a TM transition function from a transition table
  1 + n = # of states
  1 + m = # of symbols

  Input :
   * transition table            : List (TM-δ (1 + n) (1 + m))

  Output: 
   * transition function         : TM (1 + n) (1 + m)
-}
TM-from-table : {n m : Nat} → List (TM-δ (suc n) (suc m)) → TM (suc n) (suc m)
TM-from-table {n} {m} table (x , y) = Maybe-map TM-run-table-δ (find match-input table)
  where
    match-input : TM-δ (suc n) (suc m) → Bool
    match-input (δ x' y' _ _ _) = eq-∧ (eq-Fin {suc n}) (eq-Fin {suc m}) (x , y) (x' , y')




TM-raise-action : {n m : Nat} → (n' : Nat) → TM-action n m → TM-action (n' + n) m
TM-raise-action n' nothing = nothing
TM-raise-action n' (just (q , (s , b))) = just (raise n' q , (s , b))



{-
  This translates an n-state, m-symbol TM to an equivalent (n' + n)-state , m-symbol TM.
  It essentially runs on the first n states.

  Input:
   * # of states to add           : Nat
   * original TM                  : TM n m

  Outputs:
   * TM with new states added     : TM (n' + n) m

  TODO:
   * prove equivalence
-}
TM-raise : {n m : Nat} → (n' : Nat) → TM n m → TM (n' + n) m
TM-raise {n} {m} n' M (q , s) = 
  dite'
    ((toℕ q) lt n)
    (λ case-true →
      TM-raise-action n' (M (fromℕ< (lt→< case-true) , s))
    )
    (λ _ → nothing)




{-
  This translates an n-state, m-symbol TM to an equivalent (n' + n)-state , m-symbol TM.
  It runs on the last n' states.

  Input:
   * # of states to add           : Nat
   * original TM                  : TM n m

  Outputs:
   * TM with new states added     : TM (n' + n) m


  EXPLANATION:
  adding 0 states to a TM:
   * the new TM is identical to the first, just run the first directly on any input

  adding 1+n' states to a 0-state TM:
   * none of the states in the new TM correspond to states in the original TM; the semantics
     of any state will be to halt immediately on any input

  adding 1+n' states to a 1+n-state TM:
   * if the state s is less than n', this doesn't correspond to any state of the original TM,
     the semantics will be to halt immediately.
   * if the state s is greater or equal to n', this corresponds to the state (s - n') of the original TM
     run the original TM on the state (s - n')

  TODO:
   * clean up annoying Fin arithmetic
   * unify the 2 cases for adding 1+n' states
   * prove equivalence
-}
TM-raise+ : {n m : Nat} → (n' : Nat) → TM n m → TM (n' + n) m
TM-raise+ {n}     {m} 0        M (q , s) = M (q , s)
TM-raise+ {0}     {m} (suc n') M (q , s) = nothing
TM-raise+ {suc n} {m} (suc n') M (q , s) = output
  where
    qₙ' : (Fin (((1 + n') + (1 + n)) - (1 + n')))
    qₙ' = Fin-sub q (1 + n') (m<m+1+n (1 + n') n)

    qₙ : Fin (1 + n)
    qₙ = coerce (cong (λ x → Fin x) (x+y-x=y (1 + n') (1 + n))) qₙ'
    
    M-out : TM-action (1 + n) m
    M-out = M (qₙ , s)
    
    get-results : TM-action (1 + n) m → TM-action ((1 + n') + (1 + n)) m
    get-results nothing = nothing
    get-results (just (q' , (s' , d))) = just ((raise (suc n') q') , (s' , d))
    
    output = get-results M-out



{-
  This takes two TMs and produces a TM that's equivalent to running them in sequence
  
  Inputs:
   * n-state , m-symbol TM              : TM n m
   * 1+n'-state , m-symbol TM           : TM (1 + n') m

  Output:
   * (1+n')+n-state , m-symbol TM       : TM ((1 + n') + n) m

  NOTE:
   * This isn't equivalent to the partial-function composition M₂ ∘ M₁ , because
     it doesn't shift back to the beginning of the tape after M₁ finishes, it just
     shifts one cell right and starts running M₂.
   * This can perhaps be used as a primitive in constructing partial-function composition.

  TODO:
   * prove these specifications on the behavior
-}
seq : {n n' m : Nat} → (M₁ : TM n m) → (M₂ : TM (1 + n') m) → TM ((1 + n') + n) m
seq {n} {n'} {m} M₁ M₂ = M₁,₂
  where
    {-
      Raise M₁ and M₂ to machines with (1 + n' + n) states.
    -}
    fix-M₁ : TM (1 + n' + n) m
    fix-M₁ = TM-raise (1 + n') M₁

    fix-M₂ : TM (1 + n' + n) m
    fix-M₂ = coerce (cong (λ x → TM x m) (+-comm n (1 + n'))) (TM-raise+ n M₂)

    {-
      If the action of M₁ would have been to halt, then the action of M₂∘M₁ will be to
      set the state to n (equivalent to state 0 of M₂), leave the tape symbol unchanged, and move right,
      otherwise just do the normal action of M₁.
    -}
    switch : Fin m → TM-action (1 + n' + n) m → TM-transition (1 + n' + n) m
    switch s nothing = (fromℕ< (m<1+n+m n n')) , (s , true)
    switch s (just transition) = transition

    {-
      If the state q is less than n, then do the action M₁ (with the appropriate `switch` if the action
      would have been to halt), otherwise do the action of M₂.
    -}
    M₁,₂ : TM (1 + n' + n) m
    M₁,₂ (q , s) =
      if (Fin-lt q n) then
        just (switch s (fix-M₁ (q , s)))
      else
        fix-M₂ (q , s)
