module Determinism where

open import Basic hiding (_^_) renaming (func-rep to _^_)
open import Util.BoolProp


{-
This is probably an inadequate definition of determinism because any ℕ → Instant you provide already predetermines the entire history.

This isn't really a definition of "determinism" it's a definition of an instance of discrete-time dynamical systems

Other problems:
* ℕ as the index on instants in the history
* What about other notions of time? In special relativity there is no globally well-defined ordering of events
-}

deterministic1 : (Instant : Set) → (history : ℕ → Instant) → Set
deterministic1 Instant history =
  Σ[ f ∈ (Instant → Instant) ] (
    (n : ℕ) →
    history n ≡ (f ^ n) (history 0)
  )




deterministic2 : (Instant : Set) → (history : ℕ → Instant → Set) → Set
deterministic2 Instant history =
  Functional history ×
  Σ[ start ∈ Instant ] (
    (history 0 start) × 
    Σ[ f ∈ (Instant → Instant) ] (
      (n : ℕ) →
      history n ((f ^ n) start)
    )
  )

deterministic2→total :
  (Instant : Set) →
  (history : ℕ → Instant → Set) →
  deterministic2 Instant history →
  Total history
deterministic2→total Instant history (history-functional , (start , (H-0-start , (f , evolution)))) n = ((f ^ n) start) , (evolution n)

{-
 This is actually false; deterministic2 requires that any configuration uniquely determines the next configuration,
 by a function which can compute the latter from the former,
 only based on the information contained in the configuration.

 total-functional doesn't require this and doesn't impose any constraints on how successive configurations might relate to each other.
-}

{-
total-functional→deterministic2 :
  (Instant : Set)
  (history : ℕ → Instant → Set) →
  Total history →
  Functional history →
  deterministic2 Instant history
total-functional→deterministic2 Instant history history-total history-functional = history-functional , (start , (H-0-start , (f , evolution)))
  where
    start = proj₁ (history-total 0)
    H-0-start = proj₂ (history-total 0)
    f 
    evolution
-}

{-
  Instead of expressing the state transitions as a function, which is necessarily deterministic,
  specify the state transition as a relation between possible adjacent states. This way at any given
  moment there can be multiple possible futures. A "history" is then a sequence of states each representing
  a single choice from these possibilities.

  Note that the set of possible transitions from any given state is purely a function of that State, and not
  ex.. previous history, etc.. This is probably not a limitation though because States could be defined such
  that they encode the relevant information from the history, or any other info, if necessary.
-}

deterministic3 : {State : Set} → (δ : State → State → Set) → Set
deterministic3 δ = Functional δ

nondeterministic3 : {State : Set} → (δ : State → State → Set) → Set
nondeterministic3 δ = ¬ (deterministic3 δ)

history3 : {State : Set} → (δ : State → State → Set) → Set
history3 {State} δ = Σ[ f ∈ (ℕ → State) ] ((x : ℕ) → δ (f x) (f (1 + x)))

coin-flip-world : Bool → Bool → Set
coin-flip-world _ _ = ⊤

coin-flip-world-nondeterministic : nondeterministic3 coin-flip-world
coin-flip-world-nondeterministic δ-functional = contradiction
  where
    {-
      the 'true' state can be followed by either the 'true' state or the 'false' state
      if δ was deterministic, i.e. if δ was functional, then true = false; contradiction.
      therefore the coin-flip world is nondeterministic
    -}
    true≡false : true ≡ false
    true≡false = δ-functional true true false unit unit
    
    contradiction = true≠false true≡false

{-
TODO:
* causality
* randomness
* information
* indeterminism
* locality
* realism
* materialism
-}
