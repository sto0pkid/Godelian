module HaltingProblemGameTheory where

open import Basic

{-
  Inputs:
   * player 1's choice
   * player 2's choice
  
  Outputs:
   * winner; false for player 1, true for player 2
-}

game : Bool → Bool → Bool
game x y = x xor y

{-
  Player 2 can always win
-}
player2-wins : (player1-choice : Bool) → Σ[ player2-choice ∈ Bool ] (game player1-choice player2-choice ≡ true)
player2-wins true = false , refl
player2-wins false = true , refl

{-
  This proves the undecidability of the halting problem for Turing machines;
  * the halting decider H is player 1
  * the diagonalization gadget K is player 2
  Works for any property of the partial function defining the I/O behavior of the machine. If you have one machine
  that satisfies the property, and another machine that doesn't, then you can make K choose to do one or the other
  depending on what H decides.

  K always wins, H is always wrong.

  Note that by another interpretation, H is always right but in a language where the meaning of the terms is changed.
  The label "false" now indicates that K will halt, and "true" now indicates that K will loop.
-}
