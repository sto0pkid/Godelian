module MuRecursive.Examples.HaltExample where

open import Basic
open import MuRecursive

{-
  Simple 0-ary μ-recursive function that halts on its (empty) input
-}
μR-halt-example : μR 0
μR-halt-example = μ-rec zero


μR-halt-example-halts : μR-halt-example [ [] ]= 0
μR-halt-example-halts = refl , (λ _ _ → z≤n)

