module MuRecursive.Examples.LoopExample2 where

open import Basic
open import MuRecursive
open import MuRecursive.Properties

{-
  Simple 2-ary μ-recursive function that loops on every input
-}
μR-loop-example2 : μR 2
μR-loop-example2 = μ-rec (comp succ (proj 3 zero ∷ []))

μR-loop-example2-loops :  (x : Vec ℕ 2) → ¬ (μR-Halting μR-loop-example2 x)
μR-loop-example2-loops x@(x₁ ∷ x₂ ∷ []) (y , f[x]≡y) = 0≢succ-v {proj₁ (proj₁ f[x]≡y)} (proj₂ (proj₂ (proj₁ f[x]≡y)))
