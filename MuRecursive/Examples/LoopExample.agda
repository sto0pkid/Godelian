module MuRecursive.Examples.LoopExample where

open import Basic
open import Data.Vec using (head)
open import MuRecursive
open import MuRecursive.Properties
open import PR

{-
 Simple 0-ary μ-recursive function that loops on its (empty) input

-}
μR-loop-example : μR 0
μR-loop-example = μ-rec (comp succ (proj 1 zero ∷ []))

μR-loop-example-loops : ¬ (μR-Halting μR-loop-example [])
μR-loop-example-loops (y , μf[]≡y) = contradiction
  where
    μf = μR-loop-example

    f : μR 1
    f = comp succ (proj 1 zero ∷ [])

    f[y]≡0 : Σ[ v ∈ Vec ℕ 1 ] ((fold[ (proj 1 zero ∷ []) , (y ∷ []) ]= v) × (succ [ v ]= 0))
    f[y]≡0 = proj₁ μf[]≡y

    v : Vec ℕ 1
    v = proj₁ f[y]≡0

    succ[v]≡0 : succ [ v ]= 0
    succ[v]≡0 = proj₂ (proj₂ f[y]≡0)

    0≡1+h[v] : 0 ≡ 1 + (head v)
    0≡1+h[v] = succ[v]≡0

    contradiction = 1+n≢0 (≡-sym 0≡1+h[v])

{-
  The looping μ-recursive function is not primitive recursive
-}
μR-loop-example-not-PR : ¬ (Is-semantically-PR μR-loop-example)
μR-loop-example-not-PR (f , λx→P[x]≡f[x]) = proof
  where
    P[]≡f[] : μR-loop-example [ [] ]= (PR-interp f [])
    P[]≡f[] = λx→P[x]≡f[x] []

    proof = μR-loop-example-loops (PR-interp f [] , P[]≡f[])
