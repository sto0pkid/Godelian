module MuRecursive where

open import Basic hiding ([_]) renaming (Vec-get to _[_])
open import Data.Vec using (head)
open import PR

-- The "mu" is for all the mutual recursion I needed to make the definitions and proofs pass termination check...


{-
  AST data structure for μ-recursive functions
-}
data μR : ℕ → Set where
  zero : μR 1
  succ : μR 1
  proj : (n : ℕ) → Fin n → μR n
  comp : {n k : ℕ} → μR k → Vec (μR n) k → μR n
  prim-rec : {n : ℕ} → μR n → μR (2 + n) → μR (1 + n)
  μ-rec : {k : ℕ} → μR (1 + k) → μR k


μ : {k : ℕ} → μR (1 + k) → μR k
μ = μ-rec



{-
 Interpretation of arity-n μ-recursive functions as an input/output relations R ⊆ ℕ^(n+1)

 FIXME: can we abstract out the mutual recursive part for clarity?
-}


_[_]=_ : {n : ℕ} → μR n → Vec ℕ n → ℕ → Set


fold[_,_]=_ : {n k : ℕ} → Vec (μR n) k → Vec ℕ n → Vec ℕ k → Set
fold[ [] , _ ]= [] = ⊤
fold[ (g ∷ gs) , xs ]= (y ∷ ys) = (g [ xs ]= y) × (fold[ gs , xs ]= ys)

zero                [ _              ]= y = y ≡ 0
succ                [ xs             ]= y = y ≡ (1 + (head xs))
(proj n i)          [ xs             ]= y = y ≡ xs [ i ]
(comp {n} {k} f gs) [ xs             ]= y = Σ[ v ∈ Vec ℕ k ] ((fold[ gs , xs ]= v) × (f [ v ]= y))
(prim-rec f g)      [ (0 ∷ xs)       ]= y = f [ xs ]= y
(prim-rec f g)      [ ((suc n) ∷ xs) ]= y = Σ[ r ∈ ℕ ] (
                                                   ((prim-rec f g) [ (n ∷ xs)           ]= r)
                                                 × (g              [ ((1 + n) ∷ r ∷ xs) ]= y)
                                            )
(μ-rec f)           [ xs             ]= y = min-Nat (λ n → f [ (n ∷ xs)]= 0) y

μR-interp : {n : ℕ } → μR n → Vec ℕ n → ℕ → Set
μR-interp = _[_]=_
