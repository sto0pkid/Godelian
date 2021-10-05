module FOL.Example2 where

open import Basic hiding (all)
open import FOL

ϕ₂ : FOL 1
ϕ₂ = all (v 0) (exists (v 1) (rel zero (v (v 0)) (v (v 1))))


ϕ₂-preinterpretation : PreInterpretation {1}
ϕ₂-preinterpretation = record {
    A = ℕ ;
    objs = id ;
    rels = (λ R → (λ x y → (suc x) ≡ y))
  }

ϕ₂-model : model ϕ₂ ϕ₂-preinterpretation
ϕ₂-model = proof
  where
    proof : (x : ℕ) → Σ[ y ∈ ℕ ] (suc x ≡ y)
    proof x = (suc x) , refl
