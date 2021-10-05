module FOL.Example1 where

open import Basic
open import FOL

ϕ₁ : FOL 1
ϕ₁ = (0 R 1) & (1 R 2)
  where
    _R_ : ℕ → ℕ → FOL 1
    x R y = rel zero (c x) (c y)

ϕ₁-preinterpretation : PreInterpretation {1}
ϕ₁-preinterpretation = record {
    A = ℕ ;
    objs = id ;
    rels = (λ R → (λ x y → (suc x) ≡ y))
  }

ϕ₁-model : model ϕ₁ ϕ₁-preinterpretation
ϕ₁-model = proof
  where
    proof : ((suc 0) ≡ 1) × ((suc 1) ≡ 2)
    proof = refl , refl
