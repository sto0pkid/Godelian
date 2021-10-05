module FOL.Example3 where

open import Basic
open import FOL

ϕ₃ : FOL 1
ϕ₃ = 0 R 0
  where
    _R_ : ℕ → ℕ → FOL 1
    x R y = rel zero (c x) (c y)

ϕ₃-preinterpretation : PreInterpretation {1}
ϕ₃-preinterpretation = record {
    A = ℕ ;
    objs = id ;
    rels = (λ _ → (λ x y → x ≡ y))
  }

ϕ₃-model : model ϕ₃ ϕ₃-preinterpretation
ϕ₃-model = refl
