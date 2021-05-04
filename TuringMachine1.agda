module TuringMachine1 where

open import Basic

record TuringMachine : Set₁ where
  field
    Q : Set
    Q-finite : Finite Q
    Γ : Set
    Γ-finite : Finite Γ
    b : Γ -- covers the non-empty criteria for Γ
    S : Γ → Set
    S-no-b : ¬ (S b)
    q₀ : Q -- covers the non-empty criteria for Q
    F : Q → Set
    δ : Q × Γ → Q × (Γ × Bool)
