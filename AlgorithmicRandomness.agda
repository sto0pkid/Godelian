module AlgorithmicRandomness where

open import Basic
open import TuringMachine3 using (TM ; TM-state ; TM-run)
open import Util.List

{-
  This isn't an adequate definition because the sequence S is already definitionally computable.
  Can that be proved within Agda though, for arbitrary S?
-}
algorithmically-nonrandom1 : (ℕ → Fin 2) → Set
algorithmically-nonrandom1 S =
  Σ[ n ∈ ℕ ] (
    Σ[ M ∈ TM (suc n) 2 ] (
      Σ[ tape ∈ List (Fin 2) ] (
        (k : ℕ) →
        Σ[ m ∈ ℕ ] (
          (k' : ℕ) →
          k' > k →
          matches S (TM-state.tape (TM-run k' M tape))
        )
      )
    )
  )
  where
    matches : (ℕ → Fin 2) → List (Fin 2) → Set
    matches f l = (x : ℕ) → (x<|l| : x < length l) → lookup< l x x<|l| ≡ f x

algorithmically-random1 : (ℕ → Fin 2) → Set
algorithmically-random1 S = ¬ (algorithmically-nonrandom1 S)



{-
  This should capture the definition.
  Instead of using a sequence defined by an explicit function ℕ → Fin 2,
  we use a sequence defined by a proposition.

  Now we should actually be able to define an algorithmically random sequence and prove it.
-}
algorithmically-nonrandom2 : (S : ℕ → Fin 2 → Set) → Functional S → Set
algorithmically-nonrandom2 S S-functional =
  Σ[ n ∈ ℕ ] (
    Σ[ M ∈ TM (suc n) 2 ] (
      Σ[ tape ∈ List (Fin 2) ] (
        (k : ℕ) →
        Σ[ m ∈ ℕ ] (
          (k' : ℕ) →
          k' > k →
          matches S (TM-state.tape (TM-run k' M tape))
        )
      )
    )
  )
  where
    matches : (ℕ → Fin 2 → Set) → List (Fin 2) → Set
    matches s l = (x : ℕ) → (x<|l| : x < length l) → s x (lookup< l x x<|l|)

algorithmically-random2 : (S : ℕ → Fin 2 → Set) → Functional S → Set
algorithmically-random2 S S-functional = ¬ (algorithmically-nonrandom2 S S-functional)

{-
TODO: prove an algorithmically random sequence using this definition
-}
