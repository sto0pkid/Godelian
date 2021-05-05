module MuRecursive where

open import Basic hiding ([_] ; map ; foldr) renaming (Vec-get to _[_])
open import Data.Vec using (map ; zip ; foldr)

data μR : ℕ → Set where
  zero : μR 1
  succ : μR 1
  proj : (n : ℕ) → Fin n → μR n
  comp : {n k : ℕ} → μR k → Vec (μR n) k → μR n
  prim-rec : {n : ℕ} → μR n → μR (2 + n) → μR (1 + n)
  μ-rec : {k : ℕ} → μR (1 + k) → μR k


-- how to fix to make it pass the termination checker?
{-# NON_TERMINATING #-}
μR-interp : {n : ℕ} → μR n → Vec ℕ n → ℕ → Set
μR-interp zero _ y = y ≡ 0
μR-interp succ (x ∷ []) y = y ≡ (1 + x)
μR-interp (proj n i) xs y = y ≡ xs [ i ]
μR-interp (comp {n} {k} f gs) xs y =
  Σ[ v ∈ Vec ℕ k ] (
    (foldr (λ _ → Set) _×_ ⊤ (map (λ (g , w) → (μR-interp g xs w)) (zip gs v)))
    × (μR-interp f v y)
  )
μR-interp (prim-rec f g) (0 ∷ xs) y = μR-interp f xs y
μR-interp (prim-rec f g) ((suc n) ∷ xs) y =
  Σ ℕ (λ r →
    (μR-interp (prim-rec f g) (n ∷ xs) r)
    × (μR-interp g (n ∷ r ∷ xs) y)
  )
μR-interp (μ-rec f) xs y = min-Nat (λ n → μR-interp f (y ∷ xs) 0) y
