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


μR-interp : {n : ℕ} → μR n → Vec ℕ n → ℕ → Set
μR-interp zero _ y = y ≡ 0
μR-interp succ (x ∷ []) y = y ≡ (1 + x)
μR-interp (proj n i) xs y = y ≡ xs [ i ]
μR-interp (comp {n} {k} f gs) xs y = Σ[ v ∈ Vec ℕ k ] ((fold' gs v) × (μR-interp f v y))
  where
    fold' : {k' : ℕ} → Vec (μR n) k' → Vec ℕ k' → Set
    fold' [] [] = ⊤
    fold' (g' ∷ gs') (y' ∷ ys') = (μR-interp g' xs y') × (fold' gs' ys')
μR-interp (prim-rec f g) (0 ∷ xs) y = μR-interp f xs y
μR-interp (prim-rec f g) ((suc n) ∷ xs) y =
  Σ[ r ∈ ℕ ] (
      (μR-interp (prim-rec f g) (n ∷ xs) r)
    × (μR-interp g (n ∷ r ∷ xs) y)
  )
μR-interp (μ-rec f) xs y = min-Nat (λ n → μR-interp f (y ∷ xs) 0) y
