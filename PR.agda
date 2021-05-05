module PR where

open import Basic hiding ([_] ; map) renaming (Vec-get to _[_])
open import Data.Vec using (map)

data PR : ℕ → Set where
  zero : PR 1
  succ : PR 1
  proj : (n : ℕ) → Fin n → PR n
  comp : {n k : ℕ} → PR k → Vec (PR n) k → PR n
  prim-rec : {n : ℕ} → PR n → PR (2 + n) → PR (1 + n)


PR-interp : {n : ℕ} → PR n → Vec ℕ n → ℕ
PR-interp zero (x ∷ []) = 0
PR-interp succ (x ∷ []) = suc x
PR-interp (proj n i) xs = xs [ i ]
PR-interp (comp f gs) xs = PR-interp f (map' gs xs)
  where
    map' : {n k : ℕ } → Vec (PR n) k → Vec ℕ n → Vec ℕ k
    map' [] ys = []
    map' (g ∷ gs') ys = (PR-interp g ys) ∷ (map' gs' ys)
PR-interp (prim-rec f g) (0 ∷ xs) = PR-interp f xs
PR-interp (prim-rec f g) ((suc n) ∷ xs) = PR-interp g (n ∷ (PR-interp (prim-rec f g) (n ∷ xs)) ∷ xs)
