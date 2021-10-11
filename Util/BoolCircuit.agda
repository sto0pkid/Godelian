module Util.BoolCircuit where

open import Basic
open import Util.Arithmetic


Bool→Nat : Bool → ℕ
Bool→Nat false = 0
Bool→Nat true = 1

mod2 : ℕ → Bool
mod2 0 = false
mod2 (suc n) = not (mod2 n) 

parity : List Bool → Bool
parity [] = false
parity (false ∷ xs) = parity xs
parity (true ∷ xs) = not (parity xs)

threshold : ℕ → List Bool → Bool
threshold n l = (sum (map Bool→Nat l)) ge n

base-n→unary : {n : ℕ} → List (Fin n) → ℕ
base-n→unary {0} [] = 0
base-n→unary {1} [] = 0
base-n→unary {1} (x ∷ xs) = suc (base-n→unary {1} xs)
base-n→unary {(suc (suc n))} [] = 0
base-n→unary {(suc (suc n))} (x ∷ xs) = (x' * (base ^ (length xs))) + (base-n→unary xs)  
  where
    x' = toℕ x
    base = (suc (suc n))


inc-rev : List Bool → List Bool
inc-rev [] = true ∷ []
inc-rev (false ∷ as) = true ∷ as
inc-rev (true ∷ as) = false ∷ (inc-rev as)


ℕ→Binary : ℕ → List Bool
ℕ→Binary 0 = false ∷ []
ℕ→Binary (suc n) = reverse (inc-rev (reverse (ℕ→Binary n)))
