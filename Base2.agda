module Base2 where

open import Basic
open import Util.Bool
open import Util.BoolCircuit

-- output: sum , carry
base2+₁ : Bool → Bool → Bool × Bool
base2+₁ x y = (x xor y) , (x and y)

-- output: sum , carry
base2+carry : Bool → Bool → Bool → Bool × Bool
base2+carry x y c = (parity (x ∷ (y ∷ (c ∷ [])))) , (threshold 2 (x ∷ (y ∷ (c ∷ []))))


base2-suc-helper2 : (List Bool) × Bool → Bool × Bool → (List Bool) × Bool
base2-suc-helper2 p q = (current_sum ∷ current_list) , new_carry
  where
    current_list = proj₁ p
    current_sum = proj₁ q
    new_carry = proj₂ q


base2-suc-helper : List Bool → (List Bool) × Bool
base2-suc-helper [] = [] , false
base2-suc-helper (x ∷ []) = (s ∷ []) , c
  where
    p = base2+carry x true false
    s = proj₁ p
    c = proj₂ p
base2-suc-helper (x ∷ (y ∷ xs)) =
  base2-suc-helper2
    (base2-suc-helper (y ∷ xs))
    (base2+carry x false (proj₂ (base2-suc-helper (y ∷ xs))))

base2-suc : List Bool → List Bool
base2-suc [] = []
base2-suc (x ∷ xs) = if c then (true ∷ l) else l
  where
    p = base2-suc-helper (x ∷ xs)
    l = proj₁ p
    c = proj₂ p

unary→base2 : ℕ → List Bool
unary→base2 0 = (false ∷ [])
unary→base2 (suc n) = base2-suc (unary→base2 n)

base2→unary : List Bool → ℕ
base2→unary [] = 0
base2→unary (false ∷ xs) = base2→unary xs
base2→unary (true ∷ xs) = (2 ^ (length xs)) + (base2→unary xs)
