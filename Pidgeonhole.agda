module Pidgeonhole where

open import Basic hiding (Σ)
open import Util.Arithmetic
open import Util.Vec renaming (Vec-sum to Σ ; Vec-any to ∃ ; Vec-any-monotonic to ∃-monotonic)


{-
The pidgeonhole principle.

If n > m, and you put n objects in m boxes, then some box will contain more than 1 object.

Here restated in terms of arithmetic:

If n > m, and you have a vector v, where |v|=m and Σv=n, then for some i < m, v[i]>1.

There are no cases when m or n = 0.

If m, n ≠ 0 then this will return the first index i such that v[i] > 1


-}
-- would be nice if builtin Nats let you pattern-match on (1+n) for (suc n), (2+n) for (suc (suc n)) etc...
pidgeonhole : (m n : ℕ) → m < n → (v : Vec ℕ m) → n ≡ (Σ v) → ∃ v (λ x → x > 1)
pidgeonhole m 0 ()
pidgeonhole 0 (suc n) _ [] ()
pidgeonhole 1 (suc n) 1<sn (x ∷ []) sn=x = zero , x>1
  where
    x>1 = resp (λ x → x > 1) (≡-trans sn=x (+-identityʳ x)) 1<sn
    
pidgeonhole (suc (suc m)) (suc n) sn>ssm (0 ∷ xs) sn=Σxs = ∃-monotonic (λ x → x > 1) (pidgeonhole (suc m) (suc n) sn>sm xs sn=Σxs) 0
  where
    sn>sm = x>sy→x>y sn>ssm
    
pidgeonhole (suc (suc m)) (suc n) sn>ssm (1 ∷ xs) sn=Σv = proof
  where
    n=Σxs : n ≡ Σ xs
    n=Σxs = cong pred sn=Σv

    n>sm : n > (suc m)
    n>sm = sx>sy→x>y sn>ssm

    proof = ∃-monotonic (λ x → x > 1) (pidgeonhole (suc m) n n>sm xs n=Σxs) 1

pidgeonhole (suc (suc m)) (suc n) _ ((suc (suc k)) ∷ xs) _ = zero , (s≤s (s≤s z≤n))
