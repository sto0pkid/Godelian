module Combinators where

open import Basic hiding ([_])

data Bin (A : Set) : Set where
  _∙_ : Bin A → Bin A → Bin A
  [_] : A → Bin A

-- this ensures the combinators are appropriately defined
Combinator : ℕ → Set
Combinator n = Bin (Fin n)

I : Combinator 1
I = [ x ]
  where
    x = zero

K : Combinator 2
K = [ x ]
  where
    x = zero

S : Combinator 3
S = ([ x ] ∙ [ z ]) ∙ ([ y ] ∙ [ z ])
  where
    x = zero
    y = suc zero
    z = suc (suc zero)

B : Combinator 3
B = [ x ] ∙ ([ y ] ∙ [ z ])
  where
    x = zero
    y = suc zero
    z = suc (suc zero)

C : Combinator 3
C = ([ x ] ∙ [ z ]) ∙ [ y ]
  where
    x = zero
    y = suc zero
    z = suc (suc zero)

W : Combinator 2
W = ([ x ] ∙ [ y ]) ∙ [ y ]
  where
    x = zero
    y = suc zero
  
