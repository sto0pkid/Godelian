module Combinators where

open import Basic hiding ([_])

data Bin (A : Set) : Set where
  _∙_ : Bin A → Bin A → Bin A
  [_] : A → Bin A

{-
  this ensures the combinators are appropriately defined
  Fin n represents the arguments to the combinator, rather than the carrier set
    from which those arguments are taken
  Bin (Fin n) represents the possible (bin-)trees you can construct from just the
  arguments, i.e. the combinators restrict you to the following operations on the arguments
    * rearrange
    * repeat
    * remove
    * regroup
-}
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

{-
Combinatory completeness:
* remove any unused arguments
* repeat the remaining arguments as many times as they are used in the result
* rearrange the arguments into their proper order
* regroup them into their proper tree structure
-}
