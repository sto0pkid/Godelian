module SKI where

open import Basic hiding ([_])

data Bin (A : Set) : Set where
  _∙_ : Bin A → Bin A → Bin A
  [_] : A → Bin A


data SKI : Set where
  S : SKI
  K : SKI
  I : SKI
  v : ℕ → SKI


data SKIExpr₁ : Set where
  node : List SKIExpr₁ → SKIExpr₁
  [_] : SKI → SKIExpr₁

SKIExpr : Set
SKIExpr = List SKIExpr₁

I-func : SKIExpr → SKIExpr
I-func [] = ([ I ] ∷ [])
I-func (x ∷ xs) = (x ∷ xs)

K-func : SKIExpr → SKIExpr
K-func [] = ([ K ] ∷ [])
K-func (x ∷ []) = ([ K ] ∷ x ∷ [])
K-func (x ∷ y ∷ xs) = (x ∷ xs)

S-func : SKIExpr → SKIExpr
S-func [] = ([ S ] ∷ [])
S-func (x ∷ []) = ([ S ] ∷ x ∷ [])
S-func (x ∷ y ∷ []) = ([ S ] ∷ x ∷ y ∷ [])
S-func (x ∷ y ∷ z ∷ xs) = (x ∷ z ∷ (node (y ∷ z ∷ [])) ∷ xs)

SKI-interp : SKIExpr → SKIExpr
SKI-interp [] = []
SKI-interp e@([ v n ] ∷ xs) = e
SKI-interp ([ I ] ∷ xs) = I-func xs
SKI-interp ([ K ] ∷ xs) = K-func xs
SKI-interp ([ S ] ∷ xs) = S-func xs
SKI-interp ((node []) ∷ xs) = xs
SKI-interp ((node (x ∷ [])) ∷ xs) = x ∷ xs
SKI-interp ((node head@(x ∷ y ∷ ys)) ∷ xs) = (node (SKI-interp head)) ∷ xs
