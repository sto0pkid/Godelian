module Combinators where

open import Basic hiding ([_] ; _^_) renaming (func-rep to _^_)
open import Util.Arithmetic
open import Util.DependentIf
open import Util.Vec

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

{-
  This has the advantage that you can consider all the combinators in a single set regardless
  of arity.
-}
Combinator' : Set
Combinator' = Σ[ n ∈ ℕ ] (Bin (Fin n))

Combinator→Combinator' : {n : ℕ} → Combinator n → Combinator'
Combinator→Combinator' {n} c = n , c

Combinator'→Combinator : (c : Combinator') → Combinator (proj₁ c)
Combinator'→Combinator (n , c) = c



I-def : Combinator 1
I-def = [ x ]
  where
    x = zero

K-def : Combinator 2
K-def = [ x ]
  where
    x = zero

S-def : Combinator 3
S-def = ([ x ] ∙ [ z ]) ∙ ([ y ] ∙ [ z ])
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




rspine : {A : Set} → Bin A → List (Bin A)
rspine ([ x ]) = ([ x ]) ∷ []
rspine (l ∙ r) = l ∷ (rspine r)

lspine : {A : Set} → Bin A → List (Bin A)
lspine ([ x ]) = ([ x ]) ∷ []
lspine (l ∙ r) = (lspine l) ++ (r ∷ [])

un-lspine-helper : {A : Set} → (l : List (Bin A)) → Bin A → Bin A
un-lspine-helper [] acc = acc
un-lspine-helper (l ∷ r) acc = un-lspine-helper r (acc ∙ l)

un-lspine : {A : Set} → (l : List (Bin A)) → {l ≢ []} → Bin A
un-lspine ([]) {l≢[]} = ⊥-elim (l≢[] refl)
un-lspine (l ∷ r) = un-lspine-helper r l

un-rspine : {A : Set} → (l : List (Bin A)) → {l ≢ []} → Bin A
un-rspine ([]) {l≢[]} = ⊥-elim (l≢[] refl)
un-rspine (x ∷ []) = x
un-rspine (l ∷ r ∷ rs) = l ∙ (un-rspine (r ∷ rs) {λ ()})

ex : Bin ℕ
ex = ([ 0 ] ∙ [ 1 ]) ∙ ([ 2 ] ∙ [ 3 ])


subst : {n : ℕ} {A : Set} → Combinator n → (Fin n → A) → Bin A
subst [ x ] f = [ f x ]
subst (l ∙ r) f = (subst l f) ∙ (subst r f)

subs-ex : Fin 3 → ℕ
subs-ex zero = 17
subs-ex (suc zero) = 18
subs-ex (suc (suc zero)) = 19

subst' : {A : Set} → (c : Combinator') → (Fin (proj₁ c) → A) → Bin A
subst' (n , c) f = subst c f

Bin-flat : {A : Set} → Bin (Bin A) → Bin A
Bin-flat ([ x ]) = x
Bin-flat (l ∙ r) = (Bin-flat l) ∙ (Bin-flat r)

data SKI : Set where
  v : ℕ → SKI
  S : SKI
  K : SKI
  I : SKI

interp : SKI → Maybe Combinator'
interp (v _) = nothing
interp S = just (Combinator→Combinator' S-def)
interp K = just (Combinator→Combinator' K-def)
interp I = just (Combinator→Combinator' I-def)

is-just-lemma : {A : Set} → (m : Maybe A) → is-just m ≡ true → Σ[ a ∈ A ] (m ≡ just a)
is-just-lemma nothing ()
is-just-lemma (just x) refl = x , refl

is-just-get : {A : Set} → (m : Maybe A) → is-just m ≡ true → A
is-just-get nothing ()
is-just-get (just x) refl = x

grab-n-vec : {A : Set} (n : ℕ) → (l : List A) → n ≤ (length l) → Vec A n
grab-n-vec 0 _ _ = []
grab-n-vec (suc n) [] ()
grab-n-vec (suc n) l@(x ∷ xs) (s≤s n≤|xs|) = x ∷ (grab-n-vec n xs n≤|xs|)

grab-n-list : {A : Set} (n : ℕ) → (l : List A) → n ≤ (length l) → List A
grab-n-list 0 _ _ = []
grab-n-list (suc n) [] ()
grab-n-list (suc n) l@(x ∷ xs) (s≤s n≤|xs|) = x ∷ (grab-n-list n xs n≤|xs|)

grab-n-length : {A : Set} (n : ℕ) → (l : List A) → (n≤|l| : n ≤ (length l)) → length (grab-n-list n l n≤|l|) ≡ n
grab-n-length 0 _ _ = refl
grab-n-length (suc n) [] ()
grab-n-length (suc n) l@(x ∷ xs) (s≤s n≤|xs|) = cong suc (grab-n-length n xs n≤|xs|)

split-n : {A : Set} (n : ℕ) → (l : List A) → n ≤ (length l) → List A × List A
split-n 0 l _ = [] , l
split-n (suc n) [] ()
split-n (suc n) l@(x ∷ xs) (s≤s n≤|xs|) = x ∷ (proj₁ rest) , (proj₂ rest)
  where
    rest = split-n n xs n≤|xs|


split-n-grab-n : {A : Set} (n : ℕ) (l : List A) (n≤|l| : n ≤ (length l)) → proj₁ (split-n n l n≤|l|) ≡ (grab-n-list n l n≤|l|)
split-n-grab-n 0 l _ = refl
split-n-grab-n (suc n) [] ()
split-n-grab-n (suc n) l@(x ∷ xs) (s≤s n≤|xs|) = cong (_∷_ x) (split-n-grab-n n xs n≤|xs|)


split-n-length-n : {A : Set} (n : ℕ) → (l : List A) → (n≤|l| : n ≤ (length l)) → length (proj₁ (split-n n l n≤|l|)) ≡ n
split-n-length-n n l n≤|l| = ≡-trans (cong length (split-n-grab-n n l n≤|l|)) (grab-n-length n l n≤|l|)

Vec→Fin : {A : Set} {n : ℕ} → Vec A n → Fin n → A
Vec→Fin {A} {0} [] ()
Vec→Fin {A} {suc n} (x ∷ xs) zero = x
Vec→Fin {A} {suc n} (x ∷ xs) (suc m) = Vec→Fin xs m


eval-helper2-case-true : (c : Combinator') → (l : List (Bin SKI)) → (proj₁ c) ≤ (length l) → List (Bin SKI)
eval-helper2-case-true (n , c) l n≤|l| = out ++ rest
  where
    split = split-n n l n≤|l|
    args = proj₁ split
    rest = proj₂ split
    subs = Vec→Fin (List→Vec-length args (split-n-length-n n l n≤|l|))
    out = lspine (Bin-flat (subst c subs))
    
eval-helper2 : SKI → Combinator' → List (Bin SKI) → List (Bin SKI)
eval-helper2 x (n , c) l = 
    dite'
    (n le (length l))
    (λ case-true → eval-helper2-case-true (n , c) l (le→≤ case-true))
    (λ case-false → ([ x ] ∷ l))

eval-helper : SKI → List (Bin SKI) → List (Bin SKI)
eval-helper c exp = 
    dite'
    (is-just (interp c))
    (λ case-true → eval-helper2 c (is-just-get (interp c) case-true) exp)
    (λ case-false → ([ c ] ∷ exp))

lspine-head-tail : {A : Set} → Bin A → A × List (Bin A)
lspine-head-tail [ x ] = x , []
lspine-head-tail (l ∙ r) = proj₁ rec , (proj₂ rec) ++ (r ∷ [])
  where
    rec = lspine-head-tail l

++-nonempty : {A : Set} → (l₁ l₂ : List A) → l₁ ++ l₂ ≡ [] → l₁ ≡ [] × l₂ ≡ []
++-nonempty [] [] refl = refl , refl
++-nonempty (x ∷ xs) _ ()
++-nonempty [] (y ∷ ys) ()


lspine-nonempty : {A : Set} → (t : Bin A) → lspine t ≢ []
lspine-nonempty [ x ] ()
lspine-nonempty (l ∙ r) lspine≡[] = contradiction
  where
    lspine≡l++r : lspine (l ∙ r) ≡ (lspine l) ++ (r ∷ [])
    lspine≡l++r = refl
    
    l++r≡[]  :(lspine l) ++ (r ∷ []) ≡ []
    l++r≡[] = ≡-trans (≡-sym lspine≡l++r) lspine≡[]

    r≡[] : (r ∷ []) ≡ []
    r≡[] = proj₂ (++-nonempty (lspine l) (r ∷ []) l++r≡[])

    r≢[] : (r ∷ []) ≢ []
    r≢[] ()

    contradiction = r≢[] r≡[]



eval-helper2-case-true-nonempty : (c : Combinator') (l : List (Bin SKI)) (n≤|l| : (proj₁ c) ≤ (length l)) → eval-helper2-case-true c l n≤|l| ≢ []
eval-helper2-case-true-nonempty (n , c) l n≤|l| eval≡[] = contradiction
  where
    split = split-n n l n≤|l|
    args = proj₁ split
    rest = proj₂ split
    subs = Vec→Fin (List→Vec-length args (split-n-length-n n l n≤|l|))
    out = lspine (Bin-flat (subst c subs))

    out++rest≡eval : eval-helper2-case-true (n , c) l n≤|l| ≡ out ++ rest
    out++rest≡eval = refl

    out++rest≡[] = ≡-trans out++rest≡eval eval≡[]

    out≡[] : out ≡ []
    out≡[] = proj₁ (++-nonempty out rest out++rest≡[])

    out≢[] : out ≢ []
    out≢[] = lspine-nonempty (Bin-flat (subst c subs))

    contradiction = out≢[] out≡[]


eval-helper2-nonempty : (x : SKI) (c : Combinator') (l : List (Bin SKI)) → eval-helper2 x c l ≢ []
eval-helper2-nonempty x (n , c) l = ⊎-elim lemma1 lemma2 eval-LEM
  where
    case-true = λ case → eval-helper2-case-true (n , c) l (le→≤ case)
    case-false = λ _ → ([ x ] ∷ l)
    
    eval-def = dite' (n le (length l)) case-true case-false

    eval-LEM :
      (Σ[ e ∈ (n le (length l)) ≡ true ] (eval-def ≡ case-true e)) ⊎
      (Σ[ e ∈ (n le (length l)) ≡ false ] (eval-def ≡ case-false e))
    eval-LEM = dite'-LEM (n le (length l)) case-true case-false

    lemma1 : (Σ[ e ∈ (n le (length l)) ≡ true ] (eval-def ≡ case-true e)) → eval-def ≢ []
    lemma1 (n-le-|l| , eval≡eval2) eval≡[] = subcontradiction
      where
        eval2≡[] = ≡-trans (≡-sym eval≡eval2) eval≡[]
        subcontradiction = eval-helper2-case-true-nonempty (n , c) l (le→≤ n-le-|l|) eval2≡[]

    lemma2 : (Σ[ e ∈ (n le (length l)) ≡ false ] (eval-def ≡ case-false e)) → eval-def ≢ []
    lemma2 (_ , eval≡x∷l) eval≡[] = subcontradiction
      where
        x∷l≡[] = ≡-trans (≡-sym eval≡x∷l) eval≡[]
        x∷l≢[] : ([ x ] ∷ l) ≢ []
        x∷l≢[] ()
        subcontradiction = x∷l≢[] x∷l≡[]


eval-helper-nonempty : (c : SKI) → (exp : List (Bin SKI)) → eval-helper c exp ≢ []
eval-helper-nonempty c exp = ⊎-elim lemma1 lemma2 eval-LEM
  where
    case-true = (λ case → eval-helper2 c (is-just-get (interp c) case) exp)
    case-false = (λ case → ([ c ] ∷ exp))

    eval-def = dite' (is-just (interp c)) case-true case-false

    eval-LEM :
      (Σ[ e ∈ (is-just (interp c)) ≡ true ] (eval-def ≡ case-true e)) ⊎
      (Σ[ e ∈ (is-just (interp c)) ≡ false ] (eval-def ≡ case-false e))
    eval-LEM = dite'-LEM (is-just (interp c)) case-true case-false
    
    lemma1 : (Σ[ e ∈ (is-just (interp c)) ≡ true ] (eval-def ≡ case-true e)) → eval-def ≢ []
    lemma1 (hyp , eval≡eval2) eval≡[] = eval-helper2-nonempty c (is-just-get (interp c) hyp) exp (≡-trans (≡-sym eval≡eval2) eval≡[])

    lemma2 : (Σ[ e ∈ (is-just (interp c)) ≡ false ] (eval-def ≡ case-false e)) → eval-def ≢ []
    lemma2 (_ , eval≡c∷exp) eval≡[] = c∷exp≢[] (≡-trans (≡-sym eval≡c∷exp) eval≡[])
      where
        c∷exp≢[] : ([ c ] ∷ exp) ≢ []
        c∷exp≢[] ()


eval : Bin SKI → Bin SKI
eval exp = un-lspine (eval-helper (proj₁ (lspine-head-tail exp)) (proj₂ (lspine-head-tail exp))) {eval-helper-nonempty (proj₁ (lspine-head-tail exp)) (proj₂ (lspine-head-tail exp))}

exp1 : Bin SKI
exp1 = (((([ S ]) ∙ [ v 0 ]) ∙ [ v 1 ]) ∙ [ v 2 ]) ∙ [ v 3 ]

exp2 : Bin SKI
exp2 = ((([ S ]) ∙ [ K ]) ∙ [ I ]) ∙ ((([ K ]) ∙ [ I ]) ∙ [ S ])

{-
TODO:
* string parser
* arbitrary reductions
* normal forms
* translation between combinatory logic and UTLC
-}

{-
Combinatory completeness:
* remove any unused arguments
* repeat the remaining arguments as many times as they are used in the result
* rearrange the arguments into their proper order
* regroup them into their proper tree structure
-}
