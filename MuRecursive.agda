module MuRecursive where

open import Basic hiding ([_] ; map ; foldr) renaming (Vec-get to _[_])
open import Data.Vec using (map ; foldr ; head ; tail)
open import PR

-- The "mu" is for all the mutual recursion I needed to make the definitions and proofs pass termination check...

List-ext : {i : Level} {A : Set i} {x y : A} {xs ys : List A} → x ≡ y → xs ≡ ys → _≡_ {i} {List A} (x ∷ xs) (y ∷ ys)
List-ext refl refl = refl


Vec-ext : {i : Level} {A : Set i} {n : ℕ} {x y : A} {xs ys : Vec A n} → x ≡ y → xs ≡ ys → _≡_ {i} {Vec A (1 + n)} (x ∷ xs) (y ∷ ys)
Vec-ext refl refl = refl

Vec-ext2 : {i : Level} {A : Set i} {n : ℕ} (xs : Vec A (1 + n)) → xs ≡ (head xs) ∷ (tail xs)
Vec-ext2 (x ∷ xs) = refl

Vec-empty : {i : Level} {A : Set i} → (xs : Vec A 0) → xs ≡ []
Vec-empty [] = refl

Vec1-ext : {i : Level} {A : Set i} → (xs : Vec A 1) → xs ≡ ((head xs) ∷ [])
Vec1-ext (x ∷ []) = refl

{-
These are all more general
-}
total : {A B : Set} → (A → B → Set) → Set
total {A} {B} R = (x : A) → Σ[ y ∈ B ] (R x y)

{-
  domain ϕ where ϕ : μR n is a predicate which is true of an input x ∈ ℕ^n if ∃ y , f(x) = y
-}
domain : {A B : Set} → (A → B → Set) → A → Set
domain {A} {B} R x = (Σ[ y ∈ B ] (R x y))

Defined : {A B : Set} → (A → B → Set) → A → Set
Defined {A} {B} R x = domain R x

Functional : {A B : Set} → (A → B → Set) → Set
Functional {A} {B} R = (x : A) → (y₁ y₂ : B) → R x y₁ → R x y₂ → y₁ ≡ y₂

rel-map : {A B : Set} → {k : ℕ} → (A → B → Set) → Vec A k → Vec B k → Set
rel-map R [] [] = ⊤
rel-map R (a ∷ as) (b ∷ bs) = (R a b) × (rel-map R as bs)

rel-fold : {A B C : Set} → {k : ℕ} → (A → B → C → Set) → Vec A k → B → Vec C k → Set
rel-fold R [] b [] = ⊤
rel-fold R (a ∷ as) b (c ∷ cs) = (R a b c) × (rel-fold R as b cs)






{-
  AST data structure for μ-recursive functions
-}
data μR : ℕ → Set where
  zero : μR 1
  succ : μR 1
  proj : (n : ℕ) → Fin n → μR n
  comp : {n k : ℕ} → μR k → Vec (μR n) k → μR n
  prim-rec : {n : ℕ} → μR n → μR (2 + n) → μR (1 + n)
  μ-rec : {k : ℕ} → μR (1 + k) → μR k


μ : {k : ℕ} → μR (1 + k) → μR k
μ = μ-rec



{-
 Interpretation of arity-n μ-recursive functions as an input/output relations R ⊆ ℕ^(n+1)

 FIXME: can we abstract out the mutual recursive part for clarity?
-}


_[_]=_ : {n : ℕ} → μR n → Vec ℕ n → ℕ → Set


fold[_,_]=_ : {n k : ℕ} → Vec (μR n) k → Vec ℕ n → Vec ℕ k → Set
{-
fold[ gs , xs ]= v = = Vec-map (λ g → 
-}
fold[ [] , _ ]= [] = ⊤
fold[ (g ∷ gs) , xs ]= (y ∷ ys) = (g [ xs ]= y) × (fold[ gs , xs ]= ys)

zero                [ _              ]= y = y ≡ 0
succ                [ xs             ]= y = y ≡ (1 + (head xs))
(proj n i)          [ xs             ]= y = y ≡ xs [ i ]
(comp {n} {k} f gs) [ xs             ]= y = Σ[ v ∈ Vec ℕ k ] ((fold[ gs , xs ]= v) × (f [ v ]= y))
(prim-rec f g)      [ (0 ∷ xs)       ]= y = f [ xs ]= y
(prim-rec f g)      [ ((suc n) ∷ xs) ]= y = Σ[ r ∈ ℕ ] (
                                                   ((prim-rec f g) [ (n ∷ xs)           ]= r)
                                                 × (g              [ ((1 + n) ∷ r ∷ xs) ]= y)
                                            )
(μ-rec f)           [ xs             ]= y = min-Nat (λ n → f [ (n ∷ xs)]= 0) y

μR-interp : {n : ℕ } → μR n → Vec ℕ n → ℕ → Set
μR-interp = _[_]=_








{-
 Proof that the μ-recursive functions are actually functions
-}
μR-functional : ∀ { n } (f : μR n) → Functional (μR-interp f)

{-
 -- fold (Vec-ext ∘ μR-functional) refl ?
 -- fold : B → (A → B → B) → List A → B

-}
μR-functional-vec : {n k : ℕ} → (gs : Vec (μR n) k) → (xs : Vec ℕ n) → (v₁ v₂ : Vec ℕ k) → fold[ gs , xs ]= v₁ → fold[ gs , xs ]= v₂ → v₁ ≡ v₂
{-
μR-functional-vec gs xs ys₁ ys₂ h₁ h₂ = fold (Vec-ext ∘ μR-functional) refl 
-}

μR-functional-vec {n} {0} [] _ [] [] unit unit = refl
μR-functional-vec {n} {suc k} (g ∷ gs) xs (y₁ ∷ ys₁) (y₂ ∷ ys₂) (g[xs]≡y₁ , gs[xs]≡ys₁) (g[xs]≡y₂ , gs[xs]≡ys₂) = Vec-ext y₁≡y₂ ys₁≡ys₂
  where
    y₁≡y₂ : y₁ ≡ y₂
    y₁≡y₂ = μR-functional g xs y₁ y₂ g[xs]≡y₁ g[xs]≡y₂

    ys₁≡ys₂ : ys₁ ≡ ys₂
    ys₁≡ys₂ = μR-functional-vec gs xs ys₁ ys₂ gs[xs]≡ys₁ gs[xs]≡ys₂



μR-functional-prim-rec : {n : ℕ} → (f : μR n) → (g : μR (2 + n)) → (m : ℕ) → (xs : Vec ℕ n) → (y₁ y₂ : ℕ) → (prim-rec f g) [ (m ∷ xs) ]= y₁ → (prim-rec f g) [ (m ∷ xs) ]= y₂ → y₁ ≡ y₂
μR-functional-prim-rec {n} f g 0 xs y₁ y₂ f[xs]≡y₁ f[xs]≡y₂ = μR-functional f xs y₁ y₂ f[xs]≡y₁ f[xs]≡y₂
μR-functional-prim-rec {n} f g (suc m) xs y₁ y₂ (r₁ , (rec[m∷xs]≡r₁ , g[1+m∷r₁∷xs]≡y₁)) (r₂ , (rec[m∷xs]≡r₂ , g[1+m∷r₂∷xs]≡y₂)) = proof
  where
    r₁≡r₂ : r₁ ≡ r₂
    r₁≡r₂ = μR-functional-prim-rec f g m xs r₁ r₂ rec[m∷xs]≡r₁ rec[m∷xs]≡r₂

    lemma : g [ ((1 + m) ∷ r₁ ∷ xs) ]= y₂
    lemma = resp (λ r → g [ ((1 + m) ∷ r ∷ xs) ]= y₂) (≡-sym r₁≡r₂) g[1+m∷r₂∷xs]≡y₂

    proof = μR-functional g ((1 + m) ∷ r₁ ∷ xs) y₁ y₂ g[1+m∷r₁∷xs]≡y₁ lemma



μR-functional zero _ y₁ y₂ y₁≡0 y₂≡0 = ≡-trans y₁≡0 (≡-sym y₂≡0)
μR-functional succ (x ∷ []) y₁ y₂ y₁≡1+x y₂≡1+x = ≡-trans y₁≡1+x (≡-sym y₂≡1+x)
μR-functional (proj n i) xs y₁ y₂ y₁≡xs[i] y₂≡xs[i] = ≡-trans y₁≡xs[i] (≡-sym y₂≡xs[i])
μR-functional (prim-rec f g) (n ∷ xs) y₁ y₂ hyp₁ hyp₂ = μR-functional-prim-rec f g n xs y₁ y₂ hyp₁ hyp₂
μR-functional (μ-rec f) xs y₁ y₂ hyp₁ hyp₂ = min-Nat-unique (λ n → f [ (n ∷ xs) ]= 0) hyp₁ hyp₂
μR-functional (comp f gs) xs y₁ y₂ (v₁ , (gs[xs]≡v₁ , f[v₁]≡y₁)) (v₂ , (gs[xs]≡v₂ , f[v₂]≡y₂)) = μR-functional f v₂ y₁ y₂ f[v₂]≡y₁ f[v₂]≡y₂
  where
    v₁≡v₂ : v₁ ≡ v₂
    v₁≡v₂ = μR-functional-vec gs xs v₁ v₂ gs[xs]≡v₁ gs[xs]≡v₂

    f[v₂]≡y₁ : f [ v₂ ]= y₁
    f[v₂]≡y₁ = resp (λ v → f [ v ]= y₁) v₁≡v₂ f[v₁]≡y₁










{-
What is this?
-}
RE : {n : ℕ} → (Vec ℕ n → Set) → Set
RE {n} S = Σ[ f ∈ (μR n) ] ((x : Vec ℕ n) → S x ↔ (domain (μR-interp f) x))





Is-syntactically-PR : {n : ℕ} → μR n → Set

fold'' : {n k : ℕ} → Vec (μR n) k → Set
fold'' [] = ⊤
fold'' (g ∷ gs) = Is-syntactically-PR g × (fold'' gs)
    
Is-syntactically-PR zero = ⊤
Is-syntactically-PR succ = ⊤
Is-syntactically-PR (proj n i) = ⊤
Is-syntactically-PR (comp f gs) = (Is-syntactically-PR f) × (fold'' gs)
Is-syntactically-PR (prim-rec f g) = (Is-syntactically-PR f) × (Is-syntactically-PR g)
Is-syntactically-PR (μ-rec f) = ⊥

{-
FIXME: Kind of annoying that we are essentially duplicating Is-syntactically-PR to create a runnable Bool version. Any way to just use Is-syntactically-PR directly?
-}
is-syntactically-PR : {n : ℕ} → μR n → Bool

is-syntactically-PR-helper : {n k : ℕ} → Vec (μR n) k → Bool
is-syntactically-PR-helper [] = true
is-syntactically-PR-helper (g ∷ gs) = (is-syntactically-PR g) and (is-syntactically-PR-helper gs)

is-syntactically-PR zero = true
is-syntactically-PR succ = true
is-syntactically-PR (proj n i) = true
is-syntactically-PR (comp f gs) = (is-syntactically-PR f) and (is-syntactically-PR-helper gs)
is-syntactically-PR (prim-rec f g) = (is-syntactically-PR f) and (is-syntactically-PR g)
is-syntactically-PR (μ-rec f) = false




Is-semantically-PR : {n : ℕ} → μR n → Set
Is-semantically-PR {n} f = Σ[ f' ∈ PR n ] ((x : Vec ℕ n) → f [ x ]= (PR-interp f' x))


{-
Lift a syntactically PR function to a μR function
-}
PR→μR : {n : ℕ} → PR n → μR n
PR→μR zero = zero
PR→μR succ = succ
PR→μR (proj n i) = proj n i
PR→μR (comp {n} {k} f gs) = comp (PR→μR f) (map' gs)
  where
    map' : {k' : ℕ} → Vec (PR n) k' → Vec (μR n) k'
    map' [] = []
    map' (g' ∷ gs') = PR→μR g' ∷ (map' gs')
PR→μR (prim-rec f g) = prim-rec (PR→μR f) (PR→μR g)




{-
Lower a syntactically PR function from a μR function
-}
μR→PR : {n : ℕ} → (f : μR n) → Is-syntactically-PR f → PR n

fold''-lemma : {n k : ℕ} → (gs : Vec (μR n) k) → fold'' gs → Vec (PR n) k
fold''-lemma [] unit = []
fold''-lemma (g ∷ gs) (g-PR , gs-PR) = (μR→PR g g-PR) ∷ (fold''-lemma gs gs-PR)

μR→PR zero _ = zero
μR→PR succ _ = succ
μR→PR (proj n i) _ = proj n i
μR→PR (comp {n} {k} f gs) (f-PR , gs-PR) = comp (μR→PR f f-PR) (fold''-lemma gs gs-PR)
μR→PR (prim-rec f g) (f-PR , g-PR) = prim-rec (μR→PR f f-PR) (μR→PR g g-PR)
μR→PR (μ-rec f) ()




μR-Defined : {n : ℕ} → μR n → Vec ℕ n → Set
μR-Defined f x = Defined (μR-interp f) x

μR-Halting : {n : ℕ} → μR n → Vec ℕ n → Set
μR-Halting = μR-Defined




{-
 A predicate P on domain A is μR-decidable if there exists a bijective encoding e : A → ℕ
 and a μ-recursive function f of arity 1 that outputs 0 or 1 and such that f(e a) = 1 iff P(a).
-}
μR-decidable : {i j : Level} {A : Set i} → (P : A → Set j) → Set (i ⊔ j)
μR-decidable {i} {j} {A} P =
  Σ[ e ∈ (A → ℕ) ] (
      (Bijective e)
    × Σ[ f ∈ μR 1 ] (
      ((a : A) → ((f [ ((e a) ∷ []) ]= 0) ⊎ (f [ ((e a) ∷ []) ]= 1)))
      × ((a : A) → ((f [ ((e a) ∷ []) ]= 1) ↔ P a))
    )
  )

μR-undecidable : {i j : Level} {A : Set i} → (P : A → Set j) → Set (i ⊔ j)
μR-undecidable P = ¬ (μR-decidable P)


{-
 Simple 0-ary μ-recursive function that loops on its (empty) input

-}
μR-loop-example : μR 0
μR-loop-example = μ-rec (comp succ (proj 1 zero ∷ []))

μR-loop-example-loops : ¬ (μR-Halting μR-loop-example [])
μR-loop-example-loops (y , μf[]≡y) = contradiction
  where
    μf = μR-loop-example

    f : μR 1
    f = comp succ (proj 1 zero ∷ [])

    f[y]≡0 : Σ[ v ∈ Vec ℕ 1 ] ((fold[ (proj 1 zero ∷ []) , (y ∷ []) ]= v) × (succ [ v ]= 0))
    f[y]≡0 = proj₁ μf[]≡y

    v : Vec ℕ 1
    v = proj₁ f[y]≡0

    succ[v]≡0 : succ [ v ]= 0
    succ[v]≡0 = proj₂ (proj₂ f[y]≡0)

    0≡1+h[v] : 0 ≡ 1 + (head v)
    0≡1+h[v] = succ[v]≡0

    contradiction = 1+n≢0 (≡-sym 0≡1+h[v])

{-
  The looping μ-recursive function is not primitive recursive
-}
μR-loop-example-not-PR : ¬ (Is-semantically-PR μR-loop-example)
μR-loop-example-not-PR (f , λx→P[x]≡f[x]) = proof
  where
    P[]≡f[] : μR-loop-example [ [] ]= (PR-interp f [])
    P[]≡f[] = λx→P[x]≡f[x] []

    proof = μR-loop-example-loops (PR-interp f [] , P[]≡f[])

{-
  Simple 0-ary μ-recursive function that halts on its (empty) input
-}
μR-halt-example : μR 0
μR-halt-example = μ-rec zero


μR-halt-example-halts : μR-halt-example [ [] ]= 0
μR-halt-example-halts = refl , (λ _ _ → z≤n)


{-
  Simple 2-ary μ-recursive function that loops on every input
-}
μR-loop-example2 : μR 2
μR-loop-example2 = μ-rec (comp succ (proj 3 zero ∷ []))

0≢succ-v : {xs : Vec ℕ 1} → ¬ (succ [ xs ]= 0)
0≢succ-v {xs@(x₁ ∷ [])} succ[xs]≡0 = 1+n≢0 (≡-sym succ[xs]≡0)


μR-loop-example2-loops :  (x : Vec ℕ 2) → ¬ (μR-Halting μR-loop-example2 x)
μR-loop-example2-loops x@(x₁ ∷ x₂ ∷ []) (y , f[x]≡y) = 0≢succ-v {proj₁ (proj₁ f[x]≡y)} (proj₂ (proj₂ (proj₁ f[x]≡y)))


{-
  This is to help construct the "diagonalization gadget" for proving the undecidability of the halting problem
  Intuitively it has the semantics that it will halt on input 0 and loop on any other input
-}
μR-K-helper : μR 1
μR-K-helper = prim-rec μR-halt-example μR-loop-example2

μR-K-helper-halts-on-0 : μR-K-helper [ (0 ∷ []) ]= 0
μR-K-helper-halts-on-0 = μR-halt-example-halts

μR-K-helper-loops-on-1 : ¬ (μR-Halting μR-K-helper (1 ∷ []))
μR-K-helper-loops-on-1 (y , f[1]≡y) = μR-loop-example2-loops (1 ∷ (proj₁ f[1]≡y) ∷ []) (y , (proj₂ (proj₂ f[1]≡y)))






{-
Proof that the halting problem for μ-recursive functions is undecidable (by μ-recursive functions)
-}

μR-halting-undecidable :
  ¬(
    Σ[ e ∈ (μR 1 → ℕ) ] (
      Σ[ H ∈ μR 2 ] (
        (P : μR 1) → 
        (x : Vec ℕ 1) →
          ((H [ ((e P) ∷ x) ]= 0) ⊎ (H [ ((e P) ∷ x) ]= 1))
        × ((H [ ((e P) ∷ x) ]= 1) ↔ (Σ[ y ∈ ℕ ] (P [ x ]= y)))
      )
    )
  )
μR-halting-undecidable (e , (H , H-def)) = contradiction
  where
    {-
      Intuitively, on input x, K runs H[x,x].
      If H[x,x] returns 0 indicating that x loops on input x, then K halts
      If H[x,x] returns 1 indicating that x halts on input x, then K loops
    -}

    K' = μR-K-helper
    
    K'[0]≡0 : K' [ (0 ∷ []) ]= 0
    K'[0]≡0 = μR-K-helper-halts-on-0
    ¬∃y,K'[1]≡y = μR-K-helper-loops-on-1

    π₀ = proj 1 zero
    
    K : μR 1
    K = comp K' (comp H (π₀ ∷ π₀ ∷ []) ∷ [])

    ϕ = e K
    H[ϕ,ϕ] = H [ (ϕ ∷ ϕ ∷ []) ]= 1
    ¬H[ϕ,ϕ] = H [ (ϕ ∷ ϕ ∷ []) ]= 0

    {-
      By definition, H always terminates with output either 0 or 1
    -}
    LEM[H[ϕ,ϕ]] : ¬H[ϕ,ϕ] ⊎ H[ϕ,ϕ]
    LEM[H[ϕ,ϕ]] = proj₁ (H-def K (ϕ ∷ []))

    {-
      By definition, H terminates with 1 on input pair (ϕ₁, ϕ₂) exactly when ϕ₁ = e P where P is a μ-recursive function and P is defined on input ϕ₂ 
    -}
    H[ϕ,ϕ]→Defined[K[ϕ]] : H[ϕ,ϕ] → μR-Defined K (ϕ ∷ [])
    H[ϕ,ϕ]→Defined[K[ϕ]] = proj₁ (proj₂ (H-def K (ϕ ∷ [])))

    Defined[K[ϕ]]→H[ϕ,ϕ] : μR-Defined K (ϕ ∷ []) → H[ϕ,ϕ]
    Defined[K[ϕ]]→H[ϕ,ϕ] = proj₂ (proj₂ (H-def K (ϕ ∷ [])))

    

    {-
      K is not defined on input ϕ, because then H[ϕ,ϕ] ≡ 1, and then K' must be defined on 1 otherwise K would be undefined on ϕ, but K' is not defined on 1
    -}
    ¬Defined[K[ϕ]] : ¬ (μR-Defined K (ϕ ∷ []))
    ¬Defined[K[ϕ]] Defined[K[ϕ]]@(y , K[ϕ]≡y) = contradiction
      where
        H[ϕ,ϕ]-proof : H[ϕ,ϕ]
        H[ϕ,ϕ]-proof = Defined[K[ϕ]]→H[ϕ,ϕ] Defined[K[ϕ]]

        
        ∃v,[H[ϕ,ϕ]≡v]×[K'[v]≡y] : Σ[ v ∈ Vec ℕ 1 ] ((fold[ (comp H (π₀ ∷ π₀ ∷ []) ∷ []) , (ϕ ∷ []) ]= v) × K' [ v ]= y)
        ∃v,[H[ϕ,ϕ]≡v]×[K'[v]≡y] = K[ϕ]≡y

        {-
          All of this to establish that v ≡ (x ∷ [])
        -}
        v : Vec ℕ 1
        v = proj₁ K[ϕ]≡y
      
        x : ℕ
        x = head v

        v≡x∷[] : v ≡ (x ∷ [])
        v≡x∷[] = Vec1-ext v


        sublemma4 : fold[ (comp H (π₀ ∷ π₀ ∷ []) ∷ []) , (ϕ ∷ []) ]= v
        sublemma4 = proj₁ (proj₂ K[ϕ]≡y)

        sublemma5 : fold[ (comp H (π₀ ∷ π₀ ∷ []) ∷ []) , (ϕ ∷ []) ]= (x ∷ [])
        sublemma5 = resp (λ r → fold[ (comp H (π₀ ∷ π₀ ∷ []) ∷ []) , (ϕ ∷ []) ]= r) v≡x∷[] sublemma4

        H∘<π₀,π₀>[ϕ]≡x : (comp H (π₀ ∷ π₀ ∷ [])) [ (ϕ ∷ []) ]= x
        H∘<π₀,π₀>[ϕ]≡x = proj₁ sublemma5

        
        sublemma7 : Σ[ v₂ ∈ Vec ℕ 2 ] ((fold[ (π₀ ∷ π₀ ∷ []) , (ϕ ∷ []) ]= v₂ ) × (H [ v₂ ]= x))
        sublemma7 = H∘<π₀,π₀>[ϕ]≡x

        v₂ : Vec ℕ 2
        v₂ = proj₁ sublemma7



        sublemma8 : fold[ (π₀ ∷ π₀ ∷ []) , (ϕ ∷ []) ]= v₂
        sublemma8 = proj₁ (proj₂ sublemma7)

        sublemma9 : fold[ (π₀ ∷ π₀ ∷ []) , (ϕ ∷ []) ]= (ϕ ∷ ϕ ∷ [])
        sublemma9 = (refl , (refl , unit))

        v₂≡ϕ∷ϕ∷[] : v₂ ≡ (ϕ ∷ ϕ ∷ [])
        v₂≡ϕ∷ϕ∷[] = μR-functional-vec ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ((e K) ∷ []) v₂ ((e K) ∷ (e K) ∷ []) sublemma8 sublemma9

        H[v₂]≡x : H [ v₂ ]= x
        H[v₂]≡x = proj₂ (proj₂ sublemma7)

        H[ϕ,ϕ]≡x : H [ (ϕ ∷ ϕ ∷ []) ]= x
        H[ϕ,ϕ]≡x = resp (λ r → H [ r ]= x) v₂≡ϕ∷ϕ∷[] H[v₂]≡x

        x≡1 : x ≡ 1
        x≡1 = μR-functional H (ϕ ∷ ϕ ∷ []) x 1 H[ϕ,ϕ]≡x H[ϕ,ϕ]-proof

        x∷[]≡1∷[] : (x ∷ []) ≡ (1 ∷ [])
        x∷[]≡1∷[] = cong (λ r → r ∷ []) x≡1

        v≡1∷[] : v ≡ (1 ∷ [])
        v≡1∷[] = ≡-trans v≡x∷[] x∷[]≡1∷[]

        K'[v]≡y : K' [ v ]= y
        K'[v]≡y = proj₂ (proj₂ ∃v,[H[ϕ,ϕ]≡v]×[K'[v]≡y])

        K'[1]≡y : K' [ (1 ∷ []) ]= y
        K'[1]≡y = resp (λ r → K' [ r ]= y) v≡1∷[] K'[v]≡y

        ∃y,K'[1]≡y = y , K'[1]≡y

        contradiction = ¬∃y,K'[1]≡y ∃y,K'[1]≡y

    {-
      H(ϕ,ϕ) ≢ 1 because H(ϕ,ϕ) → K is defined on ϕ, by definition of H, but K is not defined on ϕ
    -}
    H[ϕ,ϕ]≢1 : ¬ (H [ (ϕ ∷ ϕ ∷ []) ]= 1)
    H[ϕ,ϕ]≢1 H[ϕ,ϕ]≡1 = ¬Defined[K[ϕ]] (H[ϕ,ϕ]→Defined[K[ϕ]] H[ϕ,ϕ]≡1)

    {-
      H(ϕ,ϕ) ≢ 0 because ¬H(ϕ,ϕ) → K is defined on ϕ, by definition of K (note K'[0] ≡ 0), but K is not defined on ϕ
    -}
    H[ϕ,ϕ]≢0 : ¬ (H [ (ϕ ∷ ϕ ∷ []) ]= 0)
    H[ϕ,ϕ]≢0 H[ϕ,ϕ]≡0 = contradiction
      where
        K[ϕ]≡0 : K [ (ϕ ∷ []) ]= 0
        K[ϕ]≡0 = subsubproof
          where
            <π₀,π₀>[ϕ]≡[ϕ,ϕ] : fold[ (π₀ ∷ π₀ ∷ []) , (ϕ ∷ []) ]= (ϕ ∷ ϕ ∷ [])
            <π₀,π₀>[ϕ]≡[ϕ,ϕ] = refl , (refl , unit)

            <H∘<π₀,π₀>>[ϕ]≡0 : fold[ (comp H (π₀ ∷ π₀ ∷ []) ∷ []) , (ϕ ∷ []) ]= (0 ∷ [])
            <H∘<π₀,π₀>>[ϕ]≡0 = ((ϕ ∷ ϕ ∷ []) , (<π₀,π₀>[ϕ]≡[ϕ,ϕ] , H[ϕ,ϕ]≡0)) , unit
            
            subsubproof = (0 ∷ []) , (<H∘<π₀,π₀>>[ϕ]≡0 , K'[0]≡0)
            
        Defined[K[ϕ]] : μR-Defined K (ϕ ∷ [])
        Defined[K[ϕ]] = 0 , K[ϕ]≡0
        
        contradiction = ¬Defined[K[ϕ]] Defined[K[ϕ]]

    ¬LEM[H[ϕ,ϕ]] : ¬ (¬H[ϕ,ϕ] ⊎ H[ϕ,ϕ])
    ¬LEM[H[ϕ,ϕ]] (inj₁ H[ϕ,ϕ]≡0) = H[ϕ,ϕ]≢0 H[ϕ,ϕ]≡0
    ¬LEM[H[ϕ,ϕ]] (inj₂ H[ϕ,ϕ]≡1) = H[ϕ,ϕ]≢1 H[ϕ,ϕ]≡1
    
    contradiction = ¬LEM[H[ϕ,ϕ]] LEM[H[ϕ,ϕ]]
