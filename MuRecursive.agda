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

data μR : ℕ → Set where
  zero : μR 1
  succ : μR 1
  proj : (n : ℕ) → Fin n → μR n
  comp : {n k : ℕ} → μR k → Vec (μR n) k → μR n
  prim-rec : {n : ℕ} → μR n → μR (2 + n) → μR (1 + n)
  μ-rec : {k : ℕ} → μR (1 + k) → μR k

 
μR-interp : {n : ℕ} → μR n → Vec ℕ n → ℕ → Set

-- FIXME: better name for this?
fold' : {n k : ℕ} → Vec (μR n) k → Vec ℕ k → Vec ℕ n → Set
fold' [] [] _ = ⊤
fold' (g ∷ gs) (y ∷ ys) xs = (μR-interp g xs y) × (fold' gs ys xs)

-- μR-interp : {n : ℕ} → μR n → Vec ℕ n → ℕ → Set
μR-interp zero _ y = y ≡ 0
μR-interp succ (x ∷ []) y = y ≡ (1 + x)
μR-interp (proj n i) xs y = y ≡ xs [ i ]
μR-interp (comp {n} {k} f gs) xs y = Σ[ v ∈ Vec ℕ k ] ((fold' gs v xs) × (μR-interp f v y))
μR-interp (prim-rec f g) (0 ∷ xs) y = μR-interp f xs y
μR-interp (prim-rec f g) ((suc n) ∷ xs) y =
  Σ[ r ∈ ℕ ] (
      (μR-interp (prim-rec f g) (n ∷ xs) r)
    × (μR-interp g ((1 + n) ∷ r ∷ xs) y)
  )
μR-interp (μ-rec f) xs y = min-Nat (λ n → μR-interp f (n ∷ xs) 0) y

total : {n : ℕ} → μR n → Set
total {n} f = (x : Vec ℕ n) → Σ[ y ∈ ℕ ] (μR-interp f x y)

domain : {n : ℕ} → μR n → (Vec ℕ n) → Set
domain {n} f x = (Σ[ y ∈ ℕ ] (μR-interp f x y))



μR-functional : {n : ℕ} → (f : μR n) → (x : Vec ℕ n) → (y₁ y₂ : ℕ) → μR-interp f x y₁ → μR-interp f x y₂ → y₁ ≡ y₂

fold'-lemma : {n k : ℕ} → (gs : Vec (μR n) k) → (v₁ v₂ : Vec ℕ k) → (xs : Vec ℕ n) → fold' gs v₁ xs → fold' gs v₂ xs → v₁ ≡ v₂
fold'-lemma [] [] [] _ _ _ = refl
fold'-lemma (g ∷ gs) (y₁ ∷ ys₁) (y₂ ∷ ys₂) x (g[x]≡y₁ , gs[x]≡ys₁) (g[x]≡y₂ , gs[x]≡ys₂) = Vec-ext y₁≡y₂ ys₁≡ys₂
  where
    y₁≡y₂ : y₁ ≡ y₂
    y₁≡y₂ = μR-functional g x y₁ y₂ g[x]≡y₁ g[x]≡y₂

    ys₁≡ys₂ : ys₁ ≡ ys₂
    ys₁≡ys₂ = fold'-lemma gs ys₁ ys₂ x gs[x]≡ys₁ gs[x]≡ys₂

prim-rec-lemma : {n : ℕ} → (f : μR n) → (g : μR (2 + n)) → (m : ℕ) → (xs : Vec ℕ n) → (y₁ y₂ : ℕ) → μR-interp (prim-rec f g) (m ∷ xs) y₁ → μR-interp (prim-rec f g) (m ∷ xs) y₂ → y₁ ≡ y₂
prim-rec-lemma {n} f g 0 xs y₁ y₂ f[xs]≡y₁ f[xs]≡y₂ = μR-functional f xs y₁ y₂ f[xs]≡y₁ f[xs]≡y₂
prim-rec-lemma {n} f g (suc m) xs y₁ y₂ (r₁ , (rec[m∷xs]≡r₁ , g[1+m∷r₁∷xs]≡y₁)) (r₂ , (rec[m∷xs]≡r₂ , g[1+m∷r₂∷xs]≡y₂)) = proof
  where
    r₁≡r₂ : r₁ ≡ r₂
    r₁≡r₂ = prim-rec-lemma f g m xs r₁ r₂ rec[m∷xs]≡r₁ rec[m∷xs]≡r₂

    lemma : μR-interp g ((1 + m) ∷ r₁ ∷ xs) y₂
    lemma = resp (λ r → μR-interp g ((1 + m) ∷ r ∷ xs) y₂) (≡-sym r₁≡r₂) g[1+m∷r₂∷xs]≡y₂

    proof = μR-functional g ((1 + m) ∷ r₁ ∷ xs) y₁ y₂ g[1+m∷r₁∷xs]≡y₁ lemma

μR-functional zero _ y₁ y₂ y₁≡0 y₂≡0 = ≡-trans y₁≡0 (≡-sym y₂≡0)
μR-functional succ (x ∷ []) y₁ y₂ y₁≡1+x y₂≡1+x = ≡-trans y₁≡1+x (≡-sym y₂≡1+x)
μR-functional (proj n i) xs y₁ y₂ y₁≡xs[i] y₂≡xs[i] = ≡-trans y₁≡xs[i] (≡-sym y₂≡xs[i])
μR-functional (prim-rec f g) (n ∷ xs) y₁ y₂ hyp₁ hyp₂ = prim-rec-lemma f g n xs y₁ y₂ hyp₁ hyp₂
μR-functional (μ-rec f) xs y₁ y₂ hyp₁ hyp₂ = min-Nat-unique (λ n → μR-interp f (n ∷ xs) 0) hyp₁ hyp₂
μR-functional (comp f gs) xs y₁ y₂ (v₁ , (gs[xs]≡v₁ , f[v₁]≡y₁)) (v₂ , (gs[xs]≡v₂ , f[v₂]≡y₂)) = μR-functional f v₂ y₁ y₂ f[v₂]≡y₁ f[v₂]≡y₂
  where
    v₁≡v₂ : v₁ ≡ v₂
    v₁≡v₂ = fold'-lemma gs v₁ v₂ xs gs[xs]≡v₁ gs[xs]≡v₂

    f[v₂]≡y₁ : μR-interp f v₂ y₁
    f[v₂]≡y₁ = resp (λ v → μR-interp f v y₁) v₁≡v₂ f[v₁]≡y₁


RE : {n : ℕ} → (Vec ℕ n → Set) → Set
RE {n} S = Σ[ f ∈ (μR n) ] ((x : Vec ℕ n) → S x ↔ (domain f x))

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
Is-semantically-PR {n} f = Σ[ f' ∈ PR n ] ((x : Vec ℕ n) → μR-interp f x (PR-interp f' x))


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

μR-halting : Σ[ n ∈ ℕ ] (μR n × Vec ℕ n) → Set
μR-halting (n , (f , x)) = Σ[ y ∈ ℕ ] (μR-interp f x y)


μR-decidable : {i j : Level} {A : Set i} → (P : A → Set j) → Set (i ⊔ j)
μR-decidable {i} {j} {A} P =
  Σ[ e ∈ (A → ℕ) ] (
      (Bijective e)
    × Σ[ f ∈ μR 1 ] (
      ((a : A) → ((μR-interp f ((e a) ∷ []) 0) ⊎ (μR-interp f ((e a) ∷ []) 1)))
      × ((a : A) → ((μR-interp f ((e a) ∷ []) 1) ↔ P a))
    )
  )

μR-undecidable : {i j : Level} {A : Set i} → (P : A → Set j) → Set (i ⊔ j)
μR-undecidable P = ¬ (μR-decidable P)

{-
Can use this to prove that not every μ-recursive function is semantically primitive recursive
-}
μR-loop-example : μR 0
μR-loop-example = μ-rec (comp succ (proj 1 zero ∷ []))

μR-loop-example-loops : ¬ (μR-halting (0 , (μR-loop-example , [])))
μR-loop-example-loops (y , f[]≡y) = proof
  where
    lemma1 : μR-interp μR-loop-example [] y
    lemma1 = f[]≡y

    lemma2 :  min-Nat (λ n → μR-interp (comp succ (proj 1 zero ∷ [])) (n ∷ []) 0) y
    lemma2 = f[]≡y

    lemma3 : min-Nat (λ n →  Σ[ v ∈ Vec ℕ 1 ] ((fold' (proj 1 zero ∷ []) v (n ∷ [])) × (μR-interp succ v 0))) y
    lemma3 = f[]≡y

    lemma4 : (Σ[ v ∈ Vec ℕ 1 ] ((fold' (proj 1 zero ∷ []) v (y ∷ [])) × (μR-interp succ v 0))) × ((m : ℕ) → (Σ[ v ∈ Vec ℕ 1 ] ((fold' (proj 1 zero ∷ []) v (m ∷ [])) × (μR-interp succ v 0))) → y ≤ m)
    lemma4 = f[]≡y

    lemma5 : Σ[ v ∈ Vec ℕ 1 ] ((fold' (proj 1 zero ∷ []) v (y ∷ [])) × (μR-interp succ v 0))
    lemma5 = proj₁ f[]≡y

    v : Vec ℕ 1
    v = proj₁ lemma5

    x : ℕ
    x = head v

    vs : Vec ℕ 0
    vs = tail v

    v≡x∷vs : v ≡ (x ∷ vs)
    v≡x∷vs = Vec-ext2 v

    vs≡[] : vs ≡ []
    vs≡[] = Vec-empty vs

    x∷vs≡x∷[] : (x ∷ vs) ≡ (x ∷ [])
    x∷vs≡x∷[] = cong (λ xs → x ∷ xs) vs≡[]

    v≡x∷[] : v ≡ (x ∷ [])
    v≡x∷[] = ≡-trans v≡x∷vs x∷vs≡x∷[]

    lemma6 : fold' (proj 1 zero ∷ []) v (y ∷ [])
    lemma6 = proj₁ (proj₂ lemma5)

    lemma7 : fold' (proj 1 zero ∷ []) (x ∷ []) (y ∷ [])
    lemma7 = resp (λ r → fold' (proj 1 zero ∷ []) r (y ∷ [])) v≡x∷[] lemma6

    lemma8 : μR-interp (proj 1 zero) (y ∷ []) x
    lemma8 = proj₁ lemma7

    x≡y : x ≡ y
    x≡y = lemma8

    x∷[]≡y∷[] : (x ∷ []) ≡ (y ∷ [])
    x∷[]≡y∷[] = Vec-ext x≡y refl

    v≡y∷[] : v ≡ (y ∷ [])
    v≡y∷[] = ≡-trans v≡x∷[] x∷[]≡y∷[]

    lemma9 : μR-interp succ v 0
    lemma9 = proj₂ (proj₂ lemma5)

    lemma10 : μR-interp succ (y ∷ []) 0
    lemma10 = resp (λ r → μR-interp succ r 0) v≡y∷[] lemma9

    lemma11 : 0 ≡ 1 + y
    lemma11 = lemma10

    proof = 1+n≢0 (≡-sym lemma11)

μR-loop-example-not-PR : ¬ (Is-semantically-PR μR-loop-example)
μR-loop-example-not-PR (f , λx→P[x]≡f[x]) = proof
  where
    P[]≡f[] : μR-interp μR-loop-example [] (PR-interp f [])
    P[]≡f[] = λx→P[x]≡f[x] []

    proof = μR-loop-example-loops (PR-interp f [] , P[]≡f[])


μR-halt-example : μR 0
μR-halt-example = μ-rec zero

μR-halt-example-halts : μR-interp μR-halt-example [] 0
μR-halt-example-halts = refl , (λ _ _ → z≤n)

μR-loop-example2 : μR 2
μR-loop-example2 = μ-rec (comp succ (proj 3 zero ∷ []))

0≢succ-v : {xs : Vec ℕ 1} → ¬ (μR-interp succ xs 0)
0≢succ-v {xs@(x₁ ∷ [])} succ[xs]≡0 = 1+n≢0 (≡-sym succ[xs]≡0)


μR-loop-example2-loops :  (x : Vec ℕ 2) → ¬ (μR-halting (2 , (μR-loop-example2 , x)))
μR-loop-example2-loops x@(x₁ ∷ x₂ ∷ []) (y , f[x]≡y) = 0≢succ-v {proj₁ (proj₁ f[x]≡y)} (proj₂ (proj₂ (proj₁ f[x]≡y)))


μR-K-helper : μR 1
μR-K-helper = prim-rec μR-halt-example μR-loop-example2

μR-K-helper-halts-on-0 : μR-interp μR-K-helper (0 ∷ []) 0
μR-K-helper-halts-on-0 = μR-halt-example-halts

μR-K-helper-loops-on-1 : ¬ (μR-halting (1 , (μR-K-helper , (1 ∷ []))))
μR-K-helper-loops-on-1 (y , f[1]≡y) = μR-loop-example2-loops (1 ∷ (proj₁ f[1]≡y) ∷ []) (y , (proj₂ (proj₂ f[1]≡y)))

{-
{- 
  problem: e : μR 1 × Vec ℕ 1 → ℕ
  but how to get a Vec ℕ 1 from K ?
  need H (e (K , e₂ K))
  where does the e₂ come from ?
  could do... e (K , []) ? but [] : Vec ℕ 0 not Vec ℕ 1
  could do... e (K , (0 ∷ [])) ?

  this is tricky... K needs to actually do the calling somehow...
-}
μR-halting-undecidable : μR-undecidable μR-halting
μR-halting-undecidable dec@(e , (e-bij , (H , (H-complete , H-sound)))) = proof
  where
    K : μR 1
    K = comp μR-K-helper (H ∷ [])

    K = comp μR-K-helper (comp H (e ∷ []) ∷ [])

    K P = comp μR-K-helper (comp H ∷ []) (e (P , (e (P , (0 ∷ [])))))
    K K = comp μR-K-helper (comp H ∷ []) (e (K , (e (K , (0 ∷ [])))))
    
    μR-K-helper (H (e₂ (P , e₁ P)))
    μR-K-helper (H (e₂ (P , e₁ 

    proof
-}

μR-functional-vec : {n k : ℕ} → (gs : Vec (μR n) k) → (xs : Vec ℕ n) → (v₁ v₂ : Vec ℕ k) → fold' gs v₁ xs → fold' gs v₂ xs → v₁ ≡ v₂
μR-functional-vec {n} {0} [] _ [] [] unit unit = refl
μR-functional-vec {n} {suc k} (g ∷ gs) xs (y₁ ∷ ys₁) (y₂ ∷ ys₂) (g[xs]≡y₁ , gs[xs]≡ys₁) (g[xs]≡y₂ , gs[xs]≡ys₂) = Vec-ext y₁≡y₂ ys₁≡ys₂
  where
    y₁≡y₂ : y₁ ≡ y₂
    y₁≡y₂ = μR-functional g xs y₁ y₂ g[xs]≡y₁ g[xs]≡y₂

    ys₁≡ys₂ : ys₁ ≡ ys₂
    ys₁≡ys₂ = μR-functional-vec gs xs ys₁ ys₂ gs[xs]≡ys₁ gs[xs]≡ys₂




μR-halting-undecidable :
  ¬(
    Σ[ e ∈ (μR 1 → ℕ) ] (
      Σ[ H ∈ μR 2 ] (
        (P : μR 1) → 
        (x : Vec ℕ 1) →
          ((μR-interp H ((e P) ∷ x) 0) ⊎ (μR-interp H ((e P) ∷ x) 1))
        × ((μR-interp H ((e P) ∷ x) 1) ↔ (Σ[ y ∈ ℕ ] (μR-interp P x y)))
      )
    )
  )
μR-halting-undecidable (e , (H , H-def)) = proof
  where
    K : μR 1
    K = comp μR-K-helper (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ∷ [])

    lemma1 : (μR-interp H ((e K) ∷ (e K) ∷ []) 0) ⊎ (μR-interp H ((e K) ∷ (e K) ∷ []) 1)
    lemma1 = proj₁ (H-def K ((e K) ∷ []))

    lemma2 : (μR-interp H ((e K) ∷ (e K) ∷ []) 1) ↔ (Σ[ y ∈ ℕ ] (μR-interp K ((e K) ∷ []) y))
    lemma2 = proj₂ (H-def K ((e K) ∷ []))

    lemma3 : ¬ (Σ[ y ∈ ℕ ] (μR-interp K ((e K) ∷ []) y))
    lemma3 (y , K[K]≡y) = subproof
      where
        sublemma1 : μR-interp H ((e K) ∷ (e K) ∷ []) 1
        sublemma1 = (proj₂ lemma2) (y , K[K]≡y)

        sublemma2 : μR-interp K ((e K) ∷ []) y
        sublemma2 = K[K]≡y

        sublemma3 : Σ[ v ∈ Vec ℕ 1 ] (fold' (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ∷ []) v ((e K) ∷ []) × μR-interp μR-K-helper v y)
        sublemma3 = K[K]≡y

        v : Vec ℕ 1
        v = proj₁ sublemma3

        x : ℕ
        x = head v

        xs : Vec ℕ 0
        xs = tail v

        v≡x∷xs : v ≡ (x ∷ xs)
        v≡x∷xs = Vec-ext2 v

        xs≡[] : xs ≡ []
        xs≡[] = Vec-empty xs

        x∷xs≡x∷[] : (x ∷ xs) ≡ (x ∷ [])
        x∷xs≡x∷[] = cong (λ r → x ∷ r) xs≡[]

        v≡x∷[] : v ≡ (x ∷ [])
        v≡x∷[] = ≡-trans v≡x∷xs x∷xs≡x∷[]

        sublemma4 : fold' (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ∷ []) v ((e K) ∷ [])
        sublemma4 = proj₁ (proj₂ sublemma3)

        sublemma5 : fold' (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ∷ []) (x ∷ []) ((e K) ∷ [])
        sublemma5 = resp (λ r → fold' (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ∷ []) r ((e K) ∷ [])) v≡x∷[] sublemma4

        sublemma6 : μR-interp (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ [])) ((e K) ∷ []) x
        sublemma6 = proj₁ sublemma5

        sublemma7 : Σ[ v₂ ∈ Vec ℕ 2 ] (fold' ((proj 1 zero) ∷ (proj 1 zero) ∷ []) v₂ ((e K) ∷ []) × μR-interp H v₂ x)
        sublemma7 = sublemma6

        v₂ : Vec ℕ 2
        v₂ = proj₁ sublemma7

        

        sublemma8 : fold' ((proj 1 zero) ∷ (proj 1 zero) ∷ []) v₂ ((e K) ∷ [])
        sublemma8 = proj₁ (proj₂ sublemma7)

        sublemma9 : fold' ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ((e K) ∷ (e K) ∷ []) ((e K) ∷ [])
        sublemma9 = (refl , (refl , unit))

        v₂≡K∷K∷[] : v₂ ≡ ((e K) ∷ (e K) ∷ [])
        v₂≡K∷K∷[] = μR-functional-vec ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ((e K) ∷ []) v₂ ((e K) ∷ (e K) ∷ []) sublemma8 sublemma9

        sublemma10 : μR-interp H v₂ x
        sublemma10 = proj₂ (proj₂ sublemma7)

        sublemma11 : μR-interp H ((e K) ∷ (e K) ∷ []) x
        sublemma11 = resp (λ r → μR-interp H r x) v₂≡K∷K∷[] sublemma10

        x≡1 : x ≡ 1
        x≡1 = μR-functional H ((e K) ∷ (e K) ∷ []) x 1 sublemma11 sublemma1

        x∷[]≡1∷[] : (x ∷ []) ≡ (1 ∷ [])
        x∷[]≡1∷[] = cong (λ r → r ∷ []) x≡1

        v≡1∷[] : v ≡ (1 ∷ [])
        v≡1∷[] = ≡-trans v≡x∷[] x∷[]≡1∷[]

        sublemma12 :  μR-interp μR-K-helper v y
        sublemma12 = proj₂ (proj₂ sublemma3)

        sublemma13 : μR-interp μR-K-helper (1 ∷ []) y
        sublemma13 = resp (λ r → μR-interp μR-K-helper r y) v≡1∷[] sublemma12
        
        subproof = μR-K-helper-loops-on-1 (y , sublemma13)

    H[K,K]≢1 : ¬ (μR-interp H ((e K) ∷ (e K) ∷ []) 1)
    H[K,K]≢1 H[K,K]≡1 = lemma3 ((proj₁ lemma2) H[K,K]≡1)

    H[K,K]≢0 : ¬ (μR-interp H ((e K) ∷ (e K) ∷ []) 0)
    H[K,K]≢0 H[K,K]≡0 = subproof
      where
        sublemma1 : μR-interp H ((e K) ∷ (e K) ∷ []) 0
        sublemma1 = H[K,K]≡0

        sublemma2 :  ¬ (Σ[ y ∈ ℕ ] (μR-interp K ((e K) ∷ []) y))
        sublemma2 hyp = subsubproof
          where
             subsublemma1 : μR-interp H ((e K) ∷ (e K) ∷ []) 1
             subsublemma1 = (proj₂ lemma2) hyp

             1≡0 : 1 ≡ 0
             1≡0 = μR-functional H ((e K) ∷ (e K) ∷ []) 1 0 subsublemma1 sublemma1
             
             subsubproof = 1+n≢0 1≡0
        sublemma3 : μR-interp K (e K ∷ []) 0
        sublemma3 = subsubproof
          where
            -- μR-interp K (e K ∷ []) 0
            -- μR-interp (comp μR-K-helper (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ∷ [])) (e K ∷ []) 0
            -- Σ[ v ∈ Vec ℕ 1 ] (fold' (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ∷ []) v (e K ∷ []) × (μR-interp μR-K-helper v 0))
            
            -- fold' (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ∷ []) v (e K ∷ [])
            -- μR-interp (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ [])) (e K ∷ []) (head v)
            -- Σ[ v₂ ∈ Vec ℕ 2 ] (fold' ((proj 1 zero) ∷ (proj 1 zero) ∷ []) v₂ (e K ∷ []) × (μR-interp H v₂ (head v)))
            
            -- fold' ((proj 1 zero) ∷ (proj 1 zero) ∷ []) v₂ (e K ∷ [])
            -- fold' ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ((e K) ∷ (e K) ∷ []) (e K ∷ [])
            
            v₂ : Vec ℕ 2
            v₂ = ((e K) ∷ (e K) ∷ [])
            
            subsublemma1 : fold' ((proj 1 zero) ∷ (proj 1 zero) ∷ []) v₂ (e K ∷ [])
            subsublemma1 = refl , (refl , unit)

            v : Vec ℕ 1
            v = (0 ∷ [])

            subsublemma2 : μR-interp H v₂ (head v)
            subsublemma2 = H[K,K]≡0

            subsublemma3 : fold' (comp H ((proj 1 zero) ∷ (proj 1 zero) ∷ []) ∷ []) v (e K ∷ [])
            subsublemma3 = (v₂ , (subsublemma1 , subsublemma2)) , unit

            subsublemma4 : μR-interp μR-K-helper v 0
            subsublemma4 = μR-K-helper-halts-on-0

            
            subsubproof = v , (subsublemma3 , subsublemma4)
        subproof = sublemma2 (0 , sublemma3)

    lemma6 : ¬ ((μR-interp H ((e K) ∷ (e K) ∷ []) 0) ⊎ (μR-interp H ((e K) ∷ (e K) ∷ []) 1))
    lemma6 (inj₁ H[K,K]≡0) = H[K,K]≢0 H[K,K]≡0
    lemma6 (inj₂ H[K,K]≡1) = H[K,K]≢1 H[K,K]≡1
    
    proof = lemma6 lemma1
