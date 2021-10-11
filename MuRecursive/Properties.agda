module MuRecursive.Properties where

open import Basic hiding ([_] ; map ; foldr)
open import Data.Vec using (map ; foldr ; head ; tail)
open import MuRecursive
open import PR
open import Util.Arithmetic
open import Util.Bool
open import Util.Vec renaming (Vec-get to _[_])

{-
 Proof that the μ-recursive functions are actually functions
-}
μR-functional : ∀ { n } (f : μR n) → Functional (μR-interp f)


μR-functional-vec : {n k : ℕ} → (gs : Vec (μR n) k) → (xs : Vec ℕ n) → (v₁ v₂ : Vec ℕ k) → fold[ gs , xs ]= v₁ → fold[ gs , xs ]= v₂ → v₁ ≡ v₂
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

0≢succ-v : {xs : Vec ℕ 1} → ¬ (succ [ xs ]= 0)
0≢succ-v {xs@(x₁ ∷ [])} succ[xs]≡0 = 1+n≢0 (≡-sym succ[xs]≡0)
