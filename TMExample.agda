module TMExample where

open import Agda.Primitive
open import Basic
open import TuringMachine3 using (TM-δ ; δ)

{-
data TM-δ (n m : Nat) : Set where
  δ : Fin n → Fin m → Fin n → Fin m → Bool → TM-δ n m
-}

data TM-δ-ℕ : Set where
  δ : ℕ → ℕ → ℕ → ℕ → Bool → TM-δ-ℕ


parse-Fin : {n : ℕ} → ℕ → Maybe (Fin n)
parse-Fin {n} x =
  dite
  {λ b → Maybe (Fin n)}
  (x lt n)
  (λ case-true → just (fromℕ< (lt→< case-true)))
  (λ case-false → nothing)


Bool→ℕ : Bool → ℕ
Bool→ℕ false = 0
Bool→ℕ true = 1

data DVec {l : Level} : {n : ℕ} → Vec (Set l) n → Set l where
  [] : DVec []
  _∷_ : {n : ℕ} → {A : Set l} → {As : Vec (Set l) n} → A → DVec As → DVec (A ∷ As)

vec-level-max : {n : ℕ} → (sig : Vec Level n) → Level
vec-level-max [] = lzero
vec-level-max (l ∷ ls) = l ⊔ (vec-level-max ls)
  

TM-δ→DVec : {n m : ℕ} → TM-δ n m → DVec ((Fin n) ∷ (Fin m) ∷ (Fin n) ∷ (Fin m) ∷ Bool ∷ [])
TM-δ→DVec {n} {m} (δ a b c d e) = a ∷ b ∷ c ∷ d ∷ e ∷ []

Rel : {n : ℕ} → (sig : Vec Set n) → Set₁
Rel sig = DVec sig → Set

rel : {n : ℕ} → (sig : Vec Set n) → Set
rel sig = DVec sig → Bool

rel-dec : {n : ℕ} → {sig : Vec Set n} → rel sig → Rel sig → Set
rel-dec {n} {sig} r R = (x : DVec sig) → R x ↔ (r x ≡ true)

Rel-example1 : Rel (ℕ ∷ ℕ ∷ [])
Rel-example1 (x ∷ y ∷ []) = x ≤ y

rel-example1 : rel (ℕ ∷ ℕ ∷ [])
rel-example1 (x ∷ y ∷ []) = x le y

rel-dec-example1 : rel-dec rel-example1 Rel-example1
rel-dec-example1 (x ∷ y ∷ []) = (≤→le , le→≤)


sig-Rel : {n : ℕ} → (sig : Vec Set n) → Set₁
sig-Rel sig = DVec (vec-map (λ A → (A → Set)) sig)

sig-rel : {n : ℕ} → (sig : Vec Set n) → Set
sig-rel sig = DVec (vec-map (λ A → (A → Bool)) sig)

sig-rel-holds : {n : ℕ} → {sig : Vec Set n} → sig-rel sig → DVec sig → Bool
sig-rel-holds [] [] = true
sig-rel-holds (r ∷ rs) (x ∷ xs) = (r x) and (sig-rel-holds rs xs)

sig-Rel-holds : {n : ℕ} → {sig : Vec Set n} → sig-Rel sig → DVec sig → Set
sig-Rel-holds [] [] = ⊤
sig-Rel-holds (R ∷ Rs) (x ∷ xs) = (R x) × (sig-Rel-holds Rs xs)


δ-check-rel : (n m : ℕ) → sig-rel (ℕ ∷ ℕ ∷ ℕ ∷ ℕ ∷ [])
δ-check-rel n m =
  (
    (λ x → x lt n)
  ∷ (λ x → x lt m)
  ∷ (λ x → x lt n)
  ∷ (λ x → x lt m)
  ∷ []
  )

δ-check-Rel : (n m : ℕ) → sig-Rel (ℕ ∷ ℕ ∷ ℕ ∷ ℕ ∷ [])
δ-check-Rel n m =
  (
    (λ x → x < n)
  ∷ (λ x → x < m)
  ∷ (λ x → x < n)
  ∷ (λ x → x < m)
  ∷ []
  )

pred-dec : {A : Set} → (r : A → Bool) → (R : A → Set) → Set
pred-dec {A} r R = (a : A) → (R a) ↔ ((r a) ≡ true)

and→× : {b₁ b₂ : Bool} → b₁ and b₂ ≡ true → (b₁ ≡ true) × (b₂ ≡ true)
and→× {true} {true} refl = refl , refl
and→× {true} {false} ()
and→× {false} {_} ()

×→and : {b₁ b₂ : Bool} → (b₁ ≡ true) × (b₂ ≡ true) → b₁ and b₂ ≡ true
×→and {true} {true} _ = refl
×→and {true} {false} (_ , ())
×→and {false} {_} (() , _)

or→⊎ : {b₁ b₂ : Bool} → b₁ or b₂ ≡ true → (b₁ ≡ true) ⊎ (b₂ ≡ true)
or→⊎ {true} {_} refl = inj₁ refl
or→⊎ {false} {true} refl = inj₂ refl
or→⊎ {false} {false} ()

⊎→or : {b₁ b₂ : Bool} → (b₁ ≡ true) ⊎ (b₂ ≡ true) → b₁ or b₂ ≡ true
⊎→or {true} {_} _ = refl
⊎→or {false} {true} _ = refl
⊎→or {false} {false} (inj₁ ())
⊎→or {false} {false} (inj₂ ())

not→¬ : {b : Bool} → (not b ≡ true) → ¬ (b ≡ true)
not→¬ {true} ()
not→¬ {false} _ ()

¬→not : {b : Bool} → ¬ (b ≡ true) → not b ≡ true
¬→not {true} ¬b = ⊥-elim (¬b refl)
¬→not {false} ¬b = refl


and-rel→×-Rel :
  {A B : Set}
  {r₁ : A → Bool} {r₂ : B → Bool}
  {R₁ : A → Set} {R₂ : B → Set} →
  pred-dec r₁ R₁ → pred-dec r₂ R₂ →
  (a : A) → (b : B) →
  (r₁ a) and (r₂ b) ≡ true →
  (R₁ a) × (R₂ b)
and-rel→×-Rel r₁-dec-R₁ r₂-dec-R₂ a b r₁a-and-r₂b = R₁a , R₂b
  where
    r₁a×r₂b = and→× r₁a-and-r₂b
    R₁a = (proj₂ (r₁-dec-R₁ a)) (proj₁ r₁a×r₂b)
    R₂b = (proj₂ (r₂-dec-R₂ b)) (proj₂ r₁a×r₂b)

×-Rel→and-rel  :
  {A B : Set}
  {r₁ : A → Bool} {r₂ : B → Bool}
  {R₁ : A → Set} {R₂ : B → Set} →
  pred-dec r₁ R₁ → pred-dec r₂ R₂ →
  (a : A) → (b : B) →
  (R₁ a) × (R₂ b) →
  (r₁ a) and (r₂ b) ≡ true
×-Rel→and-rel r₁-dec-R₁ r₂-dec-R₂ a b (R₁a , R₂b) = r₁a-and-r₂b
  where
    r₁a-and-r₂b = ×→and (proj₁ (r₁-dec-R₁ a) R₁a , proj₁ (r₂-dec-R₂ b) R₂b)

sig-rel-dec : {n : ℕ} → {sig : Vec Set n} → sig-rel sig → sig-Rel sig → Set
sig-rel-dec {0} {[]} [] [] = ⊤
sig-rel-dec {suc n} {A ∷ As} (r ∷ rs) (R ∷ Rs) = (pred-dec r R) × (sig-rel-dec rs Rs)

δ-check-dec : (n m : ℕ) → sig-rel-dec (δ-check-rel n m) (δ-check-Rel n m)
δ-check-dec n m =
  (λ x → (<→lt {x} {n} , lt→< {x} {n})) ,
  (λ x → (<→lt {x} {m} , lt→< {x} {m})) ,
  (λ x → (<→lt {x} {n} , lt→< {x} {n})) ,
  (λ x → (<→lt {x} {m} , lt→< {x} {m})) ,
  unit

sig-rel-dec-holds : {n : ℕ} {sig : Vec Set n} (r : sig-rel sig) (R : sig-Rel sig) → sig-rel-dec r R → (x : DVec sig) → sig-rel-holds r x ≡ true → sig-Rel-holds R x
sig-rel-dec-holds {0} {[]} [] [] unit [] refl = unit
sig-rel-dec-holds {suc n} {A ∷ As} (r ∷ rs) (R ∷ Rs) (r-dec-R , rs-dec-Rs) (x ∷ xs) rx-and-rs-xs = Rx , Rs-xs
  where
    rx×rs-xs : (r x ≡ true) × (sig-rel-holds rs xs ≡ true)
    rx×rs-xs = and→× rx-and-rs-xs

    rx = proj₁ rx×rs-xs
    rs-xs = proj₂ rx×rs-xs
    
    Rx = (proj₂ (r-dec-R x)) rx
    Rs-xs = sig-rel-dec-holds {n} {As} rs Rs rs-dec-Rs xs rs-xs


δ-check-rel→δ-check-Rel : {n m : ℕ} → (x : DVec (ℕ ∷ ℕ ∷ ℕ ∷ ℕ ∷ [])) → sig-rel-holds (δ-check-rel n m) x ≡ true → sig-Rel-holds (δ-check-Rel n m) x
δ-check-rel→δ-check-Rel {n} {m} x rx = sig-rel-dec-holds (δ-check-rel n m) (δ-check-Rel n m) (δ-check-dec n m) x rx

{-
  (
    (λ x → x lt n) : ℕ → Bool 
  ∷ (λ x → x lt m)
  ∷ (λ x → x lt n)
  ∷ (λ x → x lt m)
  ∷ []
  )
-}

TM-δ-ℕ→DVec : TM-δ-ℕ → DVec (ℕ ∷ ℕ ∷ ℕ ∷ ℕ ∷ [])
TM-δ-ℕ→DVec (δ a b c d _) = a ∷ b ∷ c ∷ d ∷ []

parse-TM-δ-true : {n m : ℕ} → (x : TM-δ-ℕ) → (sig-rel-holds (δ-check-rel n m) (TM-δ-ℕ→DVec x)) ≡ true → TM-δ n m
parse-TM-δ-true {n} {m} (δ a b c d x) a-b-c-d = TM-δ.δ a' b' c' d' x
  where
    [abcd] = and→× a-b-c-d
    a-lt-n = proj₁ [abcd]
    [bcd] = and→× (proj₂ [abcd])
    b-lt-m = proj₁ [bcd]
    [cd] = and→× (proj₂ [bcd])
    c-lt-n = proj₁ [cd]
    [d] = and→× (proj₂ [cd])
    d-lt-m = proj₁ [d]
    a' = fromℕ< (lt→< a-lt-n)
    b' = fromℕ< (lt→< b-lt-m)
    c' = fromℕ< (lt→< c-lt-n)
    d' = fromℕ< (lt→< d-lt-m)


parse-TM-δ : {n m : ℕ} → TM-δ-ℕ → Maybe (TM-δ n m)
parse-TM-δ {n} {m} x =
  dite
  {λ b → Maybe (TM-δ n m)}
  (sig-rel-holds (δ-check-rel n m) (TM-δ-ℕ→DVec x))
  (λ case-true → just (parse-TM-δ-true x case-true))
  (λ case-false → nothing)


Maybe-∷ : {A : Set} → Maybe A → Maybe (List A) → Maybe (List A)
Maybe-∷ (just a) (just as) = just (a ∷ as)
Maybe-∷ nothing _ = nothing
Maybe-∷ _ nothing = nothing

parse-TM : {n m : ℕ} → List TM-δ-ℕ → Maybe (List (TM-δ n m))
parse-TM [] = just []
parse-TM {n} {m} (x ∷ xs) = Maybe-∷ (parse-TM-δ x) (parse-TM xs)

{-
  copies the first string of bits to the cells immediately after it
  bb1010bbbbbb --> bb1010b1010b

  expects at least 2 b's at the beginning of the tape
  expects the tape to only contain b, 0 and 1
  expects there to actually be a bit string: it will loop on blank tape looking for it
-}
tm-table-21,6-copy-bits : List (TM-δ 21 6)
tm-table-21,6-copy-bits =
    -- mark the beginning of the tape
    (δ q₀ b q₁ sₓ R)
    
    -- scan to the beginning of the bit string;
  ∷ (δ q₁ b q₁ b R)
  ∷ (δ q₁ s₀ q₂ s₀ L)
  ∷ (δ q₁ s₁ q₂ s₁ L)

    -- mark the cell immediately before the beginning of the bit string
  ∷ (δ q₂ b  q₃  u R)

    -- scan to the end of the bit string;
    -- mark the cell immediately after it
  ∷ (δ q₃ s₀ q₃ s₀ R)
  ∷ (δ q₃ s₁ q₃ s₁ R)
  ∷ (δ q₃ b  q₄ t  L)

    -- check cell immediately preceding t; if u then done.
  ∷ (δ q₄ s₀ q₅ s₀ L)
  ∷ (δ q₄ s₁ q₆ s₁ L)
  ∷ (δ q₄ u  q₁₇ u R)

    -- scan back to the u mark
    -- track last seen bit in internal state
    -- when reaching u, replace it with the stored bit (0)
  ∷ (δ q₅ s₀ q₅ s₀ L)
  ∷ (δ q₅ s₁ q₆ s₁ L)
  ∷ (δ q₅ u  q₈ s₀ R)

    -- replace that stored bit with u
  ∷ (δ q₈ s₀ q₉ u  R)

    -- scan back to the end of the tape to add a 0 to the end
  ∷ (δ q₉ s₀ q₉ s₀ R)
  ∷ (δ q₉ s₁ q₉ s₁ R)
  ∷ (δ q₉ t  q₉ t  R)
  ∷ (δ q₉ b  q₁₀ s₀ L)

    -- scan back to the u mark
    -- track last seen bit in internal state
    -- when reaching u, replace it with the stored bit (1)
  ∷ (δ q₆ s₀ q₅ s₀ L)
  ∷ (δ q₆ s₁ q₆ s₁ L)
  ∷ (δ q₆ u  q₁₁ s₁ R)

    -- replace that stored bit (1) with u
  ∷ (δ q₁₁ s₁ q₁₂ u R)

    -- scan back to the end of the tape to add a 1 to the end
  ∷ (δ q₁₂ s₀ q₁₂ s₀ R)
  ∷ (δ q₁₂ s₁ q₁₂ s₁ R)
  ∷ (δ q₁₂ t  q₁₂ t  R)
  ∷ (δ q₁₂ b  q₁₀ s₁ L)

    -- scan back to the t mark
  ∷ (δ q₁₀ s₀ q₁₀ s₀ L)
  ∷ (δ q₁₀ s₁ q₁₀ s₁ L)
  ∷ (δ q₁₀ t  q₄  t  L)

    -- shift the original back into position and erase the t, sₓ and u
  ∷ (δ q₁₃ s₀ q₁₄ u R)
  ∷ (δ q₁₃ s₁ q₁₅ u R)
  ∷ (δ q₁₃ b  q₁₈ b R)
  ∷ (δ q₁₃ sₓ q₁₈ sₓ R)
  ∷ (δ q₁₄ u  q₁₆ s₀ L)
  ∷ (δ q₁₅ u  q₁₆ s₁ L)
  ∷ (δ q₁₆ u  q₁₃ u L)
  
    -- erase the t
  ∷ (δ q₁₇ t  q₁₇ b L)
  ∷ (δ q₁₇ u  q₁₃ u L)
  ∷ (δ q₁₈ u  q₁₉ b L)
  ∷ (δ q₁₉ b  q₁₉ b L)
  
    -- erase the sₓ and halt
  ∷ (δ q₁₉ sₓ q₂₀ b L)
  ∷ []
  where
    q₀ = raise 20 (fromℕ 0)
    q₁ = raise 19 (fromℕ 1)
    q₂ = raise 18 (fromℕ 2)
    q₃ = raise 17 (fromℕ 3)
    q₄ = raise 16 (fromℕ 4)
    q₅ = raise 15 (fromℕ 5)
    q₆ = raise 14 (fromℕ 6)
    q₇ = raise 13 (fromℕ 7)
    q₈ = raise 12  (fromℕ 8)
    q₉ = raise 11  (fromℕ 9)
    q₁₀ = raise 10 (fromℕ 10)
    q₁₁ = raise 9 (fromℕ 11)
    q₁₂ = raise 8 (fromℕ 12)
    q₁₃ = raise 7 (fromℕ 13)
    q₁₄ = raise 6 (fromℕ 14)
    q₁₅ = raise 5 (fromℕ 15)
    q₁₆ = raise 4 (fromℕ 16)
    q₁₇ = raise 3 (fromℕ 17)
    q₁₈ = raise 2 (fromℕ 18)
    q₁₉ = raise 1 (fromℕ 19)
    q₂₀ = raise 0 (fromℕ 20)
    
    
    b = zero
    s₀ = suc zero
    s₁ = suc (suc zero)
    sₓ = suc (suc (suc zero))
    t = suc (suc (suc (suc zero)))
    u = suc (suc (suc (suc (suc zero))))
    
    R = true
    L = false
