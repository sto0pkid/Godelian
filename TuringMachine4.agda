module TuringMachine4 where

open import Basic hiding (_^_ ; raise ; list-product ; filter) renaming (func-rep to _^_)
open import Data.Nat.Base using (NonZero)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary.Decidable.Core using (False)

data TM-δ : Set where
  δ : ℕ → ℕ → ℕ → ℕ → Bool → TM-δ

TM : Set
TM = List TM-δ

read : ℕ → List ℕ → ℕ
read x l = get-default 0 l x

δ-match : ℕ → ℕ → TM-δ → Bool
δ-match state symbol (δ x y _ _ _) = (state eq x) and (symbol eq y)


record TM-configuration : Set where
  field
    state : ℕ
    tape : List ℕ
    pos : ℕ
    halted : Bool

apply-δ : TM-configuration → Maybe TM-δ → TM-configuration
apply-δ config nothing =
  record{
    state  = state
  ; tape   = tape
  ; pos    = pos
  ; halted = true
  }
  where
    open TM-configuration config
apply-δ config (just (δ _ _ new-state symbol lr)) =
  record{
    state  = new-state
  ; tape   = new-tape
  ; pos    = new-pos
  ; halted = halted
  }
  where
    open TM-configuration config

    new-tape = set tape pos symbol
    new-pos = if lr then (suc pos) else (pred pos)

step : TM → TM-configuration → TM-configuration
step M config = apply-δ config (find (δ-match state (read pos tape)) M)
  where
    open TM-configuration config

start-state : List ℕ → TM-configuration
start-state tape =
  record{
    state  = 0
  ; tape   = tape
  ; pos    = 0
  ; halted = false
  }

run : TM → ℕ → List ℕ → TM-configuration
run M n tape = ((step M) ^ n) (start-state tape)

raise-δ : ℕ → TM-δ → TM-δ
raise-δ n (δ in-state in-symbol out-state out-symbol lr) = δ (n + in-state) in-symbol (n + out-state) out-symbol lr

raise : ℕ → TM → TM
raise n M = map (raise-δ n) M


max-state : TM → ℕ
max-state M = list-max (map f M)
  where
    f : TM-δ → ℕ
    f (δ in-state _ out-state _ _) = max in-state out-state

max-symbol : TM → ℕ
max-symbol M = list-max (map f M)
  where
    f : TM-δ → ℕ
    f (δ _ in-symbol _ out-symbol _) = max in-symbol out-symbol


list-product : {A B : Set} → List A → List B → List (A × B)
list-product []       _  = []
list-product (a ∷ as) l₂ = ((map (λ x → a , x)) l₂) ++ (list-product as l₂)

filter : {A : Set} → (A → Bool) → List A → List A
filter P [] = []
filter P (x ∷ xs) = if (P x) then (x ∷ (filter P xs)) else (filter P xs)

make-switch : ℕ → ℕ × ℕ → TM-δ
make-switch n (state , symbol) = δ state symbol n symbol true

δ-filter : TM → ℕ × ℕ → Bool
δ-filter M (state , symbol) = not (match (δ-match state symbol) M)


fix : TM → TM
fix M = M ++ (map (make-switch #states) (filter (δ-filter M) inputs))
  where
    #states = 1 + (max-state M)
    #symbols = 1 + (max-symbol M)
    
    states = range #states
    symbols = range #symbols

    inputs : List (ℕ × ℕ)
    inputs = list-product states symbols


{-
  Sequences the actions of two Turing machines

  Each state s in M₁ will correspond to the state s in seq M₁ M₂
  Each state s in M₂ will correspond to the state (1 + (max-state M₁) + s)  in seq M₁ M₂

  In particular state 0 in M₂, the start state of M₂, will correspond to the state (1 + (max-state M₁)) in seq M₁ M₂

  For any (state , symbol) pair for which M₁ would halt, a transition (state , symbol) -> ((1 + (max-state M₁)) , symbol , R) will be added
  
  NOTE:
   * for any input tape for which M₁ loops, seq M₁ M₂ will loop and in particular the action corresponding to M₂ will never run, but
     this is expected behavior.
   * in particular, if there are no (state , symbol) input pairs for which M₁ halts, then the action corresponding to M₂ will never run
     on any input, and all the states corresponding to states of M₂ will be inaccessible. This is still the intended semantics.
  
-}
seq : TM → TM → TM
seq M₁ M₂ = (fix M₁) ++ (raise (1 + (max-state M₁)) M₂)

example1 : TM
example1 =
    (δ 0 0 0 0 true)
  ∷ (δ 1 0 1 0 true)
  ∷ (δ 1 0 0 1 true)
  ∷ []

raise-config : (n : ℕ) → TM-configuration → TM-configuration
raise-config n config =
  record{
    state = n + state
  ; pos = pos
  ; tape = tape
  ; halted = halted
  }
  where
    open TM-configuration config



raise-δ-lemma : (n state symbol : ℕ) (transition : TM-δ) → δ-match state symbol transition ≡ δ-match (n + state) symbol (raise-δ n transition)
raise-δ-lemma 0 _ _ (δ _ _ _ _ _) = refl
raise-δ-lemma (suc n) state symbol transition@(δ a b c d e) = raise-δ-lemma n state symbol transition


raise-find-lemma : (M : TM) (n state symbol : ℕ) → Maybe-map (raise-δ n) (find (δ-match state symbol) M) ≡ find (δ-match (n + state) symbol) (raise n M)
raise-find-lemma M n state symbol = find-preserve (δ-match state symbol) (δ-match (n + state) symbol) (raise-δ n) (raise-δ-lemma n state symbol) M



raise-apply-lemma : (config : TM-configuration) (action : Maybe TM-δ) (n : ℕ) → raise-config n (apply-δ config action) ≡ apply-δ (raise-config n config) (Maybe-map (raise-δ n) action)
raise-apply-lemma _ nothing _ = refl
raise-apply-lemma _ (just (δ _ _ _ _ _)) n = refl

raise-tape-lemma : (config : TM-configuration) (n : ℕ) → TM-configuration.tape (raise-config n config) ≡ TM-configuration.tape config
raise-tape-lemma config n = refl


raise-step-lemma : (M : TM) (n : ℕ) (config : TM-configuration) → raise-config n (step M config) ≡ step (raise n M) (raise-config n config)
raise-step-lemma M n config =
  raise-config n (step M config)

    ≡⟨ cong (raise-config n) refl ⟩
    
  raise-config n (apply-δ config (find (δ-match state (read pos tape)) M))

    ≡⟨ raise-apply-lemma config (find (δ-match state (read pos tape)) M) n ⟩

  apply-δ (raise-config n config) (Maybe-map (raise-δ n) (find (δ-match state (read pos tape)) M))

    ≡⟨ cong (apply-δ (raise-config n config)) (raise-find-lemma M n state (read pos tape)) ⟩

  step (raise n M) (raise-config n config)

    ∎
  where
    open TM-configuration config
    open PropEq.≡-Reasoning


raise-equivalence : (M : TM) (n : ℕ) (config : TM-configuration) (steps : ℕ) → raise-config n (((step M) ^ steps) config) ≡ ((step (raise n M)) ^ steps) (raise-config n config)
raise-equivalence M n config 0 = refl
raise-equivalence M n config (suc s) =
  raise-config n (((step M) ^ (1 + s)) config)                        ≡⟨  refl ⟩
  raise-config n ((step M) (((step M) ^ s) config))                   ≡⟨ raise-step-lemma M n (((step M) ^ s) config) ⟩
  step (raise n M) (raise-config n (((step M) ^ s) config))           ≡⟨ cong (step (raise n M)) (raise-equivalence M n config s) ⟩
  step (raise n M) (((step (raise n M)) ^ s) (raise-config n config)) ≡⟨ refl ⟩
  ((step (raise n M)) ^ (1 + s)) (raise-config n config)              ∎
  where
    open PropEq.≡-Reasoning



list-product-length : (n m : ℕ) → length (list-product (range n) (range m)) ≡ n * m
list-product-length 0 _ = refl
list-product-length (suc n) m = -- proof
  length (list-product (range (1 + n)) (range m))

    ≡⟨ refl ⟩
    
  length (((map (λ x → n , x)) (range m)) ++ (list-product (range n) (range m)))

    ≡⟨ length-++ ((map (λ x → n , x)) (range m)) ⟩
    
  length  ((map (λ x → n , x)) (range m)) + length (list-product (range n) (range m))

    ≡⟨ cong (λ y → y + length (list-product (range n) (range m))) (≡-trans (length-map (λ x → n , x) (range m)) (length-range m)) ⟩

  m + length (list-product (range n) (range m))

    ≡⟨ cong (λ y → m + y) (list-product-length n m) ⟩
    
  m + (n * m)

    ≡⟨ refl ⟩
    
  (1 + n) * m

    ∎
  where
    open PropEq.≡-Reasoning



product-index-lemma : {n m x y : ℕ} → x < n → y < m → y + (x * m) < length (list-product (range n) (range m))
product-index-lemma {n} {m} {x} {y} x<n y<m = begin-strict
  y + (x * m)                                 <⟨ offset-lemma n m x y x<n y<m ⟩
  n * m                                       ≡⟨ ≡-sym (list-product-length n m) ⟩
  length (list-product (range n) (range m))   ∎
  where
    open ≤-Reasoning


_⊗_ : {A B : Set} → List A → List B → List (A × B)
_⊗_ = list-product

lookup<-lemma : {A : Set} (l₁ l₂ : List A) (x : ℕ) → (x < length l₁) → (l₁ ++ l₂) [ x ]? ≡ l₁ [ x ]?
lookup<-lemma []          _  _    ()
lookup<-lemma (x ∷ xs)    _  0    _             = refl
lookup<-lemma (x ∷ xs) l₂ (suc n) (s≤s n<|xs|)  = lookup<-lemma xs l₂ n n<|xs|

lookup-map-lemma : {A B : Set} (f : A → B) (l : List A) (n : ℕ) → Maybe-map f (l [ n ]?) ≡ (map f l) [ n ]?
lookup-map-lemma f []       _       = refl
lookup-map-lemma f (x ∷ xs) 0       = refl
lookup-map-lemma f l@(x ∷ xs) (suc n) = lookup-map-lemma f xs n

lookup+-lemma : {A : Set} (l₁ l₂ : List A) (n : ℕ) → (l₁ ++ l₂) [ ((length l₁) + n) ]? ≡ l₂ [ n ]?
lookup+-lemma []       l₂ n = refl
lookup+-lemma (x ∷ xs) l₂ n = lookup+-lemma xs l₂ n




product-lookup : {n m x y : ℕ} → (x<n : x < n) → (y<m : y < m) → ((range n) ⊗ (range m)) [ (y + (x * m)) ]? ≡ just (n - (1 + x) , m - (1 + y))
product-lookup {n = 0} ()
product-lookup {n = suc n} {m = 0} _ ()
product-lookup {suc n} {suc m} {0} {0} 0<1+n 0<1+m = refl
product-lookup {suc n} {suc m} {0} {suc y} 0<1+n 1+y<1+m = proof
  where
    lemma : (1 + y) < (length (map (λ x → n , x) (range (1 + m))))
    lemma = begin-strict
      1 + y                                          <⟨ 1+y<1+m ⟩
      1 + m                                          ≡⟨ ≡-sym (length-range (1 + m)) ⟩
      length (range (1 + m))                         ≡⟨ ≡-sym (length-map (λ x → n , x) (range (1 + m))) ⟩
      (length (map (λ x → n , x) (range (1 + m))))  ∎
      where
        open ≤-Reasoning

    lemma2 : (1 + y) < (length (range (1 + m)))
    lemma2 = begin-strict
      1 + y                     <⟨ 1+y<1+m ⟩
      1 + m                     ≡⟨ ≡-sym (length-range (1 + m)) ⟩
      length (range (1 + m))    ∎
      where
        open ≤-Reasoning


    proof : ((range (1 + n)) ⊗ (range (1 + m))) [ ((1 + y) + (0 * m)) ]? ≡ just (n , ((1 + m) - (2 + y)))
    proof =
      ((range (1 + n)) ⊗ (range (1 + m))) [ ((1 + y) + (0 * m)) ]?

        ≡⟨ cong (λ z → ((range (1 + n)) ⊗ (range (1 + m))) [ z ]?) (+-identityʳ (1 + y)) ⟩

      ((range (1 + n)) ⊗ (range (1 + m))) [ (1 + y) ]?

        ≡⟨ lookup<-lemma (map (λ x → n , x) (range (1 + m))) ((range n) ⊗ (range (1 + m))) (1 + y) lemma ⟩

      ((map (λ x → n , x) (range (1 + m))) [ (1 + y) ]?)

        ≡⟨ ≡-sym (lookup-map-lemma (λ x → n , x) (range (1 + m)) (1 + y)) ⟩

      Maybe-map (λ x → n , x) ((range (1 + m)) [ (1 + y) ]?)

        ≡⟨ cong (Maybe-map (λ x → n , x)) (range-lookup? {1 + m} {1 + y} lemma2) ⟩

      just (n , ((1 + m) - (2 + y)))

        ∎
      where
        open PropEq.≡-Reasoning
product-lookup {suc n} {suc m} {suc x} {0} 1+x<1+n@(s≤s x<n) 0<1+m = proof
  where
    length-lemma : (1 + m) ≡ length (map (λ x → n , x) (range (1 + m)))
    length-lemma =
      1 + m                                        ≡⟨ ≡-sym (length-range (1 + m)) ⟩
      length (range (1 + m))                       ≡⟨ ≡-sym (length-map (λ x → n , x) (range (1 + m))) ⟩
      length (map (λ x → n , x) (range (1 + m)))  ∎
      where
        open PropEq.≡-Reasoning

    proof :
        ((range (1 + n)) ⊗ (range (1 + m))) [ 0 + ((1 + x) * (1 + m)) ]?
      ≡ (just ((1 + n) - (2 + x) , (1 + m) - 1))
    proof =
      ((range (1 + n)) ⊗ (range (1 + m))) [ 0 + ((1 + x) * (1 + m)) ]?

        ≡⟨ cong (λ z → ((map (λ x → n , x) (range (1 + m))) ++ ((range n) ⊗ (range (1 + m)))) [ z + x * (1 + m) ]?) length-lemma ⟩ 

      ((map (λ x → n , x) (range (1 + m))) ++ ((range n) ⊗ (range (1 + m)))) [ (length (map (λ x → n , x) (range (1 + m)))) + x * (1 + m) ]?

        ≡⟨ lookup+-lemma (map (λ x → n , x) (range (1 + m))) ((range n) ⊗ (range (1 + m))) (x * (1 + m)) ⟩
        
      ((range n) ⊗ (range (1 + m))) [ x * (1 + m) ]?

        ≡⟨ product-lookup {n} {1 + m} {x} {0} x<n 0<1+m ⟩

      (just ((1 + n) - (2 + x) , (1 + m) - 1))
      
        ∎
        where
          open PropEq.≡-Reasoning
product-lookup {suc n} {suc m} {suc x} {suc y} 1+x<1+n@(s≤s x<n) 1+y<1+m = proof
  where
    length-lemma : (1 + m) ≡ length (map (λ x → n , x) (range (1 + m)))
    length-lemma =
      1 + m                                        ≡⟨ ≡-sym (length-range (1 + m)) ⟩
      length (range (1 + m))                       ≡⟨ ≡-sym (length-map (λ x → n , x) (range (1 + m))) ⟩
      length (map (λ x → n , x) (range (1 + m)))  ∎
      where
        open PropEq.≡-Reasoning


    index-lemma :
        (1 + y) + ((1 + x) * (1 + m))
      ≡ (1 + m) + ((1 + y) + (x * (1 + m)))
    index-lemma =
      (1 + y) + ((1 + x) * (1 + m))         ≡⟨ refl ⟩
      (1 + y) + ((1 + m) + (x * (1 + m)))   ≡⟨ ≡-sym (+-assoc (1 + y) (1 + m) (x * (1 + m))) ⟩
      ((1 + y) + (1 + m)) + (x * (1 + m))   ≡⟨ cong (λ z → z + (x * (1 + m))) (+-comm (1 + y) (1 + m)) ⟩
      ((1 + m) + (1 + y)) + (x * (1 + m))   ≡⟨ +-assoc (1 + m) (1 + y) (x * (1 + m)) ⟩
      (1 + m) + ((1 + y) + (x * (1 + m)))   ∎
      where
        open PropEq.≡-Reasoning
        
    proof :
        ((range (1 + n)) ⊗ (range (1 + m))) [ (1 + y) + ((1 + x) * (1 + m)) ]?
      ≡ just (n - (1 + x) , (1 + m) - (2 + y))
    proof =
      ((range (1 + n)) ⊗ (range (1 + m))) [ (1 + y) + ((1 + x) * (1 + m)) ]?

        ≡⟨ cong (λ z → ((range (1 + n)) ⊗ (range (1 + m))) [ z ]?) index-lemma ⟩ 

      ((range (1 + n)) ⊗ (range (1 + m))) [ (1 + m) + ((1 + y) + (x * (1 + m))) ]?

        ≡⟨ cong (λ z → ((range (1 + n)) ⊗ (range (1 + m))) [ z + ((1 + y) + (x * (1 + m))) ]?) length-lemma ⟩

      ((range (1 + n)) ⊗ (range (1 + m))) [ (length (map (λ x → n , x) (range (1 + m)))) + ((1 + y) + (x * (1 + m))) ]?

        ≡⟨ lookup+-lemma (map (λ x → n , x) (range (1 + m))) ((range n) ⊗ (range (1 + m))) ((1 + y) + (x * (1 + m)))  ⟩ 

      ((range n) ⊗ (range (1 + m))) [ (1 + y) + (x * (1 + m)) ]?

        ≡⟨ product-lookup {n} {1 + m} {x} {1 + y} x<n 1+y<1+m ⟩

      just (n - (1 + x) , (1 + m) - (2 + y))
      
        ∎
      where
        open PropEq.≡-Reasoning


sub<-lemma2 : {n x : ℕ} → x < n → n - (1 + x) < n
sub<-lemma2 {0}     {_}    ()
sub<-lemma2 {suc n} {0}     _         = n<1+n n
sub<-lemma2 {suc n} {suc x} (s≤s x<n) = begin-strict
  (1 + n) - (2 + x)   ≡⟨ refl ⟩
  n - (1 + x)         <⟨ sub<-lemma2 x<n ⟩
  n                   <⟨ n<1+n n ⟩
  1 + n               ∎
  where
    open ≤-Reasoning

{-proof
  where
    x<n → n - (1 + x) < n 
    proof
  -}

0-x≡0 : (x : ℕ) → 0 - x ≡ 0
0-x≡0 0 = refl
0-x≡0 (suc x) = refl

sub-assoc : (x y z : ℕ) → x - (y + z) ≡ (x - y) - z
sub-assoc 0 y z =
  0 - (y + z)   ≡⟨ 0-x≡0 (y + z) ⟩
  0             ≡⟨ ≡-sym (0-x≡0 z) ⟩
  0 - z         ≡⟨ ≡-sym (cong (λ w → w - z) (0-x≡0 y)) ⟩
  (0 - y) - z   ∎
  where
    open PropEq.≡-Reasoning
sub-assoc (suc x) 0 z = cong (λ w → w - z) refl 
sub-assoc (suc x) (suc y) z = sub-assoc x y z

sub-suc-lemma3 : (x y : ℕ) → y ≤ x → (1 + x) - y ≡ 1 + (x - y)
sub-suc-lemma3 x       0       _                  = refl
sub-suc-lemma3 0       (suc y) ()
sub-suc-lemma3 (suc x) (suc y) 1+y≤1+x@(s≤s y≤x)  = sub-suc-lemma3 x y y≤x

x-y≤x : (x y : ℕ) → x - y ≤ x
x-y≤x x       0       = ≤-refl
x-y≤x 0       (suc y) = z≤n
x-y≤x (suc x) (suc y) = begin
  (1 + x) - (1 + y) ≡⟨ refl ⟩
  x - y             ≤⟨ x-y≤x x y ⟩
  x                 ≤⟨ n≤1+n x ⟩
  1 + x             ∎
  where
    open ≤-Reasoning


sub<-lemma3 : (x y z : ℕ) → y ≤ x → y - z ≤ x
sub<-lemma3 x y z y≤x = begin
  y - z   ≤⟨ x-y≤x y z ⟩
  y       ≤⟨ y≤x ⟩
  x       ∎
  where
    open ≤-Reasoning


sub-assoc2 : (x y z : ℕ) → z ≤ y → y ≤ x → x - (y - z) ≡ (x - y) + z
sub-assoc2 0       0      0       z≤n z≤n = refl
sub-assoc2 _       0      (suc z) ()
sub-assoc2 0       (suc y) _      _   ()
sub-assoc2 (suc x) y       0      0≤y y≤1+x =
  (1 + x) - (y - 0)   ≡⟨ refl ⟩
  (1 + x) - y         ≡⟨ ≡-sym (+-identityʳ ((1 + x) - y)) ⟩
  ((1 + x) - y) + 0   ∎
  where
    open PropEq.≡-Reasoning
sub-assoc2 (suc x) (suc y) (suc z) 1+z≤1+y@(s≤s z≤y) 1+y≤1+x@(s≤s y≤x) =
  (1 + x) - ((1 + y) - (1 + z))  ≡⟨ refl ⟩
  (1 + x) - (y - z)              ≡⟨ sub-suc-lemma3 x (y - z) y-z≤x ⟩ 
  1 + (x - (y - z))              ≡⟨ cong suc (sub-assoc2 x y z z≤y y≤x) ⟩
  1 + ((x - y) + z)              ≡⟨ +-comm 1 ((x - y) + z) ⟩
  ((x - y) + z) + 1              ≡⟨ +-assoc (x - y) z 1 ⟩
  (x - y) + (z + 1)              ≡⟨ cong (λ w → (x - y) + w) (+-comm z 1) ⟩
  (x - y) + (1 + z)              ≡⟨ refl ⟩
  ((1 + x) - (1 + y)) + (1 + z)   ∎
  where
    open PropEq.≡-Reasoning
    
    y-z≤x : (y - z) ≤ x
    y-z≤x = ≤-trans (x-y≤x y z) y≤x

pred≤-lemma : {x y : ℕ} → x < y → x ≤ (y - 1)
pred≤-lemma {_} {0} ()
pred≤-lemma {x} {suc y} x<1+y@(s≤s x≤y) = x≤y

x-x≡0 : (x : ℕ) → x - x ≡ 0
x-x≡0 0 = refl
x-x≡0 (suc x) = x-x≡0 x


product-lookup2 :  {n m x y : ℕ} → (x<n : x < n) → (y<m : y < m) → ((range n) ⊗ (range m)) [ ((m - (1 + y)) + ((n - (1 + x)) * m)) ]? ≡ just (x , y)
product-lookup2 {n} {m} {x} {y} x<n y<m = proof
  where
    n-[1+x]<n : n - (1 + x) < n
    n-[1+x]<n = sub<-lemma2 x<n

    m-[1+y]<m : m - (1 + y) < m
    m-[1+y]<m = sub<-lemma2 y<m

    lemma1 : ((range n) ⊗ (range m)) [ ((m - (1 + y)) + ((n - (1 + x)) * m)) ]? ≡ just (n - (1 + (n - (1 + x))) , m - (1 + (m - (1 + y))))
    lemma1 = product-lookup {n} {m} {n - (1 + x)} {m - (1 + y)} n-[1+x]<n m-[1+y]<m

    

    lemma2 : (a b : ℕ) → a < b → b - (1 + (b - (1 + a))) ≡ a
    lemma2 a b a<b =
      b - (1 + (b - (1 + a)))  ≡⟨ sub-assoc b 1 (b - (1 + a)) ⟩
      (b - 1) - (b - (1 + a))  ≡⟨ cong (λ w → (b - 1) - w) (sub-assoc b 1 a) ⟩
      (b - 1) - ((b - 1) - a)  ≡⟨ sub-assoc2 (b - 1) (b - 1) a (pred≤-lemma a<b) ≤-refl ⟩
      ((b - 1) - (b - 1)) + a  ≡⟨ cong (λ w → w + a) (x-x≡0 (b - 1)) ⟩
      0 + a                    ≡⟨ refl ⟩
      a                        ∎
      where
        open PropEq.≡-Reasoning

    lemma3 : just (n - (1 + (n - (1 + x))) , m - (1 + (m - (1 + y)))) ≡ just (x , y)
    lemma3 =
      just (n - (1 + (n - (1 + x))) , m - (1 + (m - (1 + y))))   ≡⟨ cong (λ w → just (w , (m - (1 + (m - (1 + y)))))) (lemma2 x n x<n) ⟩ 
      just (x , m - (1 + (m - (1 + y))))                         ≡⟨ cong (λ w → just (x , w)) (lemma2 y m y<m) ⟩
      just (x , y)                                               ∎
      where
        open PropEq.≡-Reasoning

    proof = ≡-trans lemma1 lemma3

product-complete : {n m x y : ℕ} → (x < n) → (y < m) → Σ[ i ∈ ℕ ] (((range n) ⊗ (range m)) [ i ]? ≡ just (x , y))
product-complete {n} {m} {x} {y} x<n y<m = ((m - (1 + y)) + ((n - (1 + x)) * m)) , product-lookup2 x<n y<m


just-injective : {A : Set} (a₁ a₂ : A) → just a₁ ≡ just a₂ → a₁ ≡ a₂
just-injective _ _ refl = refl


filter-index-lemma : {A : Set} (P : A → Bool) (l : List A) (i : ℕ) (a : A) → l [ i ]? ≡ just a → P a ≡ true → Σ[ j ∈ ℕ ] ((filter P l) [ j ]? ≡ just a)
filter-index-lemma _ []       i _ ()
filter-index-lemma P l@(x ∷ xs) 0 a l[0]≡a Pa≡true = 0 , proof
  where
    lemma1 : P x ≡ true
    lemma1 = ≡-trans (cong P (just-injective x a l[0]≡a)) Pa≡true

    lemma2 : filter P l ≡ (x ∷ (filter P xs))
    lemma2 = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) lemma1

    lemma3 : (filter P l) [ 0 ]? ≡ (just x)
    lemma3 = cong (λ w → w [ 0 ]?) lemma2
    
    proof = ≡-trans lemma3 l[0]≡a
filter-index-lemma P l@(x ∷ xs) (suc i) a l[1+i]≡a Pa≡true = proof
  where
    l[1+i]≡xs[i] : l [ (1 + i) ]? ≡ xs [ i ]?
    l[1+i]≡xs[i] = refl

    xs[i]≡a : xs [ i ]? ≡ just a
    xs[i]≡a = ≡-trans (≡-sym l[1+i]≡xs[i]) l[1+i]≡a

    case-true : P x ≡ true → Σ[ j ∈ ℕ ] ((filter P l) [ j ]? ≡ just a)
    case-true Px≡true = subproof
      where
        sublemma1 : filter P l ≡ (x ∷ (filter P xs))
        sublemma1 = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡true

        sublemma4 : Σ[ j' ∈ ℕ ] ((filter P xs) [ j' ]? ≡ just a)
        sublemma4 = filter-index-lemma P xs i a xs[i]≡a Pa≡true

        j' =  proj₁ sublemma4
        
        sublemma5 : (filter P xs) [ j' ]? ≡ just a
        sublemma5 = proj₂ sublemma4

        sublemma6 : (x ∷ (filter P xs)) [ (1 + j') ]? ≡ (filter P xs) [ j' ]?
        sublemma6 = refl

        sublemma7 : (filter P l) [ (1 + j') ]? ≡ (x ∷ (filter P xs)) [ (1 + j') ]?
        sublemma7 = cong (λ w → w [ (1 + j') ]?) sublemma1
        
        subproof = 1 + j' , ≡-trans sublemma7 (≡-trans sublemma6 sublemma5)

    case-false : P x ≡ false → Σ[ j ∈ ℕ ] ((filter P l) [ j ]? ≡ just a)
    case-false Px≡false = subproof
      where
        sublemma1 : filter P l ≡ filter P xs
        sublemma1 = cong (λ w → if w then (x ∷ (filter P xs)) else (filter P xs)) Px≡false

        sublemma2 : Σ[ j' ∈ ℕ ] ((filter P xs) [ j' ]? ≡ just a)
        sublemma2 = filter-index-lemma P xs i a xs[i]≡a Pa≡true

        j' = proj₁ sublemma2

        sublemma3 : (filter P xs) [ j' ]? ≡ just a
        sublemma3 = proj₂ sublemma2

        sublemma4 : (filter P l) [ j' ]? ≡ (filter P xs) [ j' ]?
        sublemma4 = cong (λ w → w [ j' ]?) sublemma1

        subproof = j' , ≡-trans sublemma4 sublemma3
    proof = ⊎-elim case-true case-false (Bool-LEM (P x))

diff : ℕ → ℕ → ℕ
diff 0       0       = 0
diff (suc x) 0       = suc x
diff 0       (suc y) = suc y
diff (suc x) (suc y) = diff x y

diff[0,x]≡x : (x : ℕ) → diff 0 x ≡ x
diff[0,x]≡x 0 = refl
diff[0,x]≡x (suc x) = refl

diff[x,0]≡x : (x : ℕ) → diff x 0 ≡ x
diff[x,0]≡x 0 = refl
diff[x,0]≡x (suc x) = refl

diff[x,x]≡0 : (x : ℕ) → diff x x ≡ 0
diff[x,x]≡0 0 = refl
diff[x,x]≡0 (suc x) = diff[x,x]≡0 x

x≢y→diff[x,y]>0 : {x y : ℕ} → x ≢ y → diff x y > 0
x≢y→diff[x,y]>0 {0} {0} 0≢0 = ⊥-elim (0≢0 refl)
x≢y→diff[x,y]>0 {suc x} {0} _ = s≤s z≤n
x≢y→diff[x,y]>0 {0} {suc y} _ = s≤s z≤n
x≢y→diff[x,y]>0 {suc x} {suc y} 1+x≢1+y = x≢y→diff[x,y]>0 x≢y
  where
    x≢y : x ≢ y
    x≢y x≡y = 1+x≢1+y (cong suc x≡y)

diff[x,y]>0→x≢y : {x y : ℕ} → diff x y > 0 → x ≢ y
diff[x,y]>0→x≢y {0} {0} ()
diff[x,y]>0→x≢y {suc x} {0} _ ()
diff[x,y]>0→x≢y {0} {suc y} _ ()
diff[x,y]>0→x≢y {suc x} {suc y} diff[1+x,1+y]>0 1+x≡1+y = diff[x,y]>0→x≢y diff[1+x,1+y]>0 (suc-injective 1+x≡1+y)

diff+-lemma : (x y z : ℕ) → diff (x + y) (x + z) ≡ diff y z
diff+-lemma 0       _ _ = refl
diff+-lemma (suc x) y z = diff+-lemma x y z


*-distributes-diffₗ : (x₁ x₂ y : ℕ) → diff (y * x₁) (y * x₂) ≡ y * (diff x₁ x₂)
*-distributes-diffₗ _ _ 0 = refl
*-distributes-diffₗ 0 x₂ (suc y) =
  diff ((1 + y) * 0) ((1 + y) * x₂) ≡⟨ cong (λ w → diff w ((1 + y) * x₂)) (*-zeroʳ (1 + y)) ⟩
  diff 0 ((1 + y) * x₂)             ≡⟨ diff[0,x]≡x ((1 + y) * x₂) ⟩
  (1 + y) * x₂                      ≡⟨ cong (λ w → (1 + y) * w) (≡-sym (diff[0,x]≡x x₂)) ⟩
  (1 + y) * (diff 0 x₂)             ∎
  where
    open PropEq.≡-Reasoning
*-distributes-diffₗ (suc x₁) 0 (suc y) =
  diff ((1 + y) * (1 + x₁)) ((1 + y) * 0) ≡⟨ cong (λ w → diff ((1 + y) * (1 + x₁)) w) (*-zeroʳ (1 + y)) ⟩
  diff ((1 + y) * (1 + x₁)) 0             ≡⟨ diff[x,0]≡x ((1 + y) * (1 + x₁)) ⟩
  (1 + y) * (1 + x₁)                      ≡⟨ cong (λ w → (1 + y) * w) (≡-sym (diff[x,0]≡x (1 + x₁))) ⟩
  (1 + y) * (diff (1 + x₁) 0)             ∎
  where
    open PropEq.≡-Reasoning
*-distributes-diffₗ (suc x₁) (suc x₂) (suc y) =
  diff ((1 + y) * (1 + x₁)) ((1 + y) * (1 + x₂)) ≡⟨ cong (λ w → diff w ((1 + y) * (1 + x₂))) (*-comm (1 + y) (1 + x₁)) ⟩
  diff ((1 + x₁) * (1 + y)) ((1 + y) * (1 + x₂)) ≡⟨ cong (λ w → diff ((1 + x₁) * (1 + y)) w) (*-comm (1 + y) (1 + x₂)) ⟩
  diff ((1 + x₁) * (1 + y)) ((1 + x₂) * (1 + y)) ≡⟨ refl ⟩
  diff ((1 + y) + (x₁ * (1 + y))) ((1 + y) + (x₂ * (1 + y))) ≡⟨ diff+-lemma (1 + y) (x₁ * (1 + y)) (x₂ * (1 + y)) ⟩
  diff (x₁ * (1 + y)) (x₂ * (1 + y))             ≡⟨ cong (λ w → diff w (x₂ * (1 + y))) (*-comm x₁ (1 + y)) ⟩
  diff ((1 + y) * x₁) (x₂ * (1 + y))             ≡⟨ cong (λ w → diff ((1 + y) * x₁) w) (*-comm x₂ (1 + y)) ⟩
  diff ((1 + y) * x₁) ((1 + y) * x₂)             ≡⟨ *-distributes-diffₗ x₁ x₂ (1 + y) ⟩
  (1 + y) * (diff x₁ x₂)                         ≡⟨ refl ⟩
  (1 + y) * (diff (1 + x₁) (1 + x₂))             ∎
  where
    open PropEq.≡-Reasoning



divmod-uniqueness-lemma : (x y n : ℕ) →  x % (1 + n) ≡ y % (1 + n) → x / (1 + n) ≡ y / (1 + n) → x ≡ y
divmod-uniqueness-lemma x y n x%[1+n]≡y%[1+n] x/[1+n]≡y/[1+n] =
  x                                              ≡⟨ m≡m%n+[m/n]*n x n ⟩
  (x % (1 + n)) + ((x / (1 + n)) * (1 + n))      ≡⟨ cong (λ w → w + ((x / (1 + n)) * (1 + n))) x%[1+n]≡y%[1+n] ⟩
  (y % (1 + n)) + ((x / (1 + n)) * (1 + n))      ≡⟨ cong (λ w → (y % (1 + n)) + w) (cong (λ w → w * (1 + n)) x/[1+n]≡y/[1+n]) ⟩
  (y % (1 + n)) + ((y / (1 + n)) * (1 + n))      ≡⟨ ≡-sym (m≡m%n+[m/n]*n y n) ⟩
  y                                              ∎
  where
    open PropEq.≡-Reasoning

m<1+n→m%[1+n]≡m : {m n : ℕ} → m < (1 + n) → m % (1 + n) ≡ m
m<1+n→m%[1+n]≡m m<1+n@(s≤s m≤n) = m≤n⇒m%n≡m m≤n


divmod-lemma : (w x y n : ℕ) → y < (1 + n) → w ≡ y + x * (1 + n) → y ≡ w % (1 + n) × x ≡ w / (1 + n)
divmod-lemma w x y n y<1+n w≡y+x*[1+n] = y≡w%[1+n] , x≡w/[1+n]
  where
    y%[1+n]≡y : y % (1 + n) ≡ y
    y%[1+n]≡y = m<1+n→m%[1+n]≡m y<1+n

    w%[1+n]≡y : w % (1 + n) ≡ y
    w%[1+n]≡y =
      w % (1 + n)                  ≡⟨ cong (λ h → h % (1 + n)) w≡y+x*[1+n] ⟩
      (y + x * (1 + n)) % (1 + n)  ≡⟨ [m+kn]%n≡m%n y x n ⟩
      y % (1 + n)                  ≡⟨ y%[1+n]≡y ⟩
      y                            ∎
      where
        open PropEq.≡-Reasoning

    sublemma1 : y % (1 + n) + (x * (1 + n)) % (1 + n) < 1 + n
    sublemma1 = begin-strict
      y % (1 + n) + (x * (1 + n)) % (1 + n) ≡⟨ cong (λ h → y % (1 + n) + h) (m*n%n≡0 x n) ⟩
      y % (1 + n) + 0                       ≡⟨ +-identityʳ (y % (1 + n)) ⟩
      y % (1 + n)                           ≡⟨ y%[1+n]≡y ⟩
      y                                     <⟨ y<1+n ⟩
      1 + n                                 ∎
      where
        open ≤-Reasoning

    w/[1+n]≡x : w / (1 + n) ≡ x
    w/[1+n]≡x =
      w / (1 + n)                                ≡⟨ cong (λ h → h / (1 + n))  w≡y+x*[1+n] ⟩
      (y + x * (1 + n)) / (1 + n)                ≡⟨ +-distrib-/ y (x * (1 + n)) sublemma1 ⟩
      (y / (1 + n)) + (( x * (1 + n)) / (1 + n)) ≡⟨ cong (λ h → h + (( x * (1 + n)) / (1 + n))) ( m<n⇒m/n≡0 y<1+n ) ⟩ 
      (( x * (1 + n)) / (1 + n))                 ≡⟨  m*n/n≡m x (1 + n) ⟩
      x                                          ∎
      where
        open PropEq.≡-Reasoning
        
    y≡w%[1+n] = ≡-sym w%[1+n]≡y
    x≡w/[1+n] = ≡-sym w/[1+n]≡x



{-
 TODO : simplify this to one case by using ¬ (x₁ ≡ x₂ × y₁ ≡ y₂)
-}
offset-uniqueness-lemma : {n m x₁ y₁ x₂ y₂ : ℕ} →  (y₁ < m) → (y₂ < m) → y₁ + (x₁ * m) ≡ y₂ + (x₂ * m) → (x₁ ≡ x₂ × y₁ ≡ y₂)
offset-uniqueness-lemma {n} {m} {x₁} {y₁} {x₂} {y₂} y₁<m y₂<m w₁≡w₂ = x₁≡x₂ , y₁≡y₂
  where
    w₁ = y₁ + (x₁ * m)
    w₂ = y₂ + (x₂ * m)

    sublemma1 : Σ[ m' ∈ ℕ ] (m ≡ 1 + m')
    sublemma1 = suc<-lemma y₁<m

    m' = proj₁ sublemma1
    m≡1+m' = proj₂ sublemma1

    y₁<1+m' : y₁ < 1 + m'
    y₁<1+m' = begin-strict
      y₁       <⟨ y₁<m ⟩
      m        ≡⟨ m≡1+m' ⟩
      1 + m'   ∎
      where
        open ≤-Reasoning

    y₂<1+m' : y₂ < 1 + m'
    y₂<1+m' = begin-strict
      y₂       <⟨ y₂<m ⟩
      m        ≡⟨ m≡1+m' ⟩
      1 + m'   ∎
      where
        open ≤-Reasoning
    

    w₁' = y₁ + (x₁ * (1 + m'))
    w₂' = y₂ + (x₂ * (1 + m'))

    w₁≡w₁' : w₁ ≡ w₁'
    w₁≡w₁' = cong (λ h → y₁ + (x₁ * h)) m≡1+m'

    w₂≡w₂' : w₂ ≡ w₂'
    w₂≡w₂' = cong (λ h → y₂ + (x₂ * h)) m≡1+m'

    w₁'≡w₂' : w₁' ≡ w₂'
    w₁'≡w₂' = ≡-trans (≡-sym w₁≡w₁') (≡-trans w₁≡w₂ w₂≡w₂')
    
    sublemma2 : y₁ ≡ w₁' % (1 + m') × x₁ ≡ w₁' / (1 + m')
    sublemma2 = divmod-lemma w₁' x₁ y₁ m' y₁<1+m' refl

    sublemma3 : y₂ ≡ w₂' % (1 + m') × x₂ ≡ w₂' / (1 + m')
    sublemma3 = divmod-lemma w₂' x₂ y₂ m' y₂<1+m' refl

    x₁≡x₂ = ≡-trans (proj₂ sublemma2) (≡-trans (cong (λ h → h / (1 + m')) w₁'≡w₂') (≡-sym (proj₂ sublemma3)))
    y₁≡y₂ = ≡-trans (proj₁ sublemma2) (≡-trans (cong (λ h → h % (1 + m')) w₁'≡w₂') (≡-sym (proj₁ sublemma3)))


offset-uniqueness-lemma2 : {n m x₁ y₁ x₂ y₂ : ℕ} →  (y₁ < m) → (y₂ < m) → ¬ (x₁ ≡ x₂ × y₁ ≡ y₂) → y₁ + (x₁ * m) ≢ y₂ + (x₂ * m)
offset-uniqueness-lemma2 {n} {m} {x₁} {y₁} {x₂} {y₂} y₁<m  y₂<m = contrapositive (offset-uniqueness-lemma {n} {m} {x₁} {y₁} {x₂} {y₂} y₁<m y₂<m)

ℕ-¬¬ : (x y : ℕ) → ¬ (¬ (x ≡ y)) → x ≡ y
ℕ-¬¬ 0       0 ¬¬0≡0 = refl
ℕ-¬¬ (suc x) 0 ¬¬1+x≡0 = ⊥-elim (¬¬1+x≡0 ¬1+x≡0)
  where
    ¬1+x≡0 : (1 + x) ≢ 0
    ¬1+x≡0 ()
ℕ-¬¬ 0 (suc y) ¬¬0≡1+y = ⊥-elim (¬¬0≡1+y ¬0≡1+y)
  where
    ¬0≡1+y : 0 ≢ (1 + y)
    ¬0≡1+y ()
ℕ-¬¬ (suc x) (suc y) ¬¬1+x≡1+y = 1+x≡1+y
  where
    ¬¬x≡y : ¬ (¬ (x ≡ y))
    ¬¬x≡y ¬x≡y = contradiction
      where
        ¬1+x≡1+y : ¬ (1 + x ≡ 1 + y)
        ¬1+x≡1+y 1+x≡1+y = ¬x≡y (suc-injective 1+x≡1+y)
        
        contradiction = ¬¬1+x≡1+y ¬1+x≡1+y
    
    x≡y : x ≡ y
    x≡y = ℕ-¬¬ x y ¬¬x≡y

    1+x≡1+y = cong suc x≡y

sub-suc-lemma5 : (x y : ℕ) → x < 1 + y → x ≤ y
sub-suc-lemma5 x y (s≤s x≤y) = x≤y

+-injective : (m : ℕ) → {x y : ℕ} → m + x ≡ m + y → x ≡ y
+-injective 0       x≡y     = x≡y
+-injective (suc m) 1+x≡1+y = +-injective m (suc-injective 1+x≡1+y)





*-injectiveₗ : (m : ℕ) → {x y : ℕ} → (1 + m) * x ≡ (1 + m) * y → x ≡ y
*-injectiveₗ m {0}     {0} _   = refl
*-injectiveₗ m {suc x} {0} hyp = ⊥-elim contradiction
  where
    sublemma1 : (1 + m) * (1 + x) ≡ 1 + (x + m * (1 + x))
    sublemma1 = refl

    sublemma2 : (1 + m) * (1 + x) ≢ 0
    sublemma2 ()

    sublemma3 : (1 + m) * 0 ≡ 0
    sublemma3 = *-zeroʳ (1 + m)

    sublemma4 : (1 + m) * (1 + x) ≡ 0
    sublemma4 = ≡-trans hyp sublemma3

    contradiction = sublemma2 sublemma4
*-injectiveₗ m {0} {suc y} hyp = ⊥-elim contradiction
  where
    sublemma1 : 0 ≡ (1 + m) * 0
    sublemma1 = ≡-sym (*-zeroʳ (1 + m))

    sublemma2 : 0 ≢ (1 + m) * (1 + y)
    sublemma2 ()

    sublemma3 : 0 ≡ (1 + m) * (1 + y)
    sublemma3 = ≡-trans sublemma1 hyp

    contradiction = sublemma2 sublemma3
*-injectiveₗ m {suc x} {suc y} hyp = proof
  where
    sublemma1 : (1 + m) + x * (1 + m) ≡ (1 + m) + y * (1 + m)
    sublemma1 =
      (1 + m) + x * (1 + m) ≡⟨ refl ⟩
      (1 + x) * (1 + m)     ≡⟨ *-comm (1 + x) (1 + m) ⟩
      (1 + m) * (1 + x)     ≡⟨ hyp ⟩
      (1 + m) * (1 + y)     ≡⟨ *-comm (1 + m) (1 + y) ⟩
      (1 + y) * (1 + m)     ≡⟨ refl ⟩
      (1 + m) + y * (1 + m) ∎
      where
        open PropEq.≡-Reasoning

    sublemma2 : (1 + m) * x ≡ (1 + m) * y
    sublemma2 =
      (1 + m) * x  ≡⟨ *-comm (1 + m) x ⟩
      x * (1 + m)  ≡⟨ +-injective (1 + m) sublemma1 ⟩
      y * (1 + m)  ≡⟨ *-comm y (1 + m) ⟩
      (1 + m) * y  ∎
      where
        open PropEq.≡-Reasoning

    proof = cong suc (*-injectiveₗ m {x} {y} sublemma2)


*-injectiveᵣ : (m : ℕ) → {x y : ℕ} → x * (1 + m) ≡ y * (1 + m) → x ≡ y
*-injectiveᵣ m {x} {y} hyp = *-injectiveₗ m [1+m]*x≡[1+m]*y 
  where
    [1+m]*x≡[1+m]*y : (1 + m) * x ≡ (1 + m) * y
    [1+m]*x≡[1+m]*y =
      (1 + m) * x   ≡⟨ *-comm (1 + m) x ⟩
      x * (1 + m)   ≡⟨ hyp ⟩
      y * (1 + m)   ≡⟨ *-comm y (1 + m) ⟩
      (1 + m) * y   ∎
      where
        open PropEq.≡-Reasoning


div<-lemma : (x y m : ℕ) → y < (1 + m) → (y + x * (1 + m)) / (1 + m) ≡ x
div<-lemma x y m y<1+m = ≡-sym (proj₂ (divmod-lemma  (y + x * (1 + m)) x y m y<1+m refl))
  
mod<-lemma : (x y m : ℕ) → y < (1 + m) → (y + x * (1 + m)) % (1 + m) ≡ y
mod<-lemma x y m y<1+m = ≡-sym (proj₁ (divmod-lemma  (y + x * (1 + m)) x y m y<1+m refl))


{-
-- Contrapositive of injectivity
divmod-uniqueness3 : (x y m : ℕ) → x ≢ y → x * (1 + m) ≢ y * (1 + m)
divmod-uniqueness3 x y m x≢y x*[1+m]≡y*[1+m] = x≢y (*-injectiveᵣ m x*[1+m]≡y*[1+m])
-}
{-
  
-}

divmod-uniqueness4 : (x₁ x₂ y m : ℕ) → y + x₁ * m ≢ y + x₂ * m → x₁ ≢ x₂
divmod-uniqueness4 x₁ x₂ y m hyp x₁≡x₂ = hyp (cong (λ x → y + x * m) x₁≡x₂)

divmod-uniqueness5 : (x y₁ y₂ m : ℕ) → y₁ + x * m ≢ y₂ + x * m → y₁ ≢ y₂
divmod-uniqueness5 x y₁ y₂ m hyp y₁≡y₂ = hyp (cong (λ y → y + x * m) y₁≡y₂)

divmod-uniqueness6 : (x₁ x₂ y₁ y₂ m : ℕ) → y₁ < (1 + m) → y₂ < (1 + m) → (y₁ + x₁ * (1 + m)) / (1 + m) ≢ (y₂ + x₂ * (1 + m)) / (1 + m) → x₁ ≢ x₂
divmod-uniqueness6 x₁ x₂ y₁ y₂ m y₁<1+m y₂<1+m hyp x₁≡x₂ = contradiction
  where
    sublemma1 : (y₁ + x₁ * (1 + m)) / (1 + m) ≡ x₁
    sublemma1 = div<-lemma x₁ y₁ m y₁<1+m

    sublemma2 : (y₂ + x₂ * (1 + m)) / (1 + m) ≡ x₂
    sublemma2 = div<-lemma x₂ y₂ m y₂<1+m

    sublemma3 : (y₁ + x₁ * (1 + m)) / (1 + m) ≡ (y₂ + x₂ * (1 + m)) / (1 + m)
    sublemma3 =
      (y₁ + x₁ * (1 + m)) / (1 + m)   ≡⟨ div<-lemma x₁ y₁ m y₁<1+m ⟩
      x₁                              ≡⟨ x₁≡x₂ ⟩
      x₂                              ≡⟨ ≡-sym (div<-lemma x₂ y₂ m y₂<1+m) ⟩
      (y₂ + x₂ * (1 + m)) / (1 + m)   ∎
      where
        open PropEq.≡-Reasoning
    
    contradiction = hyp sublemma3

ℕ≡-LEM : (x y : ℕ) → (x ≡ y) ⊎ (x ≢ y)
ℕ≡-LEM 0 0 = inj₁ refl
ℕ≡-LEM (suc x) 0 = inj₂ (λ ())
ℕ≡-LEM 0 (suc y) = inj₂ (λ ())
ℕ≡-LEM (suc x) (suc y) = sublemma (ℕ≡-LEM x y)
  where
    sublemma : (x ≡ y) ⊎ (x ≢ y) → (1 + x ≡ 1 + y) ⊎ (1 + x ≢ 1 + y)
    sublemma (inj₁ x≡y) = inj₁ (cong suc x≡y)
    sublemma (inj₂ x≢y) = inj₂ (λ 1+x≡1+y → x≢y (suc-injective 1+x≡1+y))



divmod-uniqueness7 : (x₁ x₂ y₁ y₂ m : ℕ) → y₁ + x₁ * m ≢ y₂ + x₂ * m → y₁ ≢ y₂ ⊎ x₁ ≢ x₂
divmod-uniqueness7 x₁ x₂ y₁ y₂ m hyp = sublemma (ℕ≡-LEM x₁ x₂)
  where
    sublemma : (x₁ ≡ x₂) ⊎ (x₁ ≢ x₂) → y₁ ≢ y₂ ⊎ x₁ ≢ x₂
    sublemma (inj₁ x₁≡x₂) = subsublemma (ℕ≡-LEM y₁ y₂)
      where
        subsublemma : (y₁ ≡ y₂) ⊎ (y₁ ≢ y₂) → y₁ ≢ y₂ ⊎ x₁ ≢ x₂
        subsublemma (inj₁ y₁≡y₂) = ⊥-elim (hyp subsubsublemma)
          where
            subsubsublemma : y₁ + x₁ * m ≡ y₂ + x₂ * m
            subsubsublemma =
              y₁ + x₁ * m   ≡⟨ cong (λ y → y + x₁ * m) y₁≡y₂ ⟩
              y₂ + x₁ * m   ≡⟨ cong (λ x → y₂ + x * m) x₁≡x₂ ⟩
              y₂ + x₂ * m   ∎
              where
                open PropEq.≡-Reasoning
        subsublemma (inj₂ y₁≢y₂) = inj₁ y₁≢y₂
        subproof = subsublemma (ℕ≡-LEM y₁ y₂)
    sublemma (inj₂ x₁≢x₂) = inj₂ x₁≢x₂


divmod-uniqueness2 : (x y m : ℕ) → x ≢ y → (x % (1 + m) ≢ y % (1 + m)) ⊎ ((x / (1 + m)) ≢ (y / (1 + m)))
divmod-uniqueness2 x y m x≢y = proof
  where
    x-def : x ≡ (x % (1 + m)) + ((x / (1 + m)) * (1 + m))
    x-def = m≡m%n+[m/n]*n x m

    y-def : y ≡ (y % (1 + m)) + ((y / (1 + m)) * (1 + m))
    y-def = m≡m%n+[m/n]*n y m

    sublemma : ((x % (1 + m)) + ((x / (1 + m)) * (1 + m))) ≢ ((y % (1 + m)) + ((y / (1 + m)) * (1 + m)))
    sublemma hyp = x≢y (≡-trans x-def (≡-trans hyp (≡-sym y-def)))
    
    proof = divmod-uniqueness7 (x / (1 + m)) (y / (1 + m)) (x % (1 + m)) (y % (1 + m)) (1 + m) sublemma

x≢0→NonZero-x : (x : ℕ) → x ≢ 0 → NonZero x
x≢0→NonZero-x 0         0≢0 = ⊥-elim (0≢0 refl)
x≢0→NonZero-x (suc x) 1+x≢0 = tt

x≢0→x≠0 : (x : ℕ) → x ≢ 0 → False (x ≟ 0)
x≢0→x≠0  0       0≢0 = ⊥-elim (0≢0 refl)
x≢0→x≠0 (suc x) 1+x≢0 = tt

divmod-uniqueness2< : (x y m : ℕ) → (m≠0 : False (m ≟ 0)) → x ≢ y → (_%_ x m { m≠0 } ≢ _%_ y m { m≠0 }) ⊎ ((_/_ x m {m≠0}) ≢ (_/_ y m {m≠0}))
divmod-uniqueness2< x y 0 ()
divmod-uniqueness2< x y (suc m) 1+m≢0 x≢y = divmod-uniqueness2 x y m x≢y

i<n*m→n≢0 : (i n m : ℕ) → i < n * m → n ≢ 0
i<n*m→n≢0 _ 0 _ ()
i<n*m→n≢0 _ (suc n) _ _ ()

i<n*m→m≢0 : (i n m : ℕ) → i < n * m → m ≢ 0
i<n*m→m≢0 i n m i<n*m = i<n*m→n≢0 i m n (resp (λ w → i < w) (*-comm n m) i<n*m)

/-<-≤-lemma : (x y m : ℕ) → (m≠0 : False (m ≟ 0)) → x ≤ y → _/_ x m {m≠0} ≤ _/_ y m {m≠0}
/-<-≤-lemma x y m m≠0 x≤y = /-mono-≤ {x} {y} {m} {m} {m≠0} {m≠0} x≤y ≤-refl

*<-lemma :
  (i n m : ℕ) →
  (i<n*m : i < n * m) →
  let m≠0 = (x≢0→x≠0 m (i<n*m→m≢0 i n m i<n*m))
  in
  (_/_ i m {m≠0}) < n
*<-lemma  i n 0 i<n*0 = ⊥-elim (x≮0 (resp (λ w → i < w) (*-zeroʳ n) i<n*0))
*<-lemma i 0 (suc m) i<0*[1+m] = ⊥-elim (x≮0 i<0*[1+m])
*<-lemma 0 (suc n) (suc m) hyp = s≤s z≤n
*<-lemma (suc i) (suc n) (suc m) hyp = proof
  where
    1+m≢0 : 1 + m ≢ 0
    1+m≢0 ()

    1+m≠0 : False (1 + m ≟ 0)
    1+m≠0 = x≢0→x≠0 (1 + m) 1+m≢0

    sublemma≤ : (1 + i) / (1 + m) ≤ (1 + n)
    sublemma≤ = begin
      (1 + i) / (1 + m)               ≤⟨ /-<-≤-lemma (1 + i) ((1 + n) * (1 + m)) (1 + m) 1+m≠0 (<⇒≤ hyp) ⟩
      ((1 + n) * (1 + m)) / (1 + m)   ≡⟨ m*n/n≡m (1 + n) (1 + m) ⟩
      (1 + n)                         ∎
      where
        open ≤-Reasoning

    sublemma≢ : (1 + i) / (1 + m) ≢ (1 + n)
    sublemma≢ hyp2 = contradiction
      where
        subsublemma : (1 + n) * (1 + m) < (1 + n) * (1 + m)
        subsublemma = begin-strict
          (1 + n) * (1 + m)                ≡⟨ ≡-sym (cong (λ w → w * (1 + m)) hyp2) ⟩
          ((1 + i) / (1 + m)) * (1 + m)    ≤⟨ m/n*n≤m (1 + i) (1 + m) ⟩
          1 + i                            <⟨ hyp ⟩
          (1 + n) * (1 + m)                ∎
          where
            open ≤-Reasoning
            
        contradiction = <-irrefl refl subsublemma
   
    proof = ≤∧≢⇒< sublemma≤ sublemma≢


product-uniqueness3 :
  (n m i : ℕ) →
  (i<n*m : i < n * m) →
  let m≠0 = (x≢0→x≠0 m (i<n*m→m≢0 i n m i<n*m))
  in
  ((range n) ⊗ (range m)) [ i ]? ≡ just (n - (1 + (_/_ i m {m≠0})) , m - (1 + (_%_ i m {m≠0})))
product-uniqueness3 n m i i<n*m = proof
  where
    m≢0 : m ≢ 0
    m≢0 = i<n*m→m≢0 i n m i<n*m

    m≠0 : False (m ≟ 0)
    m≠0 = x≢0→x≠0 m m≢0

    m>0 : m > 0
    m>0 = n≢0⇒n>0 m≢0

    ∃m',m≡1+m' : Σ[ m' ∈ ℕ ] (m ≡ 1 + m')
    ∃m',m≡1+m' = suc<-lemma m>0

    m' = proj₁ ∃m',m≡1+m'
    m≡1+m' = proj₂ ∃m',m≡1+m'

    sublemma : i ≡ (i % (1 + m')) + (i / (1 + m')) * (1 + m')
    sublemma = m≡m%n+[m/n]*n i m'

    i%[1+m']<1+m' : i % (1 + m') < (1 + m')
    i%[1+m']<1+m' = m%n<n i m'


    i/[1+m']<n : i / (1 + m') < n
    i/[1+m']<n = *<-lemma i n (1 + m') (resp (λ w → i < n * w) m≡1+m' i<n*m)
   
    {- product-lookup : {n m x y : ℕ} → (x<n : x < n) → (y<m : y < m) → ((range n) ⊗ (range m)) [ (y + (x * m)) ]? ≡ just (n - (1 + x) , m - (1 + y)) -}
    sublemma2 : ((range n) ⊗ (range (1 + m'))) [ ((i % (1 + m')) + ((i / (1 + m')) * (1 + m'))) ]? ≡ just (n - (1 + (i / (1 + m'))) , (1 + m') - (1 + (i % (1 + m'))))
    sublemma2 = product-lookup i/[1+m']<n i%[1+m']<1+m'

    sublemma3 : ((range n) ⊗ (range (1 + m'))) [ i ]? ≡ ((range n) ⊗ (range (1 + m'))) [ ((i % (1 + m')) + ((i / (1 + m')) * (1 + m'))) ]?
    sublemma3 = cong (λ w → ((range n) ⊗ (range (1 + m'))) [ w ]?) sublemma

    sublemma4 : just (n - (1 + (i / (1 + m'))) , (1 + m') - (1 + (i % (1 + m')))) ≡ just (n - (1 + (i / m)) , m - (1 + (i % m)))
    sublemma4 = cong (λ w → just (n - (1 + (i / w)) , w - (1 + (i % w)))) (≡-sym m≡1+m')

    sublemma5 : ((range n) ⊗ (range m)) [ i ]? ≡ ((range n) ⊗ (range (1 + m'))) [ i ]?
    sublemma5 = cong (λ w → ((range n) ⊗ (range w)) [ i ]?) m≡1+m'

    proof = ≡-trans sublemma5 (≡-trans sublemma3 (≡-trans sublemma2 sublemma4))

{-
product-uniqueness : (n m x y : ℕ) → x < n → y < m → (i : ℕ) → ((range n) ⊗ (range m)) [ i ]? ≡ just (x , y) → i ≡ (m - (1 + y)) + ((n - (1 + x)) * m)
product-uniqueness n m x y x<n y<m i n⊗m[i]≡[x,y] = proof
  where
    v  = (m - (1 + y)) + ((n - (1 + x)) * m)

    sublemma-range : ((range n) ⊗ (range m)) [ i ]? ≡ ((range n) ⊗ (range m)) [ v ]?
    sublemma-range =
      ((range n) ⊗ (range m)) [ i ]?   ≡⟨ n⊗m[i]≡[x,y] ⟩
      just (x , y)                     ≡⟨ ≡-sym (product-lookup2 x<n y<m) ⟩
      ((range n) ⊗ (range m)) [ v ]?   ∎
      where
        open PropEq.≡-Reasoning

m-[1+y]<m : m - (1 + y) < m
    m-[1+y]<m = sub<-lemma2 y<m

    sublemma1 : Σ[ m' ∈ ℕ ] (m ≡ 1 + m')
    sublemma1 = suc<-lemma y<m

    m' = proj₁ sublemma1
    m≡1+m' = proj₂ sublemma1

    y≤1+m' : y ≤ 1 + m'
    y≤1+m' = begin
      y      <⟨ y<m ⟩
      m      ≡⟨ m≡1+m' ⟩
      1 + m'   ∎
      where
        open ≤-Reasoning

    sublemma2 : (1 + m') - (1 + y) < (1 + m')
    sublemma2 = resp (λ w → w - (1 + y) < w) m≡1+m' m-[1+y]<m

    m-[1+y]%m≡m-[1+y] : (m - (1 + y)) % m ≡ (m - (1 + y))
    m-[1+y]%m≡m-[1+y] =
      (m - (1 + y)) % m                ≡⟨ cong (λ w → (w - (1 + y)) % w) m≡1+m' ⟩
      ((1 + m') - (1 + y)) % (1 + m')  ≡⟨ m≤n⇒m%n≡m (sub-suc-lemma5 ((1 + m') - (1 + y)) m' sublemma2) ⟩
      (1 + m') - (1 + y)               ≡⟨ cong (λ w  → w - (1 + y)) (≡-sym m≡1+m') ⟩
      m - (1 + y)                      ∎
      where
        open PropEq.≡-Reasoning
      
    v%m≡m-[1+y]%m : v % m ≡ (m - (1 + y)) % m
    v%m≡m-[1+y]%m =
      v % m                                                          ≡⟨ refl ⟩
      ((m - (1 + y)) + ((n - (1 + x)) * m)) % m                      ≡⟨ cong (λ w → ((w - (1 + y)) + ((n - (1 + x)) * w)) % w) m≡1+m' ⟩
      (((1 + m') - (1 + y)) + ((n - (1 + x)) * (1 + m'))) % (1 + m') ≡⟨ [m+kn]%n≡m%n ((1 + m') - (1 + y)) (n - (1 + x)) m' ⟩
      ((1 + m') - (1 + y)) % (1 + m')                                ≡⟨ cong (λ w → (w - (1 + y)) % w) (≡-sym m≡1+m') ⟩ 
      (m - (1 + y)) % m                                              ∎
      where
        open PropEq.≡-Reasoning

    v%m≡m-[1+y] : v % m ≡ (m - (1 + y))
    v%m≡m-[1+y] = ≡-trans v%m≡m-[1+y]%m m-[1+y]%m≡m-[1+y]


    ¬¬i≡v : ¬ (¬ (i ≡ v))
    ¬¬i≡v ¬i≡v = contradiction
      where
        -- if i ≢ v then
        sublemma : (i % m ≢ v % m) ⊎ (i / m ≢ v / m)
        sublemma = divmod-uniqueness2< i v m (x≢0→x≠0 m (m<n⇒n≢0 y<m)) ¬i≡v

        sublemma2 : ((i % m ≢ v % m) ⊎ (i / m ≢ v / m)) → (((range n) ⊗ (range m)) [ i ]? ≢ ((range n) ⊗ (range m)) [ v ]?) 
        sublemma2 (inj₁ i%m≢v%m) = proof
          where
            proof

        contradiction = (sublemma2 sublemma) sublemma-range
    

    
{-
    sublemma2 : v / m ≡ ((m - (1 + y)) / m) + ((n - (1 + x)) / m)
    sublemma2 =
      v / m                                                             ≡⟨ cong (λ w → ((w - (1 + y)) + ((n - (1 + x)) * w)) / w) m≡1+m' ⟩
      (((1 + m') - (1 + y)) + ((n - (1 + x)) * (1 + m'))) / (1 + m')    ≡⟨ 
-}

    proof
-}

{-
fix-match-lemma1 :
  (M : TM) →
  (state symbol : ℕ) →
  (state ≤ max-state M) →
  (symbol ≤ max-symbol M) →
  find (δ-match state symbol) M ≡ nothing → 
  find (δ-match state symbol) (fix M) ≡ just (δ state symbol (1 + (max-state M)) symbol true)
fix-match-lemma1 M state symbol state≤max-states symbol≤max-symbols no-match = proof
  where
    #states = 1 + (max-state M)
    #symbols = 1 + (max-symbol M)

    state<#states : state < #states
    state<#states = begin-strict
      state               ≤⟨ state≤max-states ⟩ 
      max-state M         <⟨ n<1+n (max-state M) ⟩
      1 + (max-state M)   ∎
      where
        open ≤-Reasoning

    symbol<#symbols : symbol < #symbols
    symbol<#symbols = begin-strict
      symbol               ≤⟨ symbol≤max-symbols ⟩
      max-symbol M         <⟨ n<1+n (max-symbol M) ⟩
      1 + (max-symbol M)   ∎
      where
        open ≤-Reasoning
    
    states = range #states
    symbols = range #symbols

    inputs = list-product states symbols

    lemma1 : (fix M) ≡ M ++ (map (make-switch #states) (filter (δ-filter M) inputs))
    lemma1 = refl

    lemma2 :
        find (δ-match state symbol) (fix M)
      ≡ find (δ-match state symbol) (map (make-switch #states) (filter (δ-filter M) inputs))
    lemma2 = find-++-lemma (δ-match state symbol) M (map (make-switch #states) (filter (δ-filter M) inputs)) no-match


    lemma3 : not (match (δ-match state symbol) M) ≡ true
    lemma3 = cong not (find-match-lemma (δ-match state symbol) M no-match)

    lemma4 : Σ[ i ∈ ℕ ] (inputs [ i ]? ≡ just (state , symbol))
    lemma4 = product-complete state<#states symbol<#symbols

    i = proj₁ lemma4
    
    inputs[i]≡[state,symbol] = proj₂ lemma4

    lemma5 : δ-filter M (state , symbol) ≡ true
    lemma5 = lemma3

    lemma6 : Σ[ j ∈ ℕ ] ((filter (δ-filter M) inputs) [ j ]? ≡ just (state , symbol))
    lemma6 = filter-index-lemma (δ-filter M) inputs i (state , symbol) inputs[i]≡[state,symbol] lemma5

    j = proj₁ lemma6

    lemma7 : (filter (δ-filter M) inputs) [ j ]? ≡ just (state , symbol)
    lemma7 = proj₂ lemma6

    lemma8 : (map (make-switch #states) (filter (δ-filter M) inputs)) [ j ]? ≡ Maybe-map (make-switch #states) ((filter (δ-filter M) inputs) [ j ]?)
    lemma8 = get-map-lemma (make-switch #states) (filter (δ-filter M) inputs) j

    lemma9 : Maybe-map (make-switch #states) ((filter (δ-filter M) inputs) [ j ]?) ≡ just (δ state symbol #states symbol true)
    lemma9 = cong (Maybe-map (make-switch #states)) lemma7

    
    proof
-}
{-
fix-match-lemma2 :
  (M : TM) →
  (state symbol : ℕ) →
  (state ≤ max-state M) →
  (symbol ≤ max-symbol M) → 
  (transition : TM-δ) →
  find (δ-match state symbol) M ≡ just transition →
  find (δ-match state symbol) (fix M) ≡ just transition

-}
