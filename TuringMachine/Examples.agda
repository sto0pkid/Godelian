module TuringMachine.Examples where

open import Basic renaming (ℕ to Nat)
open import TuringMachine3
open import TuringMachine.Properties
open import Util.Arithmetic
open import Util.List

{-
TODO: offload the TM descriptions into some standard file format
-}


TM-0,m : (m : Nat) → TM 0 m
TM-0,m m (() , _)

TM-0,0 : TM 0 0
TM-0,0 = TM-0,m 0

TM-n,0 : (n : Nat) → TM n 0
TM-n,0 n (_ , ())

-- There are (1 + n*m*2)^(n*m)  Turing machines with n states, m symbols
-- 1-state, 1-symbol: 3^1 = 3
-- 1-state, 2-symbol: 5^2 = 25
-- 1-state, 3-symbol: 7^3 = 343
-- 2-state, 2-symbol: 9^4 = 6561
-- ...

-- these 3 are the only 1-state, 1-symbol Turing machines
-- loops, writing 0s across the whole tape 
tm-1,1-1 : TM 1 1
tm-1,1-1 (zero , zero) = just (zero , (zero , true))

-- loops in place
tm-1,1-2 : TM 1 1
tm-1,1-2 (zero , zero) = just (zero , (zero , false))

-- halts immediately
tm-1,1-3 : TM 1 1
tm-1,1-3 (zero , zero) = nothing


-- loops, rewriting all input to 0
tm-1,2-1 : TM 1 2
tm-1,2-1 (zero , zero) = just (zero , (zero , true))
tm-1,2-1 (zero , (suc zero)) = just (zero , (zero , true))

-- loops, preserving input
tm-1,2-2 : TM 1 2
tm-1,2-2 (zero , zero) = just (zero , (zero , true))
tm-1,2-2 (zero , (suc zero)) = just (zero , ((suc zero) , true))

-- loops, rewriting all input to 1
tm-1,2-3 : TM 1 2
tm-1,2-3 (zero , zero) = just (zero , ((suc zero) , true))
tm-1,2-3 (zero , (suc zero)) = just (zero , ((suc zero) , true))

-- loops, negating inputs
tm-1,2-4 : TM 1 2
tm-1,2-4 (zero , zero) = just (zero , ((suc zero) , true))
tm-1,2-4 (zero , (suc zero)) = just (zero , (zero , true))

-- loops until it finds a 0, preserving input
tm-1,2-5 : TM 1 2
tm-1,2-5 (zero , zero) = nothing
tm-1,2-5 (zero , (suc zero)) = just (zero , ((suc zero) , true))


-- tm₃-1,1-1 loops on all inputs
-- nice & easy proof, just listing cases.
tm-1,1-1-loops : (tape : List (Fin 1)) → TM-loops tm-1,1-1 tape
tm-1,1-1-loops tape = proof
  where
    -- show there's no halting condition by cases:
    sublemma1 :
      ¬ (Σ[ condition ∈ ((Fin 1) × (Fin 1)) ] (
              tm-1,1-1 condition ≡ nothing
      ))
    sublemma1 ((zero , zero) , ())

    -- no halting condition implies no halting
    proof = looping-transition-theorem tm-1,1-1 tape sublemma1



-- tm₃-1,1-3 halts on all inputs
tm-1,1-3-halts : (tape : List (Fin 1)) → TM-halts tm-1,1-3 tape
tm-1,1-3-halts [] = 1 , refl
tm-1,1-3-halts (zero ∷ xs) = 1 , proof
  where
    M = tm-1,1-3
    input = (zero ∷ xs)
    
    start-config = TM-start-state M input
    open TM-state start-config

    final-config = TM-step-state M start-config

    Fin1-lemma : (x : Fin 1) → x ≡ zero
    Fin1-lemma zero = refl

    symbol-lemma1 : get-default zero input pos ≡ zero
    symbol-lemma1 = Fin1-lemma (get-default zero input pos)

    tm-step : ((Fin 1) × ((List (Fin 1)) × Nat)) ⊎ (List (Fin 1))
    tm-step = TM-step M (state , (input , pos))

    tm-step-lemma2 : tm-step ≡ TM-apply-δ (state , (input , pos)) (M (zero , zero))
    tm-step-lemma2 = cong (λ x → TM-apply-δ (state , (input , pos)) (M (zero , x))) symbol-lemma1

    tm-step-lemma3 : tm-step ≡ inj₂ input
    tm-step-lemma3 = tm-step-lemma2

    config-lemma4 : TM-state.halted final-config ≡ true
    config-lemma4 = resp (λ x → TM-state.halted (TM-apply-step start-config x) ≡ true) (≡-sym tm-step-lemma3) refl
    
    proof = config-lemma4

tm-table-1,1-1 : List (TM-δ 1 1)
tm-table-1,1-1 =
    (δ zero zero zero zero true)
  ∷ []


tm-table-1,2-4 : List (TM-δ 1 2)
tm-table-1,2-4 =
    (δ q₀ s₀ q₀ s₁ true)
  ∷ (δ q₀ s₁ q₀ s₀ true)
  ∷ []
  where
    q₀ = zero
    s₀ = zero
    s₁ = suc zero

{-
supposed to compute 2n if n is odd, 2n+1 if n is even
http://www.inf.ed.ac.uk/teaching/courses/ci/documents/slides05.pdf
{
  (q0,  0, q1,  0, R),
  (q0,  1, q2,  1, R),
  (q0, ̄b, q3, ̄b, R),
  (q1,  0, q1,  0, R),
  (q1,  1, q2,  1, R),
  (q1, ̄b, q3,  1, L),
  (q2,  0, q1,  0, R),
  (q2,  1, q2,  1, R),
  (q2, ̄b, q3,  0, L)
}
least significant digit is at the end of the tape rather than the start
intuitively:
  q₀ = start state
  q₁ = last read symbol was 0
  q₂ = last read symbol was 1
  q₃ = last read symbol was blank, halt

read out to the end of the tape (i.e. until encountering a blank symbol)
if the last read digit was 0 then it's even, print 1 after the end of the tape = 2n+1
if the last read digit was 1 then it's odd, print 0 after the end of the tape  = 2n

-}
tm-table-4,3-even-odd : List (TM-δ 4 3)
tm-table-4,3-even-odd =
    (δ q₀ s₀ q₁ s₀ R)
  ∷ (δ q₀ s₁ q₂ s₁ R)
  ∷ (δ q₀ b  q₃ b  R)
  ∷ (δ q₁ s₀ q₁ s₀ R)
  ∷ (δ q₁ s₁ q₂ s₁ R)
  ∷ (δ q₁ b  q₃ s₁ L)
  ∷ (δ q₂ s₀ q₁ s₀ R)
  ∷ (δ q₂ s₁ q₂ s₁ R)
  ∷ (δ q₂ b  q₃ s₀ L)
  ∷ []
  where
    q₀ = zero
    q₁ = suc zero
    q₂ = suc (suc zero)
    q₃ = suc (suc (suc zero))
    b = zero
    s₀ = suc zero
    s₁ = suc (suc zero)
    R = true
    L = false

tm-table-1,3-strip : List (TM-δ 1 3)
tm-table-1,3-strip =
    (δ q₀ s₀ q₀ b R)
  ∷ []
  where
    q₀ = zero
    b = zero
    s₀ = suc zero
    R = true

tm-table-5,4-move-bit : List (TM-δ 5 4)
tm-table-5,4-move-bit =
    (δ q₀ b  q₁ sₓ R)
  ∷ (δ q₁ b  q₁ b R)
  ∷ (δ q₁ s₀ q₂ b L)
  ∷ (δ q₁ s₁ q₃ b L)
  ∷ (δ q₂ b  q₂ b L)
  ∷ (δ q₂ sₓ q₄ s₀ L)
  ∷ (δ q₃ b  q₃ b L)
  ∷ (δ q₃ sₓ q₄ s₁ L)
  ∷ []
  where
    q₀ = zero
    q₁ = suc zero
    q₂ = suc (suc zero)
    q₃ = suc (suc (suc zero))
    q₄ = suc (suc (suc (suc zero)))
    b = zero
    s₀ = suc zero
    s₁ = suc (suc zero)
    sₓ = suc (suc (suc zero))
    R = true
    L = false

{-
  shifts the first string of bits to the beginning of the tape, ex:
  bbbb1010bbb --> 1010bbbbbbb
  expects b in the first tape cell
  expects the initial tape to only contain b, 0, and 1
  expects there to actually be a bit string: it will loop on blank tape looking for it
-}
tm-table-10,5-move-bits : List (TM-δ 10 5)
tm-table-10,5-move-bits =
  -- mark the starting position
    (δ q₀ b  q₁ sₓ R)
    
  -- scan until a bit is found
  ∷ (δ q₁ b  q₁ b R)
  ∷ (δ q₁ s₀ q₂ s₀ R)
  ∷ (δ q₁ s₁ q₂ s₁ R)
  
  -- scan to the end of the bit string and mark the cell after the end
  ∷ (δ q₂ s₀ q₂ s₀ R)
  ∷ (δ q₂ s₁ q₂ s₁ R)
  ∷ (δ q₂ b  q₃ t  L)

  -- scan back to immediately before the beginning of the bit string
  ∷ (δ q₃ s₀ q₃ s₀ L)
  ∷ (δ q₃ s₁ q₃ s₁ L)
  ∷ (δ q₃ b  q₄ b  R)
  ∷ (δ q₃ sₓ q₄ sₓ R)

  -- scan forward to the beginning of the bit string, erase that bit
  -- the bit is stored as the internal state: q₅ for 0, q₆ for 1
  -- if it instead finds the ending marker then erase it
  ∷ (δ q₄ b  q₄ b R)
  ∷ (δ q₄ s₀ q₅ b L)
  ∷ (δ q₄ s₁ q₆ b L)
  ∷ (δ q₄ t  q₈ b L)

  -- scan back to the marked starting position and replace the mark with the stored bit
  ∷ (δ q₅ b  q₅ b L)
  ∷ (δ q₅ sₓ q₇ s₀ R)
  ∷ (δ q₆ b  q₆ b L)
  ∷ (δ q₆ sₓ q₇ s₁ R)

  -- write the starting mark in the next cell
  ∷ (δ q₇ b  q₄ sₓ R)

  -- scan back to the beginning and erase the mark
  ∷ (δ q₈ b  q₈ b L)
  ∷ (δ q₈ sₓ q₈ b L)
  ∷ []
  where
    q₀ = zero
    q₁ = suc zero
    q₂ = suc (suc zero)
    q₃ = suc (suc (suc zero))
    q₄ = suc (suc (suc (suc zero)))
    q₅ = suc (suc (suc (suc (suc zero))))
    q₆ = suc (suc (suc (suc (suc (suc zero)))))
    q₇ = suc (suc (suc (suc (suc (suc (suc zero))))))
    q₈ = suc (suc (suc (suc (suc (suc (suc (suc zero)))))))
    
    b = zero
    s₀ = suc zero
    s₁ = suc (suc zero)
    sₓ = suc (suc (suc zero))
    t = suc (suc (suc (suc zero)))
    
    R = true
    L = false

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

{-
tm-table-21,6-copy-bits-unit :
  let
    b = zero
    s₀ = suc zero
    s₁ = suc (suc zero)
  in
    TM-state.tape (
      TM-run 100
      (TM-from-table tm-table-21,6-copy-bits)
      (s₁ ∷ s₀ ∷ s₁ ∷ s₀ ∷ b ∷ b ∷ b ∷ [])
    )
    ≡ (s₁ ∷ s₀ ∷ s₁ ∷ s₀ ∷ b ∷ s₁ ∷ s₀ ∷ s₁ ∷ s₀ ∷ b ∷ b ∷ b ∷ [])
tm-table-21,6-copy-bits-unit = refl

-- it sequences but the copy machine itself doesn't play nice with sequencing
tm-double-copy : TM 42 6
tm-double-copy = seq tm tm
  where
    tm = (TM-from-table tm-table-21,6-copy-bits)


tm-double-copy-output : List Nat
tm-double-copy-output =
  map toℕ (TM-state.tape (
    TM-run 80
    tm-double-copy
    (s₁ ∷ s₀ ∷ s₁ ∷ s₀ ∷ b ∷ b ∷ b ∷ [])
  ))
  where
    b = zero
    s₀ = suc zero
    s₁ = suc (suc zero)
-}

-- move left one cell and halt
TM-L : {n : Nat} → TM 2 n
TM-L (zero , x) = just (suc zero , (x , false))
TM-L (suc zero , x) = nothing

-- move right one cell and halt
TM-R : {n : Nat} → TM 2 n
TM-R (zero , x) = just (suc zero , (x , true))
TM-R (suc zero , _) = nothing

-- write a given symbol, move right, then move back and halt
TM-a : {n : Nat} → (s : Fin n) → TM 3 n
TM-a s (zero , x) = just (suc zero , (s , true))
TM-a s (suc zero , x) = just (suc (suc zero) , (x , false))
TM-a s (suc (suc zero) , _) = nothing

TM-2L : {n : Nat} → TM 3 n
TM-2L (zero , x) = just (suc zero , (x , false))
TM-2L (suc zero , x) = just (suc (suc zero) , (x , false))
TM-2L (suc (suc zero) , _) = nothing


TM-seq2 : TM 8 2
TM-seq2 = seq (TM-a s₁) (seq TM-L (TM-a s₁))
  where
    s₁ = suc zero

TM-seq2-output : List (Fin 2)
TM-seq2-output = TM-state.tape (TM-run 4 TM-seq2 [])

TM-seq2-trace : List (Nat × List (Fin 2))
TM-seq2-trace = map (λ x → TM-state.pos x , TM-state.tape x) (map (λ x → TM-run x TM-seq2 []) (range 10))

TM-seq2-table : List (TM-δ 8 2)
TM-seq2-table = TM-to-table TM-seq2
