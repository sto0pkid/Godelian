module Godelian where

open import Agda.Primitive
open import Basic hiding (all)
open import TuringMachine3
open import FOL

record Domain
  : Set₁ where
  field
    n : ℕ
    T : FOL (suc n)

    T-preinterpretation : PreInterpretation {suc n}
    T-model : model T T-preinterpretation
    -- bijection is probably unnecessarily strong
    -- left-invertible injection is probably sufficient
    rels : Fin (suc n) → ℕ → ℕ → Set
    objs : ℕ → ℕ

    M-models-T : model T record{ A = ℕ ; objs = objs ; rels = rels }
   
    -- converts formulas to Nats, to be interpreted by the prover
    G₁ : FOL (suc n) → ℕ
    G₁-bijection : Bijective G₁

    -- converts Nats representing formulas to Nats representing numerals representing formulas;
    -- this the Godelization "proper"
    G₂ : ℕ → ℕ
    G₂-bijection : Bijective G₂

    proofs : Set
    -- converts proofs to Nats; how the proofs are represented on the Turing machine
    G₃ : proofs → ℕ
    G₃-bijection : Bijective G₃

    -- converts Nats representing proofs to Nats representing numerals representing proofs
    G₄ : ℕ → ℕ
    G₄-bijection : Bijective G₄
    
    ⊢ : FOL (suc n) → Set

    proves : proofs → FOL (suc n) → Set
    ⊢-semantics : (ϕ : FOL (suc n)) → (⊢ ϕ) ↔ (Σ[ p ∈ proofs ] (proves p ϕ))
    ⊢-sound : (ϕ : FOL (suc n)) → (⊢ ϕ) → (T ⊨ ϕ)
    ⊢-consistent : ¬ (Σ[ ϕ ∈ FOL (suc n) ] (⊢ ϕ × ⊢ (~ ϕ)))
    
    is-proof : ℕ → Set
    is-proof-semantics : (m : ℕ) → (is-proof m) ↔ (Σ[ p ∈ proofs ] ((G₃ p) ≡ m))
    is-proof-numeral : ℕ → Set
    is-proof-numeral-semantics : (m : ℕ) → (is-proof-numeral m) ↔ (Σ[ p ∈ proofs ] ((G₄ (G₃ p)) ≡ m))

    is-formula : ℕ → Set
    is-formula-semantics : (m : ℕ) → (is-formula m) ↔ (Σ[ ϕ ∈ (FOL (suc n)) ] ((G₁ ϕ) ≡ m))
    is-formula-numeral : ℕ → Set
    is-formula-numeral-semantics : (m : ℕ) → (is-formula-numeral m) ↔ (Σ[ ϕ ∈ (FOL (suc n)) ] ((G₂ (G₁ ϕ)) ≡ m))

   
    Gproves : Term → Term → FOL (suc n)
    Gproves-semantics :
      (Gp Gϕ : ℕ) →
      (
        (⊢ (Gproves (c Gp) (c Gϕ))) ↔
        (Σ[ p ∈ proofs ] (
          Σ[ ϕ ∈ (FOL (suc n)) ] (
            (Gp ≡ (G₄ (G₃ p))) × ((Gϕ ≡ (G₂ (G₁ ϕ))) × (proves p ϕ))
          )
        ))
     )
    Gprovable : Term → FOL (suc n)
    Gprovable-semantics : Gprovable ≡ (λ Gϕ → (exists (v 0) (Gproves (v (v 0)) Gϕ)))
    Gproves-rel : (n m : Term) → Gproves n m ≡ (rel zero n m)

    Godel : FOL (suc n)
    Godel-semantics : Godel ≡ ~ (Gprovable (c (G₂ (G₁ Godel))))
    Godel-semantics2 : (I ℕ objs rels Godel) → ¬ (Σ[ p ∈ proofs ] (proves p Godel))
    Godel-semantics3 : (subs : List (Var × ℕ)) → ((I-helper ℕ objs rels subs Godel) ↔ (¬ (Σ[ p ∈ proofs ] (proves p Godel))))

    proof-DNE : (ϕ : FOL (suc n)) → ¬ (¬ (Σ[ p ∈ proofs ] (proves p ϕ))) → Σ[ p ∈ proofs ] (proves p ϕ)
    
    {-
    proof-enumerator : TM
    proof-enumerator-semantics : (m : Nat) → ∃ p ∈ proofs , (outputs TM run proof-enumerator m (G₃ p))
    formula-enumerator : TM
    formula-enumerator-semantics : (m : Nat) → ∃ ϕ ∈ (FOL n) , (outputs TM run formula-enumerator m (G₁ ϕ))
    -}

A≡B→A→B : {A B : Set} → A ≡ B → A → B
A≡B→A→B refl a = a

Godel-theorem :
  (D : Domain) →
  let
    G = Domain.Godel D
    G-semantics = Domain.Godel-semantics D
    ⊢ = Domain.⊢ D
  in
    ¬ (⊢ G)
Godel-theorem D ⊢G = proof
  where
    open Domain D

    G = Godel

    M : PreInterpretation {suc n}
    M = record {
        A = ℕ ;
        objs = objs ;
        rels = rels
      }
    
    T⊨G : T ⊨ G
    T⊨G = ⊢-sound G ⊢G

    lemma1 : I ℕ objs rels G
    lemma1 = T⊨G M M-models-T

    lemma2 : ¬ (Σ[ p ∈ proofs ] (proves p G))
    lemma2 = Godel-semantics2 lemma1

    lemma3 : (Σ[ p ∈ proofs ] (proves p G))
    lemma3 = (proj₁ (⊢-semantics G)) ⊢G

    proof = lemma2 lemma3



Godel-theorem2 :
  (D : Domain) →
  let
    G = Domain.Godel D
    G-semantics = Domain.Godel-semantics D
    ⊢ = Domain.⊢ D
  in
    ¬ (⊢ (~ G))
Godel-theorem2 D ⊢~G = proof
  where
    open Domain D

    G = Godel

    M : PreInterpretation {suc n}
    M = record {
        A = ℕ ;
        objs = objs ;
        rels = rels
      }
    
    T⊨~G : T ⊨ (~ G)
    T⊨~G = ⊢-sound (~ G) ⊢~G

    lemma1 : I ℕ objs rels (~ G)
    lemma1 = T⊨~G M M-models-T

    lemma2 : ¬ (I-helper ℕ objs rels [] G)
    lemma2 = lemma1

    lemma3 : ¬ (¬ (Σ[ p ∈ proofs ] (proves p G)))
    lemma3 hyp = lemma2 ((proj₂ (Godel-semantics3 [])) hyp)

    lemma4 : Σ[ p ∈ proofs ] (proves p G)
    lemma4 = proof-DNE G lemma3

    ⊢G : ⊢ G
    ⊢G = (proj₂ (⊢-semantics G)) lemma4

    inconsistency : Σ[ ϕ ∈ FOL (suc n) ] (⊢ ϕ × ⊢ (~ ϕ))
    inconsistency = G , (⊢G , ⊢~G)

    proof = ⊢-consistent inconsistency

