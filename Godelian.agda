module Godelian where

open import Agda.Primitive
open import Basic hiding (all)
open import TuringMachine3
open import MuRecursive
open import FOL

record Domain
  : Set₂ where
  field
    n : ℕ
    T : FOL n

    rels : Fin n → ℕ → ℕ → Set
    objs : ℕ → ℕ

    M-models-T : model T record{ A = ℕ ; objs = objs ; rels = rels }
    
    proofs : Set

    ⊢ : FOL n → Set

    proves : proofs → FOL n → Set
    ⊢-semantics : (ϕ : FOL n) → (⊢ ϕ) ↔ (Σ[ p ∈ proofs ] (proves p ϕ))
    ⊢-sound : (ϕ : FOL n) → (⊢ ϕ) → (T ⊨ ϕ)
    ⊢-consistent : ¬ (Σ[ ϕ ∈ FOL n ] (⊢ ϕ × ⊢ (~ ϕ)))

    Godel : FOL n
    Godel-semantics : (I ℕ objs rels Godel) → ¬ (Σ[ p ∈ proofs ] (proves p Godel))
    Godel-semantics2 : (subs : List (Var × ℕ)) → ((I-helper ℕ objs rels subs Godel) ↔ (¬ (Σ[ p ∈ proofs ] (proves p Godel))))

    proof-DNE : (ϕ : FOL n) → ¬ (¬ (Σ[ p ∈ proofs ] (proves p ϕ))) → Σ[ p ∈ proofs ] (proves p ϕ)

    e₁ : FOL n → ℕ
    e₁-bijective : Bijective e₁

    GTh : ℕ → Set₁
    GTh-semantics : GTh ≡ (λ m → (Σ[ ϕ ∈ FOL n ] (e₁ ϕ ≡ m × T ⊨ ϕ)))
    

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

    M : PreInterpretation {n}
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
    lemma2 = Godel-semantics lemma1

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

    M : PreInterpretation {n}
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
    lemma3 hyp = lemma2 ((proj₂ (Godel-semantics2 [])) hyp)

    lemma4 : Σ[ p ∈ proofs ] (proves p G)
    lemma4 = proof-DNE G lemma3

    ⊢G : ⊢ G
    ⊢G = (proj₂ (⊢-semantics G)) lemma4

    inconsistency : Σ[ ϕ ∈ FOL n ] (⊢ ϕ × ⊢ (~ ϕ))
    inconsistency = G , (⊢G , ⊢~G)

    proof = ⊢-consistent inconsistency

{-
Godel-undecidability :
  (D : Domain) →
  let
    T = Domain.T D
  in
    μR-undecidable (_⊨_ T)
Godel-undecidability D dec@(e , (e-bij , (f , (f-complete , f-sound)))) = proof
  where
    open Domain D

    G = Godel

    fG-dec : (μR-interp f ((e G) ∷ []) 0) ⊎ (μR-interp f ((e G) ∷ []) 1)
    fG-dec = f-complete G

    helper : (μR-interp f ((e G) ∷ []) 0) ⊎ (μR-interp f ((e G) ∷ []) 1) → ⊥
    helper (inj₁ hyp) = subproof
      where
        ¬T⊨G : ¬ (T ⊨ G)
        ¬T⊨G T⊨G = subsubproof
          where
            subsubproof
        subproof
    proof
-}
