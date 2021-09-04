module Godelian where

open import Agda.Primitive
open import Basic hiding (all)
open import TuringMachine3
open import MuRecursive
open import FOL

record Domain
  : Set₂ where
  field
    {-
      The signature of the theory
    -}
    n : ℕ
    T : FOL n

    {-
      The model M of the theory T
    -}
    rels : Fin n → ℕ → ℕ → Set
    objs : ℕ → ℕ

    {-
      Assertion that M is a model of T
    -}
    M-models-T : model T record{ A = ℕ ; objs = objs ; rels = rels }

    {-
      The set of proofs
    -}
    proofs : Set

    {-
      Derivability
    -}
    ⊢ : FOL n → Set

    proves : proofs → FOL n → Set
    {-
      ϕ is derivable if there exists a proof p such that p proves ϕ
    -}
    ⊢-semantics : (ϕ : FOL n) → (⊢ ϕ) ↔ (Σ[ p ∈ proofs ] (proves p ϕ))
    {-
      Soundness: derivability implies semantic entailment
    -}
    ⊢-sound : (ϕ : FOL n) → (⊢ ϕ) → (T ⊨ ϕ)
    {-
      Consistency: there is no statement ϕ such that both ϕ and ~ϕ are derivable
    -}
    ⊢-consistent : ¬ (Σ[ ϕ ∈ FOL n ] (⊢ ϕ × ⊢ (~ ϕ)))

    {-
      The Godel statement
    -}
    Godel : FOL n

    {-
      The semantics of the Godel statement: that the intuitive statement that there is no proof of G is a logical consequence of the literal interpretation of G into model M
    -}
    Godel-semantics : (I ℕ objs rels Godel) → ¬ (Σ[ p ∈ proofs ] (proves p Godel))

    {-
      ???
    -}
    Godel-semantics2 : (subs : List (Var × ℕ)) → ((I-helper ℕ objs rels subs Godel) ↔ (¬ (Σ[ p ∈ proofs ] (proves p Godel))))

    {-
      NON-CONSTRUCTIVE!
      A double negation elimination axiom for the `proves` relation.
    -}
    proof-DNE : (ϕ : FOL n) → ¬ (¬ (Σ[ p ∈ proofs ] (proves p ϕ))) → Σ[ p ∈ proofs ] (proves p ϕ)

    {-
      The Godel encoding
    -}
    e₁ : FOL n → ℕ
    e₁-bijective : Bijective e₁

    {-
      ???
    -}
    GTh : ℕ → Set₁

    {-
      ???
    -}
    GTh-semantics : GTh ≡ (λ m → (Σ[ ϕ ∈ FOL n ] (e₁ ϕ ≡ m × T ⊨ ϕ)))
    

{-
Godel's incompleteness theorem part 1: the Godel statement is unprovable
-}
Godel-theorem :
  (D : Domain) →
  let
    G = Domain.Godel D
    G-semantics = Domain.Godel-semantics D
    ⊢ = Domain.⊢ D
  in
    ¬ (⊢ G)
Godel-theorem D ⊢G = contradiction
  where
    open Domain D

    G = Godel

    M : PreInterpretation {n}
    M = record {
        A = ℕ ;
        objs = objs ;
        rels = rels
      }

    {-
      We assumed ⊢ G is true, so soundness implies T ⊨ G
    -}
    T⊨G : T ⊨ G
    T⊨G = ⊢-sound G ⊢G

    {-
      The interpretation of the godel statement G is true in model M because T ⊨ G and M models T
    -}
    G-interpretation : I ℕ objs rels G
    G-interpretation = T⊨G M M-models-T

    {-
      The intuitive semantics of G, i.e. that there is no proof of G, is a logical consequence of the literal interpretation by the model M
    -}
    ¬[G-provable] : ¬ (Σ[ p ∈ proofs ] (proves p G))
    ¬[G-provable] = Godel-semantics G-interpretation

    {-
      The semantics of ⊢ is such that ⊢ ϕ implies ∃p,proves(p,ϕ)
    -}
    G-provable : (Σ[ p ∈ proofs ] (proves p G))
    G-provable = (proj₁ (⊢-semantics G)) ⊢G

    {-
      
    -}
    contradiction = ¬[G-provable] G-provable


{-
Godel's incompleteness theorem part 2: the negation of the Godel statement is unprovable
-}
Godel-theorem2 :
  (D : Domain) →
  let
    G = Domain.Godel D
    G-semantics = Domain.Godel-semantics D
    ⊢ = Domain.⊢ D
  in
    ¬ (⊢ (~ G))
Godel-theorem2 D ⊢~G = contradiction
  where
    open Domain D

    G = Godel

    M : PreInterpretation {n}
    M = record {
        A = ℕ ;
        objs = objs ;
        rels = rels
      }

    {-
      We assumed ⊢ ~G is true, so soundness implies T ⊨ ~G
    -}
    T⊨~G : T ⊨ (~ G)
    T⊨~G = ⊢-sound (~ G) ⊢~G

    {-
      The interpretation of ~G by model M
    -}
    ~G-interpretation : I ℕ objs rels (~ G)
    ~G-interpretation = T⊨~G M M-models-T

    {-
      The interpretation of ~G is the negation of the interpretation of G
    -}
    ¬[G-interpretation] : ¬ (I-helper ℕ objs rels [] G)
    ¬[G-interpretation] = ~G-interpretation

    {-
      The intuitive semantics of G, i.e. that there is no proof of G, is logically equivalent to the literal interpretation of G by model M.
    -}
    ¬¬[G-provable] : ¬ (¬ (Σ[ p ∈ proofs ] (proves p G)))
    ¬¬[G-provable] hyp = ¬[G-interpretation] ((proj₂ (Godel-semantics2 [])) hyp)

    {-
      Bypassing constructiveness by invoking an assertion of a special case of double-negation elimination
    -}
    G-provable : Σ[ p ∈ proofs ] (proves p G)
    G-provable = proof-DNE G ¬¬[G-provable]

    {-
      G provable implies ⊢ G by the semantics of ⊢
    -}
    ⊢G : ⊢ G
    ⊢G = (proj₂ (⊢-semantics G)) G-provable

    {-
      Since both ⊢ G and ⊢ ~G , the logic is inconsistent
    -}
    inconsistency : Σ[ ϕ ∈ FOL n ] (⊢ ϕ × ⊢ (~ ϕ))
    inconsistency = G , (⊢G , ⊢~G)

    {-
      The inconsistency contradicts the assertion that ⊢ is consistent
      QED
    -}
    contradiction = ⊢-consistent inconsistency

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
