-- -----------------------------------------------------------------------------
-- Signatures
-- -----------------------------------------------------------------------------
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)     -- Dependent types --
open import Data.String using (String) -- Strings for operator names --
open import Data.Nat using (ℕ)         -- Nats for valence --
open import Data.Fin using (Fin)       -- Fin for indexing --

-- For helper functions --
open import Data.List as List using (List; lookup; length)

module Signatures where

    Signature : Set 
    Signature = Σ[ n ∈ ℕ ] ((Fin n) → (String × ℕ))

    {-- Helper function to inhabit Signature --}
    asSignature : (ops : List (String × ℕ)) → Signature
    asSignature ops = (length ops , λ i → List.lookup ops i)

    {-- Number the ops --}
    nOps : (sig : Signature) → ℕ
    nOps sig = proj₁ sig

    {-- Extract the operator name from index --}
    name : (sig : Signature) → (i : Fin (proj₁ sig)) → String
    name sig i = proj₁ (proj₂ sig i)

    {-- Extract the valence from index --}
    valence : (sig : Signature) → (i : Fin (proj₁ sig)) → ℕ
    valence sig i = proj₂ (proj₂ sig i)
