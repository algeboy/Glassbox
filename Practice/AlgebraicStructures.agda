-- -----------------------------------------------------------------------------
-- Algebraic Structures
-- -----------------------------------------------------------------------------
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)     -- Dependent types --
open import Data.String using (String) -- Strings for operator names --
open import Data.Nat using (ℕ)         -- Nats for valence --
open import Data.Fin using (Fin)       -- Fin for indexing --
open import Data.Vec as Vec using (Vec)
open import Data.List as List using (List; lookup; length; map)

open import Signatures using (Signature; valence; nOps; asSignature)

open import Countable.Functions 

module AlgebraicStructures where

    {-- Operator on X is function X^n→X --}
    Operator : (X : Set) → (String × ℕ) → Set
    Operator X opSig = Vec X (proj₂ opSig) → X

    {-- This is Definition 3.3 : Alge_Ω --}
    AlgeStruct : (sig : Signature) → Set₁
    AlgeStruct sig = Σ[ X ∈ Set ] 
                    ((i : Fin (nOps sig) ) → Operator X (proj₂ sig i))

    getCarrier : {sig : Signature} → AlgeStruct sig → Set
    getCarrier alg = proj₁ alg

    getOp : (sig : Signature) → (A : AlgeStruct sig) → (i : Fin (nOps sig)) → Operator (getCarrier {sig} A) (proj₂ sig i)
    getOp sig alg i = (proj₂ alg) i

    {-- Homomorphisms. --}
    Homomorphism : (A B : AlgeStruct sig) → Set
    Homomorphism A B = Σ[ f ∈ (getCarrier {sig} A → getCarrier {sig} B) ] (∀ i → getOp sig B i ∘ f ≡ f ∘ getOp sig A i) 

    {-- Helper functions to inhabit AlgeStruct --}
    OpData : (X : Set) → Set
    OpData X = Σ[ name ∈ String ] Σ[ val ∈ ℕ ] (Vec X val → X)

    {-- Takes a list of operators and produces a signature --}
    getSignature : {X : Set} 
                   → List (OpData X)
                   → Signature
    getSignature {X} ops = asSignature (List.map (λ op → (proj₁ op , proj₁ (proj₂ op))) ops)

    {-- 
        Takes a list of operators and produces 
        an algebraic structure.  This makes the 
        signature itself which may require you to 
        later prove to agda that this signature 
        equals another.
    --}
    asAlgeStruct : (X : Set) 
                    → (ops : List (OpData X)) 
                    → AlgeStruct (length ops , λ i → proj₁ (List.lookup ops i) , proj₁ (proj₂ (List.lookup ops i)))
    asAlgeStruct X ops = (X , λ i → proj₂ (proj₂ (List.lookup ops i)))
