
open import Data.Empty using (⊥-elim)

open import Data.Nat using (ℕ; _≟_)
open import Data.Fin using (Fin)


open import Relation.Binary.PropositionalEquality using (refl; subst; _≡_; cong; sym; trans; subst-∘)
open import Relation.Nullary using (yes; no; Dec)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import Function using (_∘_; id)

open import Countable.Functions

{-- A minimal countable constructive set theory. --}
module CountableAlgebras where


    {-- Operator on X is function X^n→X --}
    Operator : {U : Types} → (X : asUniverse U) → ℕ → Set U
    Operator {ConSets} X n = Vec (asSet X) n → asSet X
    -- Operator {ConFuns} X n = Vec (asSet X) n → asSet X  
    Operator {Sets} X n = Vec X n → asSet X
    
    {-- Signature is a countable collection of operators --}
    Operator X opSig = Vec X (proj₂ opSig) → X

    {-- This is Definition 3.3 : Alge_Ω --}
    AlgeStruct : {U : Types} {sig : Signature} → Set₁
    AlgeStruct sig = Σ[ X : asUniverse U ] 
                    ((i : Fin (nOps sig) ) → Operator X (proj₂ sig i))


    {-- This is Definition 3.4 : Homomorphism --}
    Homomorphism : ∀ {sig : Signature} → (A B : AlgeStruct sig) → Set
    Homomorphism {sig} (A , opA) (B , opB) = 
        Σ[ f ∈ asSet A → asSet B ]
        ((i : Fin (nOps sig)) →
            (x : Vec (asSet A) (proj₂ sig i)) →
                f (opA i x) ≡ opB i (Vec.map f x)
        )