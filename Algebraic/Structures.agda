
open import Agda.Primitive using (Set)
open import Data.Empty using (⊥-elim)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Vec using (Vec; map)


open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Algebraic.Signatures
open import Countable.Sets

{-- A minimal countable constructive set theory. --}
module Algebraic.Structures where


    {-- Operator on X a ConSet is function [X]^n→[X] --}
    Operator : ConSet → ℕ → Set
    Operator X n = Vec (asSet X) n → asSet X

    {-- Operator on X a Set is function X^n→X --}
    Operator₁ : Set → ℕ → Set
    Operator₁ X n = Vec X n → X

    {-- This is Definition 3.?? : Alge_Ω --}
    Structure : {sig : Signature} → Set
    Structure {sig} = Σ[ X ∈ ConSet ] 
                    ((i : Fin (nOps sig) ) → Operator X (proj₂ (proj₂ sig i)))

    Structure₁ : {sig : Signature} → Set₁
    Structure₁ {sig} = Σ[ X ∈ Set ] 
                    ((i : Fin (nOps sig) ) → Operator₁ X (proj₂ (proj₂ sig i)))

    car : ∀ {sig : Signature} → Structure {sig} → Set
    car (A , opA) = asSet A

    car₁ : ∀ {sig : Signature} → Structure₁ {sig} → Set
    car₁ (A , opA) = A

    getOp : (sig : Signature) → (A : Structure {sig}) → (i : Fin (nOps sig)) → Operator (proj₁ A) (proj₂ (proj₂ sig i))
    getOp sig alg i = (proj₂ alg) i

    {-- Identity homomorphisms --}
    id : ∀ {sig : Signature} → (A : Structure {sig}) → ConFun
    id {sig} (N , ops) = ℕ←ℕ (λ x → x)
    id {sig} (F a , ops) = F←F {a} {a} (λ x → x)



    Homomorphism : ∀ {sig : Signature} → Structure {sig} → Structure {sig} → Set
    Homomorphism {sig} (A , opsA) (B , opsB) = 
        Σ[ f ∈ (asSet A → asSet B) ]
        ((i : Fin (nOps sig)) →
            (x : Vec (asSet A) (proj₂ (proj₂ sig i))) →
                f (opsA i x) ≡ opsB i (map f x)
        )

    {-- This is Definition 3.?? : Homomorphism --}
    Homomorphism₁ : ∀ {sig : Signature} → Structure₁ {sig} → Structure₁ {sig} → Set
    Homomorphism₁ {sig} (A , opsA) (B , opsB) = 
        Σ[ f ∈ (A → B) ]
        ((i : Fin (nOps sig)) →
            (x : Vec A (proj₂ (proj₂ sig i))) →
                f (opsA i x) ≡ opsB i (map f x)
        )        
