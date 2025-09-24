
-- open import Agda.Primitive using (Set)
open import Data.Empty using (⊥-elim)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Vec using (Vec; map)


open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

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

    {-- Terminal algebraic structure on Fin 1 where all operators return zero --}
    TerminalStruct : ∀ {sig : Signature} → Structure {sig}
    TerminalStruct {sig} = (F 1 , ops)
        where
        ops : (i : Fin (nOps sig)) → Operator (F 1) (proj₂ (proj₂ sig i))
        ops i = λ _ → Fin.zero  -- All operators return the constant zero

    {-- Terminal algebraic structure₁ on Fin 1 where all operators return zero --}
    TerminalStruct₁ : ∀ {sig : Signature} → Structure₁ {sig}
    TerminalStruct₁ {sig} = (Fin 1 , ops)
        where
        ops : (i : Fin (nOps sig)) → Operator₁ (Fin 1) (proj₂ (proj₂ sig i))
        ops i = λ _ → Fin.zero  -- All operators return the constant zero

    {-- The unique element in Fin 1 --}
    terminal-element : Fin 1
    terminal-element = Fin.zero

    {-- Proof that terminal-element is the only element in Fin 1 --}
    terminal-unique : (x : Fin 1) → x ≡ terminal-element
    terminal-unique Fin.zero = refl

    {-- Terminal property: there is a unique homomorphism from any structure to TerminalStruct --}
    terminal-map : ∀ {sig : Signature} → (A : Structure {sig}) → asSet (proj₁ A) → Fin 1
    terminal-map A x = Fin.zero

    terminal-map₁ : ∀ {sig : Signature} → {A : Set} → A → Fin 1  
    terminal-map₁ x = Fin.zero

