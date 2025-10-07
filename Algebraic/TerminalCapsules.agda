
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; #_)
open import Data.Vec using (Vec; map; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)

open import Algebraic.AbstractCategory
open import Algebraic.Signatures
open import Algebraic.Structures
open import Algebraic.Capsules
open import Algebraic.Homomorphism
open import Algebraic.HomCategories
open import Countable.Sets
open import Countable.SetCategory


module Algebraic.TerminalCapsules where

    {-- 
        Terminal-Hom bicapsule: 
        TerminalIdCat acts on the left, 
        HomCatStruct acts on the right
        The carrier is Hom {sig}, with terminal elements acting via unique terminal morphism
        and homomorphisms acting regularly on the right
    --}
    TerminalHomBiCapsule : (sig : Signature) → BiCapsule {sig}
    TerminalHomBiCapsule sig = (TerminalIdCatStruct {sig} , HomCatStruct sig , Hom {sig} , 
                               bot , leftAction , rightAction , leftGuard , rightGuard)
        where
        -- The bottom element is the null homomorphism  
        bot : Hom {sig}
        bot = (proj₂ (HomCatStruct sig)) (# 0) []  -- null homomorphism

        -- Left action: terminal elements act via the unique terminal homomorphism
        -- Since TerminalIdCat has only one element, it acts by composing with terminal homomorphism
        leftAction : car₁ {AbsCatSig} (TerminalIdCatStruct {sig}) → Hom {sig} → Hom {sig}
        leftAction terminalElem h = h ∘ terminalIdHom {sig}

        -- Right action: regular action of homomorphisms on homomorphisms (composition)
        rightAction : Hom {sig} → car₁ {AbsCatSig} (HomCatStruct sig) → Hom {sig}
        rightAction h g = (proj₂ (HomCatStruct sig)) (# 1) (h ∷ g ∷ [])  -- h ∘ g

        -- Left guard: since terminal has only one element, return the terminal homomorphism
        leftGuard : car₁ {AbsCatSig} (TerminalIdCatStruct {sig}) → Hom {sig}
        leftGuard terminalElem = terminalIdHom {sig}

        -- Right guard: apply source operation from hom category  
        rightGuard : car₁ {AbsCatSig} (HomCatStruct sig) → Hom {sig}
        rightGuard h = (proj₂ (HomCatStruct sig)) (# 2) (h ∷ [])

    -- Test that our construction creates a valid bicapsule
    test-terminal-hom-bicapsule : BiCapsule {AbsCatSig}
    test-terminal-hom-bicapsule = TerminalHomBiCapsule AbsCatSig

