
open import Data.Empty using (⊥-elim)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; #_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Vec using (Vec; map; []; _∷_)


open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Algebraic.AbstractCategory
open import Algebraic.Signatures
open import Algebraic.Structures
open import Countable.Sets
open import Countable.SetCategory

{-- A minimal countable constructive set theory. --}
module Algebraic.Capsules where

    -- A capsule is a simple algebraic structure with an action and combination operation
    -- data LCapsule : {sig : Signature} { A : ACatStruct } → Set where 

    LCapsule : {sig : Signature} → Set₁    
    LCapsule {sig} = Σ[ A ∈ ACatStruct ] 
                    Σ[ X ∈ Set ] 
                    X  -- the bot
                    × 
                    ( car₁ {AbsCatSig} A → X → X) -- the action
                    × ( car₁ {AbsCatSig} A → X ) -- the guard

    LeftRegularCapsule : ( A : ACatStruct ) → LCapsule {AbsCatSig}
    LeftRegularCapsule A = (A , car₁ {AbsCatSig} A , bot , mult , guard)
      where
        bot : car₁ {AbsCatSig} A
        bot = (proj₂ A) (# 0) []

        mult : car₁ {AbsCatSig} A → car₁ {AbsCatSig} A → car₁ {AbsCatSig} A
        mult a x = (proj₂ A) (# 1) (a ∷ x ∷ [])

        guard : car₁ {AbsCatSig} A → car₁ {AbsCatSig} A
        guard a = (proj₂ A) (# 2) (a ∷ [])

    RCapsule : {sig : Signature} → Set₁    
    RCapsule {sig} = Σ[ A ∈ ACatStruct ] 
                    Σ[ X ∈ Set ] 
                    X  -- the bot
                    × 
                    (car₁ {AbsCatSig} A → X → X) -- the action (right)
                    × (car₁ {AbsCatSig} A → X ) -- the guard

    RightRegularCapsule : (A : ACatStruct) → RCapsule {AbsCatSig}
    RightRegularCapsule A = (A , car₁ {AbsCatSig} A , bot , action , guard)
        where
        bot : car₁ {AbsCatSig} A
        bot = (proj₂ A) (# 0) []

        action : car₁ {AbsCatSig} A → car₁ {AbsCatSig} A → car₁ {AbsCatSig} A
        action x a = (proj₂ A) (# 1) (x ∷ a ∷ [])

        guard : car₁ {AbsCatSig} A → car₁ {AbsCatSig} A
        guard a = (proj₂ A) (# 2) (a ∷ [])
    
    -- Bicapsule: A acts on the left of X, B acts on the right of X
    BiCapsule : {sig : Signature} → Set₁    
    BiCapsule {sig} = Σ[ A ∈ ACatStruct ] 
                      Σ[ B ∈ ACatStruct ] 
                      Σ[ X ∈ Set ] 
                      X  -- the bot
                      × 
                      (car₁ {AbsCatSig} A → X → X) -- left action: A acts on X from left
                      × 
                      (X → car₁ {AbsCatSig} B → X) -- right action: B acts on X from right  
                      × 
                      (car₁ {AbsCatSig} A → X) -- left guard
                      × 
                      (car₁ {AbsCatSig} B → X) -- right guard

    RegularBiCapsule : (A : ACatStruct) → BiCapsule {AbsCatSig}
    RegularBiCapsule A = (A , A , car₁ {AbsCatSig} A , bot , leftAction , rightAction , leftGuard , rightGuard)
        where
        bot : car₁ {AbsCatSig} A
        bot = (proj₂ A) (# 0) []

        leftAction : car₁ {AbsCatSig} A → car₁ {AbsCatSig} A → car₁ {AbsCatSig} A
        leftAction a x = (proj₂ A) (# 1) (a ∷ x ∷ [])

        rightAction : car₁ {AbsCatSig} A → car₁ {AbsCatSig} A → car₁ {AbsCatSig} A  
        rightAction x b = (proj₂ A) (# 1) (x ∷ b ∷ [])

        leftGuard : car₁ {AbsCatSig} A → car₁ {AbsCatSig} A
        leftGuard a = (proj₂ A) (# 2) (a ∷ [])

        rightGuard : car₁ {AbsCatSig} A → car₁ {AbsCatSig} A  
        rightGuard b = (proj₂ A) (# 3) (b ∷ [])

    -- A Hom category capsule.
    

    -- A morphism of bicapsules has f(a·x)=a·f(x) and f(x·b)=f(x)·b
    BiCapsuleMorphism : {sig : Signature} → BiCapsule {sig} → BiCapsule {sig} → Set
    BiCapsuleMorphism {sig} (A₁ , B₁ , X₁ , bot₁ , leftAct₁ , rightAct₁ , leftGuard₁ , rightGuard₁) 
                            (A₂ , B₂ , X₂ , bot₂ , leftAct₂ , rightAct₂ , leftGuard₂ , rightGuard₂) = 
        Σ[ fA ∈ (car₁ {AbsCatSig} A₁ → car₁ {AbsCatSig} A₂) ]
        Σ[ fB ∈ (car₁ {AbsCatSig} B₁ → car₁ {AbsCatSig} B₂) ] 
        Σ[ fX ∈ (X₁ → X₂) ]
        -- Preserve bot
        (fX bot₁ ≡ bot₂)
        ×
        -- Left action compatibility: f(a·x) = f(a)·f(x)
        ((a : car₁ {AbsCatSig} A₁) (x : X₁) → fX (leftAct₁ a x) ≡ leftAct₂ (fA a) (fX x))
        ×
        -- Right action compatibility: f(x·b) = f(x)·f(b)  
        ((x : X₁) (b : car₁ {AbsCatSig} B₁) → fX (rightAct₁ x b) ≡ rightAct₂ (fX x) (fB b))
        ×
        -- Left guard compatibility: f(guard(a)) = guard(f(a))
        ((a : car₁ {AbsCatSig} A₁) → fX (leftGuard₁ a) ≡ leftGuard₂ (fA a))
        ×
        -- Right guard compatibility: f(guard(b)) = guard(f(b))
        ((b : car₁ {AbsCatSig} B₁) → fX (rightGuard₁ b) ≡ rightGuard₂ (fB b))

