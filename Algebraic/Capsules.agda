
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

    Capsule : {sig : Signature} → Set₁    
    Capsule {sig} = Σ[ A ∈ ACatStruct ] 
                    Σ[ X ∈ Set ] 
                    ( car {AbsCatSig} A → X → X)

    LeftRegularCapsule : ( A : ACatStruct ) → Capsule {AbsCatSig}
    LeftRegularCapsule A = (A , car {AbsCatSig} A , mult)
      where
        mult : car {AbsCatSig} A → car {AbsCatSig} A → car {AbsCatSig} A
        mult f g = (getOp AbsCatSig A (# 1)) (f ∷ g ∷ [])

    -- -- A bicapsule extends this with two target spaces
    -- Bicapsule : {sig : Signature} → Set
    -- Bicapsule {sig} = Σ[ A ∈ ACatStruct ] 
    --                   Σ[ X ∈ ACatStruct ] 
    --                   Σ[ Y ∈ ACatStruct ]
    --                   (car {AbsCatSig} A → car {AbsCatSig} X) × (car {AbsCatSig} A → car {AbsCatSig} Y) × (car {AbsCatSig} A → car {AbsCatSig} X → car {AbsCatSig} X) × (car {AbsCatSig} Y → car {AbsCatSig} A → car {AbsCatSig} Y)
    -- -- Note: we could add laws to these structures, but for now we leave them as-is.

    -- -- Example: the category of sets forms a bicapsule over itself
    -- SetBicapsule : Bicapsule {sig = AbsCatSig}
    -- SetBicapsule = (SetCat , SetCat , SetCat , leftTgt , rightTgt , combine , combine)
    --   where
    --     leftTgt : car {AbsCatSig} SetCat → car {AbsCatSig} SetCat
    --     leftTgt f = ◄ f  
    --     rightTgt : car {AbsCatSig} SetCat → car {AbsCatSig} SetCat
    --     rightTgt f = f ◄  
    --     combine : car {AbsCatSig} SetCat → car {AbsCatSig} SetCat → car {AbsCatSig} SetCat
    --     combine f g = f ← g  