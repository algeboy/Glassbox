
open import Data.Nat using (ℕ; _≟_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)


open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl; subst; _≡_; cong; sym; trans; subst-∘)
open import Relation.Nullary using (yes; no; Dec)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import Function using (_∘_; id)


open import Algebraic.Signatures
open import Countable.Sets
open import Algebraic.Structures

-- Used for signture & algebraic structure build.
open import Data.String using (String)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
-----------------------------------------------------

{-- A minimal countable constructive set category. --}
module Countable.SetCategory where

    -- TBD: should this signature belong in some general category module?
    {-- As an abstract category is a set of morphisms --}
    AbsCatSig : Signature
    AbsCatSig = (4 , λ i → lookup operations i)
        where
        operations : Vec (String × ℕ) 4
        operations = ("▦" , 0) ∷ ("_∘_" , 2) ∷ ("src" , 1) ∷ ("tgt" , 1) ∷ []

    SetCat : Structure₁ {AbsCatSig}
    SetCat = (ConFun , ops )
        where
        ops : (i : Fin 4) → (Operator₁ ConFun (proj₂ (proj₂ AbsCatSig i)))
        ops Fin.zero = λ _ → ▦        -- identity element (valence 0)
        ops (Fin.suc Fin.zero) = composeConFun  -- binary operation (valence 2)
            where
            composeConFun : Vec ConFun 2 → ConFun
            composeConFun (f ∷ g ∷ []) = f ← g
        ops (Fin.suc (Fin.suc Fin.zero)) = srcConFun  -- source (valence 1)
            where 
            srcConFun : Vec ConFun 1 → ConFun
            srcConFun (f ∷ []) = f ◄
        ops (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = tgtConFun  -- target (valence 1)
            where 
            tgtConFun : Vec ConFun 1 → ConFun
            tgtConFun (f ∷ []) = ◄ f
 
