

open import Data.Nat using (ℕ; _≟_)
open import Data.Fin using (Fin; #_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)


open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl; subst; _≡_; cong; sym; trans; subst-∘)
open import Relation.Nullary using (yes; no; Dec)
open import Axiom.Extensionality.Propositional using (Extensionality)

-- open import Function using (_∘_; id)


open import Algebraic.Signatures
open import Countable.Sets
open import Algebraic.Structures
open import Algebraic.Varieties
open import Algebraic.Equations
open import Algebraic.AbstractCategory
open import Countable.SetLaws

-- Used for signture & algebraic structure build.
open import Data.String using (String)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
-----------------------------------------------------

{-- A minimal countable constructive set category. --}
module Countable.SetCategory where

    -- TBD: should this signature belong in some general category module?

    -- We create a category structure where ConFun serves as both objects and morphisms
    -- This is a monoid-like structure on ConFun
    SetCatStruct : Structure₁ {AbsCatSig} 
    SetCatStruct = (ConFun , ops )
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

    -- SetCat satisfies all the abstract category laws
    certifySetCat : inVariety₁ {ConFun} {AbsCatSig} AbsCatLaws SetCatStruct
    certifySetCat const i = helper i const
      where
        -- THIS IS A HACK TO GET AROUND THE LACK OF DEPENDENT PATTERN MATCHING
        -- Helper pattern synonyms for readability
        pattern i0 = Fin.zero
        pattern i1 = Fin.suc i0
        pattern i2 = Fin.suc i1
        pattern i3 = Fin.suc i2
        pattern i4 = Fin.suc i3
        pattern i5 = Fin.suc i4
        pattern i6 = Fin.suc i5
        pattern i7 = Fin.suc i6
        pattern i8 = Fin.suc i7
        pattern i9 = Fin.suc i8
        pattern i10 = Fin.suc i9

        helper : (i : Fin 11) → (const : Fin 3 → ConFun) → SatEqProp₁ {Fin 3} {AbsCatSig} SetCatStruct (proj₂ (proj₂ (proj₂ AbsCatLaws) i))
        helper i0  const₁ = λ const₂ → leftSinkCompProof (const₂ (# 1))     -- 0: leftSinkCompLaw: □ · g = □
        helper i1  const₁ = λ const₂ → rightSinkCompProof (const₂ (# 0))    -- 1: rightSinkCompLaw: f · □ = □
        helper i2  const₁ = λ const₂ → sinkSrcProof                         -- 2: sinkSrcLaw: □ ◁ = □
        helper i3  const₁ = λ const₂ → sinkTgtProof                         -- 3: sinkTgtLaw: ◁ □ = □
        helper i4  const₁ = λ const₂ → tgtSrcProof (const₂ (# 0))           -- 4: codomainDomainLaw: ◁ (f ◁) = f ◁
        helper i5  const₁ = λ const₂ → srcTgtProof (const₂ (# 0))           -- 5: domainCodomainLaw: (◁ f) ◁ = ◁ f
        helper i6  const₁ = λ const₂ → tgtOrgProof (const₂ (# 0))           -- 6: codomainLeftIdLaw: (◁ f) · f = f
        helper i7  const₁ = λ const₂ → orgSrcProof (const₂ (# 0))           -- 7: domainRightIdLaw: f · (f ◁) = f
        helper i8  const₁ = λ const₂ → tgtCompProof (const₂ (# 0)) (const₂ (# 1))  -- 8: codomainCompLaw: ◁ (f · g) = ◁ (f · (◁ g))
        helper i9  const₁ = λ const₂ → srcCompProof (const₂ (# 0)) (const₂ (# 1))  -- 9: domainCompLaw: (f · g) ◁ = ((f ◁) · g) ◁
        helper i10 const₁ = λ const₂ → ∘-assoc (const₂ (# 0)) (const₂ (# 1)) (const₂ (# 2))  -- 10: assocLaw: f · (g · h) = (f · g) · h

    -- The final category with both structure and laws
    SetCat : Σ[ A ∈ Structure₁ {AbsCatSig} ] inVariety₁ {ConFun} {AbsCatSig} AbsCatLaws A
    SetCat = (SetCatStruct , certifySetCat )

    