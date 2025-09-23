
{-# OPTIONS --allow-unsolved-metas #-}

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

-- Used for signature & algebraic structure build.
open import Data.String using (String)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
-----------------------------------------------------

open import Algebraic.Homomorphism

{-- A minimal countable constructive set category. --}
module Algebraic.HomCategories where


    HomCatStruct : (sig : Signature ) → ACatStruct
    HomCatStruct sig = (Hom {sig} , ops )
        where
        ops : (i : Fin 4) → (Operator₁ (Hom {sig}) (proj₂ (proj₂ AbsCatSig i)))
        ops Fin.zero = λ _ → null ▦ refl        -- identity element (valence 0)
        ops (Fin.suc Fin.zero) = composeConFun  -- binary operation (valence 2)
            where
            composeConFun : Vec (Hom {sig}) 2 → Hom {sig}
            composeConFun (f ∷ g ∷ []) = f ∘ g
        ops (Fin.suc (Fin.suc Fin.zero)) = srcConFun  -- source (valence 1)
            where
            srcConFun : Vec (Hom {sig}) 1 → Hom {sig}
            srcConFun (f ∷ []) = f ◄◄
        ops (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = tgtConFun  -- target (valence 1)
            where
            tgtConFun : Vec (Hom {sig}) 1 → Hom {sig}
            tgtConFun (f ∷ []) = ◄◄ f

    -- HomCat satisfies all the abstract category laws
    certifyHomCat : (sig : Signature) → inVariety₁ {Hom {sig}} {AbsCatSig} AbsCatLaws (HomCatStruct sig)
    certifyHomCat sig const i = helper i const
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

        helper : (i : Fin 11) → (const : Fin 3 → Hom {sig}) → SatEqProp₁ {Fin 3} {AbsCatSig} (HomCatStruct sig) (proj₂ (proj₂ (proj₂ AbsCatLaws) i))
        helper i0  const₁ = λ const₂ → {!!}     -- 0: leftSinkCompLaw: □ · g = □
        helper i1  const₁ = λ const₂ → {!!}     -- 1: rightSinkCompLaw: f · □ = □
        helper i2  const₁ = λ const₂ → {!!}     -- 2: sinkSrcLaw: □ ◁ = □
        helper i3  const₁ = λ const₂ → {!!}     -- 3: sinkTgtLaw: ◁ □ = □
        helper i4  const₁ = λ const₂ → {!!}     -- 4: codomainDomainLaw: ◁ (f ◁) = f ◁
        helper i5  const₁ = λ const₂ → {!!}     -- 5: domainCodomainLaw: (◁ f) ◁ = ◁ f
        helper i6  const₁ = λ const₂ → {!!}     -- 6: codomainLeftIdLaw: (◁ f) · f = f
        helper i7  const₁ = λ const₂ → {!!}     -- 7: domainRightIdLaw: f · (f ◁) = f
        helper i8  const₁ = λ const₂ → {!!}     -- 8: codomainCompLaw: ◁ (f · g) = ◁ (f · (◁ g))
        helper i9  const₁ = λ const₂ → {!!}     -- 9: domainCompLaw: (f · g) ◁ = ((f ◁) · g) ◁
        helper i10 const₁ = λ const₂ → {!!}     -- 10: assocLaw: f · (g · h) = (f · g) · h


    HomCat : (sig : Signature) → ACat
    HomCat sig = (HomCatStruct sig , certifyHomCat sig )
    