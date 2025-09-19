open import Agda.Primitive using (Level; lsuc; lzero; _⊔_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List as List using (List; _∷_; [])
open import Data.Product using (∃; _,_)

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Fin using (Fin; toℕ; #_; zero; suc)

open import Data.Maybe using (Maybe; just)

open import Relation.Binary.PropositionalEquality using (refl; subst; _≡_)
open import Data.Bool using (if_then_else_; true; false)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Function using (_∘_)

open import Algebras
open import Equations
open import ConSet

{-- A minimal category of countable constructive set theory. --}
module ConSetCat where

    -- Composition Signature
    -- -----------------------------------------------------------------------------
    
    -- Composition operations: domain (_◄), codomain (◄_), and composition (_·_)
    catSig : ∀ {ℓ : Level} → Signature {ℓ}
    catSig = record { name = "src" ; valence = 1 } List.∷
             record { name = "tgt" ; valence = 1 } List.∷
             record { name = "comp" ; valence = 2 } List.∷
             record { name = "null" ; valence = 0 } List.∷
             List.[]

    -- -----------------------------------------------------
    -- Inhabiting with ConSet
    -- -----------------------------------------------------
    ConSetCat : AlgeStruct {lzero} {catSig} ConFun
    ConSetCat = record { ops = catop }
      where
        catop : (i : Fin 4) → 
                let op = List.lookup catSig i 
                in Vec ConFun (OpSig.valence op) → ConFun
        catop zero (arg Vec.∷ Vec.[]) = _◄ arg    -- "src" with valence 1
        catop (suc zero) (arg Vec.∷ Vec.[]) = ◄_ arg    -- "tgt" with valence 1
        catop (suc (suc zero)) (arg1 Vec.∷ arg2 Vec.∷ Vec.[]) = _←_ arg1 arg2  -- "comp" with valence 2
        catop (suc (suc (suc zero))) Vec.[] = ▦               -- "null" with valence 0


    -- -----------------------------------------------------
    -- Adding in laws
    -- -----------------------------------------------------

    -- Define the infix operators as in paper using direct position indices
    _◁ : ∀ {ℓ : Level} {X : Set ℓ} → Formula {ℓ} {catSig} X → Formula {ℓ} {catSig} X
    _◁ t = op (# 0) (t Vec.∷ Vec.[])

    ◁_ : ∀ {ℓ : Level} {X : Set ℓ} → Formula {ℓ} {catSig} X → Formula {ℓ} {catSig} X
    ◁_ t = op (# 1) (t Vec.∷ Vec.[])

    _·_ : ∀ {ℓ : Level} {X : Set ℓ} → Formula {ℓ} {catSig} X → Formula {ℓ} {catSig} X → Formula {ℓ} {catSig} X
    _·_ t₁ t₂ = op (# 2) (t₁ Vec.∷ t₂ Vec.∷ Vec.[])

    {-- Identity laws --}

    -- Variables for composition laws
    X : Set
    X = Fin 3

    x y z : X
    x = # 0
    y = # 1  
    z = # 2

    -- Convenient variable formulas for readability
    f g h : Formula {lzero} {catSig} X
    f = var x
    g = var y
    h = var z

    targetSourceLaw : Equation {lzero} {catSig} X
    targetSourceLaw = (◁ (f ◁) , f ◁)

    sourceTargetLaw : Equation {lzero} {catSig} X
    sourceTargetLaw = ((◁ f) ◁ , ◁ f)

    targetLeftIdLaw : Equation {lzero} {catSig} X
    targetLeftIdLaw = ((◁ f) · f , f)

    sourceRightIdLaw : Equation {lzero} {catSig} X
    sourceRightIdLaw = (f · (f ◁) , f)

    targetCompLaw : Equation {lzero} {catSig} X
    targetCompLaw = (◁ (f · g) , ◁ (f · (◁ g)))

    sourceCompLaw : Equation {lzero} {catSig} X
    sourceCompLaw = ((f · g) ◁ , ((f ◁) · g) ◁)

    {-- Associativity: (x · y) · z = x · (y · z) --}
    assocLaw : Equation {lzero} {catSig} X
    assocLaw = (f · (g · h) , (f · g) · h)

    -- Abstract Category Variety
    ACatVariety : Variety {lzero} {catSig} X
    ACatVariety = laws (
        targetSourceLaw List.∷ 
        sourceTargetLaw List.∷ 
        targetLeftIdLaw List.∷ 
        sourceRightIdLaw List.∷ 
        targetCompLaw List.∷
        sourceCompLaw List.∷
        assocLaw List.∷
        List.[]
        )

    -- Inhabit the laws.
    ConFunIsACat : inVariety {lzero} {X} {A} {sig} (laws eqs) alg 
    