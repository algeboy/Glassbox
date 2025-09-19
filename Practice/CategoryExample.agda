open import Agda.Primitive using (Level; lsuc; lzero; _⊔_)
open import Data.Integer using (ℤ; _+_; -_; 0ℤ; +_; _*_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_; lookup; length)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Product using (∃; _,_)

-- Import our algebraic structures
open import West

module CategoryExample where

-- Define infix operators for readability
-- Valence 1 operators have higher precedent than composition
infix 99 _◄
infix 99 ◄_
infix 98 _·_

-- -----------------------------------------------------------------------------
-- Composition Signature
-- -----------------------------------------------------------------------------

-- Composition operations: domain (_◄), codomain (◄_), and composition (_·_)
compositionSig : ∀ {ℓ : Level} → Signature {ℓ}
compositionSig = record { name = "dom" ; valence = 1 } ∷
                 record { name = "cod" ; valence = 1 } ∷  
                 record { name = "comp" ; valence = 2 } ∷
                 []

-- Define the infix operators as in paper using direct position indices
_◄ : ∀ {ℓ : Level} {X : Set ℓ} → Formula {ℓ} {compositionSig} X → Formula {ℓ} {compositionSig} X
_◄ t = op (# 0) (t ∷ [])

◄_ : ∀ {ℓ : Level} {X : Set ℓ} → Formula {ℓ} {compositionSig} X → Formula {ℓ} {compositionSig} X
◄_ t = op (# 1) (t ∷ [])

_·_ : ∀ {ℓ : Level} {X : Set ℓ} → Formula {ℓ} {compositionSig} X → Formula {ℓ} {compositionSig} X → Formula {ℓ} {compositionSig} X
_·_ t₁ t₂ = op (# 2) (t₁ ∷ t₂ ∷ [])


-- -----------------------------------------------------------------------------
-- Composition Quasi-Variety
-- -----------------------------------------------------------------------------

-- Variables for composition laws
X : Set
X = Fin 3

x y z : X
x = # 0
y = # 1  
z = # 2

-- Convenient variable formulas for readability
f g h : Formula {lzero} {compositionSig} X
f = var x
g = var y
h = var z

codomainDomainLaw : ConditionalEquation {lzero} {compositionSig} X 0
codomainDomainLaw = [] ⇒ (◄ (f ◄) , f ◄)

domainCodomainLaw : ConditionalEquation {lzero} {compositionSig} X 0
domainCodomainLaw = [] ⇒ ((◄ f) ◄ , ◄ f)

codomainLeftIdLaw : ConditionalEquation {lzero} {compositionSig} X 0
codomainLeftIdLaw = [] ⇒ ((◄ f) · f , f)

domainRightIdLaw : ConditionalEquation {lzero} {compositionSig} X 0
domainRightIdLaw = [] ⇒ (f · (f ◄) , f)

codomainCompLaw : ConditionalEquation {lzero} {compositionSig} X 1
codomainCompLaw = ((f ◄ , ◄ g) ∷ []) ⇒ (◄ (f · g) , ◄ (f · (◄ g)))

domainCompLaw : ConditionalEquation {lzero} {compositionSig} X 1
domainCompLaw = ((f ◄ , ◄ g) ∷ []) ⇒ ((f · g) ◄ , ((f ◄) · g) ◄)

assocLaw : ConditionalEquation {lzero} {compositionSig} X 2
assocLaw = ((g ◄ , ◄ h) ∷ (f ◄ , ◄ g) ∷ []) ⇒ (f · (g · h) , (f · g) · h)

CompositionQuasiVariety : QuasiVariety {lzero} {compositionSig} X
CompositionQuasiVariety = conditionalLaws (
    toExistential codomainDomainLaw ∷ 
    toExistential domainCodomainLaw ∷ 
    toExistential codomainLeftIdLaw ∷ 
    toExistential domainRightIdLaw ∷ 
    toExistential codomainCompLaw ∷ 
    toExistential domainCompLaw ∷ 
    toExistential assocLaw ∷ 
    []
  )

