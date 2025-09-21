
open import Data.Nat using (ℕ; _≟_)
open import Data.Fin using (Fin; #_)
open import Data.Product using (_×_; _,_)
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (Dec; yes; no)


open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl; subst; _≡_; cong; sym; trans; subst-∘)
open import Relation.Nullary using (yes; no; Dec)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import Function using (_∘_; id)


open import Algebraic.Signatures
open import Countable.Sets
open import Algebraic.Structures
open import Algebraic.Equations
open import Algebraic.Varieties

-- Used for signture & algebraic structure build.
open import Data.String using (String)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
-----------------------------------------------------

module Algebraic.AbstractCategory where 

    {-- As an abstract category is a set of morphisms --}
    AbsCatSig : Signature
    AbsCatSig = (4 , λ i → lookup operations i)
        where
        operations : Vec (String × ℕ) 4
        operations = ("□" , 0) ∷ ("_·_" , 2) ∷ ("_◁" , 1) ∷ ("◁_" , 1) ∷ []

    □ : ∀ {X : Set} → Formula {AbsCatSig} X
    □ {X} = op (# 0) []

    _·_ : ∀ {X : Set} → Formula {AbsCatSig} X → Formula {AbsCatSig} X → Formula {AbsCatSig} X
    _·_ t₁ t₂ = op (# 1) (t₁ ∷ t₂ ∷ [])

    _◁ : ∀ {X : Set} → Formula {AbsCatSig} X → Formula {AbsCatSig} X
    _◁ t = op (# 2) (t ∷ [])

    ◁_ : ∀ {X : Set} → Formula {AbsCatSig} X → Formula {AbsCatSig} X
    ◁_ t = op (# 3) (t ∷ [])


    -- Variables for composition laws
    X : Set
    X = Fin 3

    x y z : X
    x = # 0
    y = # 1  
    z = # 2

    -- Convenient variable formulas for readability
    f g h : Formula {AbsCatSig} X
    f = var x
    g = var y
    h = var z

    {-- □ is a sink for all operations --}
    leftSinkCompLaw : Equation {AbsCatSig} X
    leftSinkCompLaw = record { lhs = □ · g ; rhs = □ }

    rightSinkCompLaw : Equation {AbsCatSig} X
    rightSinkCompLaw = record { lhs = f · □ ; rhs = □ }

    sinkSrcLaw : Equation {AbsCatSig} X
    sinkSrcLaw = record { lhs = □ ◁ ; rhs = □ }

    sinkTgtLaw : Equation {AbsCatSig} X
    sinkTgtLaw = record { lhs = ◁ □ ; rhs = □ }

    {-- Source and target laws --}
    codomainDomainLaw : Equation {AbsCatSig} X
    codomainDomainLaw = record { lhs = ◁ (f ◁) ; rhs = f ◁ }

    domainCodomainLaw : Equation {AbsCatSig} X
    domainCodomainLaw = record { lhs = (◁ f) ◁ ; rhs = ◁ f }

    {-- Composition with sources and targets --}
    codomainLeftIdLaw : Equation {AbsCatSig} X
    codomainLeftIdLaw = record { lhs = (◁ f) · f ; rhs = f }

    domainRightIdLaw : Equation {AbsCatSig} X
    domainRightIdLaw = record { lhs = f · (f ◁) ; rhs = f }

    codomainCompLaw : Equation {AbsCatSig} X
    codomainCompLaw = record { lhs = ◁ (f · g) ; rhs = ◁ (f · (◁ g)) }

    domainCompLaw : Equation {AbsCatSig} X
    domainCompLaw = record { lhs = (f · g) ◁ ; rhs = ((f ◁) · g) ◁ }

    {-- Associativity of composition --}
    assocLaw : Equation {AbsCatSig} X
    assocLaw = record { lhs = f · (g · h) ; rhs = (f · g) · h }

    -- Variety {sig} = Σ[ n ∈ ℕ ] Σ[ X ∈ Set ] ((Fin n) → (String × Equation {sig} X))
    AbsCatLaws :  Variety {AbsCatSig}
    AbsCatLaws = (11 , X , helper)
      where
        lawsVector : Vec (String × Equation {AbsCatSig} X) 11
        lawsVector = 
          ("leftSinkCompLaw" , leftSinkCompLaw) ∷
          ("rightSinkCompLaw" , rightSinkCompLaw) ∷
          ("sinkSrcLaw" , sinkSrcLaw) ∷
          ("sinkTgtLaw" , sinkTgtLaw) ∷
          ("codomainDomainLaw" , codomainDomainLaw) ∷
          ("domainCodomainLaw" , domainCodomainLaw) ∷
          ("codomainLeftIdLaw" , codomainLeftIdLaw) ∷
          ("domainRightIdLaw" , domainRightIdLaw) ∷
          ("codomainCompLaw" , codomainCompLaw) ∷
          ("domainCompLaw" , domainCompLaw) ∷
          ("assocLaw" , assocLaw) ∷ []
          
        helper : Fin 11 → String × Equation {AbsCatSig} X
        helper i = lookup lawsVector i