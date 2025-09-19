-- -- -----------------------------------------------------------------------------
-- -- A variety is a collection of equations that an algebra satisfies.
-- -- -----------------------------------------------------------------------------
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)     -- Dependent types --

open import Data.Nat using (ℕ)         -- Nats for valence --
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.String using (String) -- Strings for operator names --
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


open import Data.List as List using (List; lookup; length)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup; toList)
open import Data.Product using (proj₁; proj₂)

open import Signatures using (Signature; valence; nOps)
open import AlgebraicStructures using (AlgeStruct; Operator; getOp; getCarrier)
open import Equations using (Formula; Equation; var; op; evalFormula)

module Varieties where 

    Variety : (sig : Signature) → Set₁ 
    Variety sig = Σ[ n ∈ ℕ ] Σ[ X ∈ Set ] ((Fin n) → (String × Equation sig X))

    {-- A mere proposition that states that an algebra satisfies an equation 
        for all interpretations of variables --}
    SatEqProp : ∀ {X : Set} 
              → (sig : Signature)
              → (alg : AlgeStruct sig)
              → (eq : Equation sig X)
              → Set
    SatEqProp {X} sig alg eq = 
      (const : X → proj₁ alg) 
      → evalFormula alg const (Equation.lhs eq) ≡ evalFormula alg const (Equation.rhs eq)


    {-- General proof that any algebra satisfies the reflexivity equation x = x --}
    -- Need a version of x=x that levels up -- 
    idEqPoly : (sig : Signature) → Equation sig (Fin 1)
    idEqPoly sig = record { lhs = var (# 0) ; rhs = var (# 0) }

    reflLawGeneral : ( sig : Signature )
                   → (alg : AlgeStruct sig)
                   → SatEqProp sig alg (idEqPoly sig)
    reflLawGeneral sig alg = λ const → refl


    -- data Variety {sig : Signature} (X : Set) :  Set where 
    --   laws : List (Equation {sig} X) → Variety {sig} X

    "All" for dependent predicates over lists
    data All {A : Set} (P : A → Set) : List A → Set where
      []  : All P []
      _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

    {-- A function that takes as input an algebra and a variety and stores a type that 
    if inhabited proves the algebra in the variety --}
    inVariety : ∀  {X A : Set} → {sig : Signature} 
      → (V : Variety {sig} X)
      → (alg : AlgeStruct {sig} A)
      → Set
    inVariety {X} {A} {sig} (laws eqs) alg = 
      (const : X → A) → All (λ eq → SatEqProp alg eq) eqs
