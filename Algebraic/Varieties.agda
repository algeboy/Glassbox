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

open import Algebraic.Signatures 
open import Algebraic.Structures 
open import Algebraic.Equations
open import Countable.Sets

module Algebraic.Varieties where 

    Variety : {sig : Signature} → Set₁
    Variety {sig} = Σ[ n ∈ ℕ ] Σ[ X ∈ Set ] ((Fin n) → (String × Equation {sig} X))

    {-- A mere proposition that states that an algebra satisfies an equation 
        for all interpretations of variables --}
    SatEqProp : ∀ {X : Set} 
              → {sig : Signature}
              → (alg : Structure {sig})
              → (eq : Equation {sig} X)
              → Set
    SatEqProp {X} {sig} alg eq = 
      (const : X → car {sig} alg)
      → evalFormula alg const (Equation.lhs eq) ≡ evalFormula alg const (Equation.rhs eq)


    {-- General proof that any algebra satisfies the reflexivity equation x = x --}
    -- Need a version of x=x that levels up -- 
    idEqPoly : {sig : Signature} → Equation {sig} (Fin 1)
    idEqPoly {sig} = record { lhs = var (# 0) ; rhs = var (# 0) }

    reflLawGeneral : { sig : Signature }
                   → (alg : Structure {sig})
                   → SatEqProp alg (idEqPoly {sig})
    reflLawGeneral alg = λ const → refl

    -- data Variety {sig : Signature} (X : Set) :  Set where 
    --   laws : List (Equation {sig} X) → Variety {sig} X

    -- "All" for dependent predicates over lists
    data All {A : Set} (P : A → Set) : List A → Set where
      []  : All P List.[]
      _∷_ : ∀ {x xs} → P x → All P xs → All P (x List.∷ xs)

    {-- A function that takes as input an algebra and a variety and stores a type that 
    if inhabited proves the algebra in the variety --}
    inVariety : ∀ {A : Set} → {sig : Signature} 
      → (V : Variety {sig})
      → (alg : Structure {sig})
      → Set
    inVariety {A} {sig} (n , X , eqs) alg = 
      (const : X → A) → (i : Fin n) → SatEqProp {X} {sig} alg (proj₂ (eqs i))

    {-- A mere proposition that states that a Structure₁ algebra satisfies an equation 
        for all interpretations of variables --}
    SatEqProp₁ : ∀ {X : Set} 
               → {sig : Signature}
               → (alg : Structure₁ {sig})
               → (eq : Equation {sig} X)
               → Set
    SatEqProp₁ {X} {sig} alg eq = 
      (const : X → car₁ {sig} alg)
      → evalFormula₁ alg const (Equation.lhs eq) ≡ evalFormula₁ alg const (Equation.rhs eq)

    {-- A function that takes as input a Structure₁ algebra and a variety and stores a type that 
    if inhabited proves the algebra in the variety --}
    inVariety₁ : ∀ {A : Set} → {sig : Signature} 
       → (V : Variety {sig})
       → (alg : Structure₁ {sig})
       → Set
    inVariety₁ {A} {sig} (n , X , eqs) alg = 
      (const : X → A) → (i : Fin n) → SatEqProp₁ {X} {sig} alg (proj₂ (eqs i))
