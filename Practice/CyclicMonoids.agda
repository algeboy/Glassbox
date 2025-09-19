-- -----------------------------------------------------------------------------
-- Cyclic Monoids
-- -----------------------------------------------------------------------------
open import Data.Product using (_,_; proj₁; proj₂)     -- Dependent types --
open import Data.List as List using (List; []; _∷_)
open import Data.String using (String) -- Strings for operator names --
open import Data.Fin using (Fin; toℕ; #_; zero; suc)
open import Data.Nat as Nat using (ℕ; _+_; zero; suc)
open import Data.Nat.DivMod using (_mod_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Nat.Properties using (+-identityʳ; +-identityˡ;
                                        +-comm; +-assoc)
open import Data.Fin.Properties using (toℕ-inject₁; toℕ-fromℕ)

open import Data.List as List using (List; []; _∷_; lookup; length; filter)


open import Signatures using (Signature; asSignature)
open import AlgebraicStructures using (AlgeStruct; Operator; OpData; asAlgeStruct; getSignature)
open import Equations using (Formula; Equation; var; op; evalFormula)
open import Varieties using (SatEqProp)
open import FreeAlgebras using (FreeAlge)

open import Monoids using (MonoidSig; 
                           rightIdentityLaw; 
                           leftIdentityLaw; 
                           associativityLaw;
                           _·_;
                           e)

module CyclicMonoids where 


    -- -----------------------------------------------------
    -- Modulo integer monoid.
    -- -----------------------------------------------------
    ℕ/ : (n : ℕ) → Set
    ℕ/ Nat.zero = ℕ -- ℕ/ 0 = ℕ 
    ℕ/ n = Fin n

    add : {n : ℕ} → Vec (ℕ/ n) 2 → ℕ/ n
    add {Nat.zero} (a ∷ b ∷ []) = a + b -- Natural numbers
    add {Nat.suc n} (a ∷ b ∷ []) = (toℕ a + toℕ b) mod (Nat.suc n)

    zeta : {n : ℕ} → Vec (ℕ/ n) 0 → ℕ/ n
    zeta {Nat.zero} [] = Nat.zero -- Natural numbers
    zeta {Nat.suc n} [] = Fin.zero  -- Zero of Fin (suc n)

    ModuloMonoidUnsafe : (n : ℕ) → AlgeStruct MonoidSig
    ModuloMonoidUnsafe n = (ℕ/ n , operations )
      where
        operations : (i : Fin 2) → (Operator (ℕ/ n) (proj₂ MonoidSig i))
        operations Fin.zero = zeta {n}         
        operations (Fin.suc Fin.zero) = add {n}

    -- -----------------------------------------------------
    -- Make Free Monoid on x isomorphic to N.
    -- -----------------------------------------------------
    -- FreeCyclic : AlgeStruct MonoidSig
    -- FreeCyclic = FreeAlge (Fin 1)

    -- iso : FreeCyclic ≅ ModuloMonoidUnsafe 0
    -- iso = λ formula → evalFormula formula (# 0)

    -- -----------------------------------------------------
    -- Laws we bother with, fetch things known from Agda libraries.
    -- -----------------------------------------------------

    -- Already in the library
    freeLeftIdProof : (const : Monoids.X → ℕ/ 0) → 
            evalFormula (ModuloMonoidUnsafe 0) const (Equation.lhs leftIdentityLaw) ≡ 
            evalFormula (ModuloMonoidUnsafe 0) const (Equation.rhs leftIdentityLaw)
    freeLeftIdProof const = +-identityˡ (const (# 0))

    freeLeftIdLaw : SatEqProp MonoidSig (ModuloMonoidUnsafe 0) leftIdentityLaw  
    freeLeftIdLaw = λ const → freeLeftIdProof const

    freeRightIdProof : (const : Monoids.X → ℕ/ 0) → 
            evalFormula (ModuloMonoidUnsafe 0) const (Equation.lhs rightIdentityLaw) ≡ 
            evalFormula (ModuloMonoidUnsafe 0) const (Equation.rhs rightIdentityLaw)
    freeRightIdProof const = +-identityʳ (const (# 0))

    freeRightIdLaw : SatEqProp MonoidSig (ModuloMonoidUnsafe 0) rightIdentityLaw  
    freeRightIdLaw = λ const → freeRightIdProof const

    -- Already in the library
    freeAssociativityProof : (const : Monoids.X → ℕ/ 0) → 
            evalFormula (ModuloMonoidUnsafe 0) const (Equation.lhs associativityLaw) ≡ 
            evalFormula (ModuloMonoidUnsafe 0) const (Equation.rhs associativityLaw)
    freeAssociativityProof const = +-assoc (const (# 0)) (const (# 1)) (const (# 2))

    -- postulate
    --   rightIdProof : {n : ℕ} → (const : Monoids.X → ℕ/ n) → 
    --               evalFormula (ModuloMonoidUnsafe n) const (Equation.lhs rightIdentityLaw) ≡ 
    --               evalFormula (ModuloMonoidUnsafe n) const (Equation.rhs rightIdentityLaw)

    -- cycRightIdLaw : ∀ {n : ℕ} → SatEqProp MonoidSig (ModuloMonoidUnsafe n) rightIdentityLaw  
    -- cycRightIdLaw {n} = λ const → rightIdProof {n} const
    -- postulate
    --   leftIdProof : {n : ℕ} → (const : Monoids.X → ℕ/ n) → 
    --               evalFormula (ModuloMonoidUnsafe n) const (Equation.lhs leftIdentityLaw) ≡ 
    --               evalFormula (ModuloMonoidUnsafe n) const (Equation.rhs leftIdentityLaw)

    -- cycLeftIdLaw : ∀ {n : ℕ} → SatEqProp MonoidSig (ModuloMonoidUnsafe n) leftIdentityLaw  
    -- cycLeftIdLaw {n} = λ const → leftIdProof {n} const

