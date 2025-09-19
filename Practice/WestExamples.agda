open import Agda.Primitive using (Level; lsuc; lzero; _⊔_)
open import Level using (Lift; lift)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Nat using (ℕ)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup)
open import Data.List as List using (List; []; _∷_; lookup; length)
open import Data.Integer using (ℤ; _+_; -_; 0ℤ)
open import Data.Fin using (Fin; zero; suc; #_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open import Data.Nat.Base using (zero; suc)
open import Data.Fin.Base using (zero; suc)
open import Data.Vec.Base using (head; tail)
open import Relation.Nullary using (yes; no)
open import Data.String using (String; _≟_)
open import West

module WestExamples where

-- Example: a set of OpSig for basic arithmetic operations
ADDSIG : Signature {lzero} 
ADDSIG =
  record { name = "zero" ; valence = 0 } ∷
  record { name = "succ" ; valence = 1 } ∷
  record { name = "add" ; valence = 2 } ∷
  []

-- Sanity check: Algebraic structures always have an initial object 
-- whose carrier is a singleton set.
-- Singleton ⊤
record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt

InitialAlgeStruct : {ℓ : Level} → (sig : Signature {ℓ}) → AlgeStruct {ℓ} {sig} (⊤ {ℓ})
InitialAlgeStruct sig = record
  { ops = λ opIndex → λ _ → tt }



-- Example 1:  x_42 in a 541 variables.
x42 : Formula {lzero} {ADDSIG} (Fin 541)
x42 = var (# 42)

-- Example 2: zero as operator
zz : Formula {lzero} {ADDSIG} (Fin 541)
zz = op (# 0) []

-- Example 3: two as formula 
two : Formula {lzero} {ADDSIG} (Fin 541)
two = op (# 1) ( (op (# 1) (zz ∷ [])) ∷ [] )

-- Example 3: x_42 + 2 as formula 
x42PlusTwo : Formula {lzero} {ADDSIG} (Fin 541)
x42PlusTwo = op (# 2) (x42 ∷ two ∷ [])


-- Example: Equation with x42PlusTwo as lhs and zz as rhs
randomEq : Equation {lzero} {ADDSIG} (Fin 541)
randomEq = record { lhs = x42PlusTwo ; rhs = zz }


-- x = x
idEq : Equation {lzero} {ADDSIG} (Fin 1)
idEq = record { lhs = var (# 0) ; rhs = var (# 0) }



-- Example: Simple conditional equation with one premise
-- If x + 0 = x, then 0 + x = x (commutativity from right identity)
exampleConditional : ConditionalEquation {lzero} {ADDSIG} (Fin 1) 1
exampleConditional = record
  { premises = record { lhs = op (# 2) (var (# 0) ∷ op (# 0) [] ∷ [])  -- x + 0
                       ; rhs = var (# 0) } ∷ []                         -- = x
  ; conclusion = record { lhs = op (# 2) (op (# 0) [] ∷ var (# 0) ∷ []) -- 0 + x  
                         ; rhs = var (# 0) }                            -- = x
  }

-- Example: Multiple premises
-- If x + y = y + x and (x + y) + z = x + (y + z), then something follows
exampleMultiplePremises : ConditionalEquation {lzero} {ADDSIG} (Fin 3) 2
exampleMultiplePremises = record
  { premises = 
      -- Premise 1: x + y = y + x (commutativity)
      record { lhs = op (# 2) (var (# 0) ∷ var (# 1) ∷ [])
             ; rhs = op (# 2) (var (# 1) ∷ var (# 0) ∷ []) } ∷
      -- Premise 2: (x + y) + z = x + (y + z) (associativity)  
      record { lhs = op (# 2) (op (# 2) (var (# 0) ∷ var (# 1) ∷ []) ∷ var (# 2) ∷ [])
             ; rhs = op (# 2) (var (# 0) ∷ op (# 2) (var (# 1) ∷ var (# 2) ∷ []) ∷ []) } ∷ []
  ; conclusion = 
      -- Conclusion: some derived property
      record { lhs = var (# 0) ; rhs = var (# 0) }  -- placeholder
  }

-- -- x = x (polymorphic version that levels up)
-- idEqPoly : ∀ {ℓ : Level} {sig : Signature {lzero}} → Equation {lzero} {sig} (Fin 1)
-- idEqPoly = record { lhs = var (# 0) ; rhs = var (# 0) }



-- Example: Free algebra over AddOps with variables from ℕ
FreeAddAlge2Vars : AlgeStruct {lzero} {ADDSIG} (Formula {lzero} {ADDSIG} (Fin 2))
FreeAddAlge2Vars = FreeAlge (Fin 2)


{-- Proof that InitialAlgeStruct satisfies the equation var 0 = var 0, i.e. x=x --}
trivialReflLaw : SatEqProp (InitialAlgeStruct ADDSIG) idEq
trivialReflLaw = λ const → refl

{-- Proof that InitialAlgebra satisfies the equation x_42 + 2 = 0 --}
randomLaw : SatEqProp (InitialAlgeStruct ADDSIG) randomEq
randomLaw = λ const → refl



{-- Example: Variety with idEqPoly as its only law --}
IdVariety : ∀ {ℓ : Level} {sig : Signature {ℓ}} → Variety {ℓ} {sig} (Lift ℓ (Fin 1))
IdVariety {ℓ} {sig} = laws (idEqPoly ∷ [])

{-- Example: Variety with idEq and randomEq as its laws --}
-- HACK: I am too lazy to have made the number of variables in formulas for varieties variable.
-- So I have to redefine x=x to be in 541 variables.
idEq541 : Equation {lzero} {ADDSIG} (Fin 541)
idEq541 = record { lhs = var (# 0) ; rhs = var (# 0) }

IdRandomVariety : Variety {lzero} {ADDSIG} (Fin 541)
IdRandomVariety = laws (idEq541 ∷ randomEq ∷ [])


{-- Proving that the initial algebra is in the random variety with x_42+2=0--}
InitialInIdRandomVariety : inVariety IdRandomVariety (InitialAlgeStruct ADDSIG)
InitialInIdRandomVariety const = 
  -- Proof for idEq541: var 0 = var 0
  (λ const₁ → refl) ∷ 
  -- Proof for randomEq: x_42 + 2 = 0  
  (λ const₁ → refl) ∷ 
  []


{-- Example: QuasiVariety with our simple conditional equation --}
SimpleQuasiVariety : QuasiVariety {lzero} {ADDSIG} (Fin 1)
SimpleQuasiVariety = conditionalLaws ((1 , exampleConditional) ∷ [])

{-- Example: QuasiVariety with multiple conditional equations --}
MultipleQuasiVariety : QuasiVariety {lzero} {ADDSIG} (Fin 3)
MultipleQuasiVariety = conditionalLaws (
  (1 , exampleConditional') ∷ 
  (2 , exampleMultiplePremises) ∷ [])
  where
    -- Adapted exampleConditional for 3 variables instead of 1
    exampleConditional' : ConditionalEquation {lzero} {ADDSIG} (Fin 3) 1
    exampleConditional' = record
      { premises = record { lhs = op (# 2) (var (# 0) ∷ op (# 0) [] ∷ [])  -- x + 0
                           ; rhs = var (# 0) } ∷ []                         -- = x
      ; conclusion = record { lhs = op (# 2) (op (# 0) [] ∷ var (# 0) ∷ []) -- 0 + x  
                             ; rhs = var (# 0) }                            -- = x
      }

{-- Example: Proving that the initial algebra is in SimpleQuasiVariety --}
InitialInSimpleQuasiVariety : inQuasiVariety SimpleQuasiVariety (InitialAlgeStruct ADDSIG)
InitialInSimpleQuasiVariety const = 
  -- Proof for exampleConditional: if x + 0 = x then 0 + x = x
  (λ premiseProof → refl) ∷ 
  []
