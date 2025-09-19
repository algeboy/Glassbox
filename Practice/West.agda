open import Agda.Primitive using (Level; lsuc; lzero; _⊔_)
open import Level using (Lift; lift)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; _*_)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup; toList)
open import Data.List as List using (List; []; _∷_; lookup; length; filter)
open import Data.Integer using (ℤ; _+_; -_; 0ℤ)
open import Data.Fin using (Fin; zero; suc; #_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open import Data.Nat.Base using (zero; suc)
open import Data.Fin.Base using (zero; suc)
open import Data.Vec.Base using (head; tail)
open import Relation.Nullary using (yes; no; Dec)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟ˢ_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Base using (_++_)

module West where

-- -----------------------------------------------------------------------------
-- Signatures
-- -----------------------------------------------------------------------------

-- Signature with left-normed grammar hence a name with a valence
record OpSig {ℓ : Level} : Set ℓ where
  field
    name : String -- eventually print and look up ops by name
    valence : ℕ

Signature : {ℓ : Level} → Set ℓ
Signature {ℓ} = List (OpSig {ℓ})

-- Look up operator by name
valForName : {ℓ : Level} → String → Signature {ℓ} → Maybe ℕ
valForName str ops = findHelper 0 ops
  where
    findHelper : ℕ → Signature {_} → Maybe ℕ
    findHelper _ [] = nothing
    findHelper n (op ∷ ops) with OpSig.name op ≟ˢ str
    ... | yes _ = just n
    ... | no  _ = findHelper (suc n) ops

-- Recursing over a Signature to print names
printOpNames : {ℓ : Level} → Signature {ℓ} → List String
printOpNames [] = []
printOpNames (op ∷ ops) = OpSig.name op ∷ printOpNames ops

-- -----------------------------------------------------------------------------
-- Algebraic Structures
-- -----------------------------------------------------------------------------

-- This is Definition 3.3 : Alge_Ω
record AlgeStruct {ℓ : Level} {sig : Signature {ℓ}} (carrier : Set ℓ) : Set ℓ where
  field
    ops : (i : Fin (List.length sig)) → 
          let op = List.lookup sig i 
          in Vec carrier (OpSig.valence op) → carrier


-- -----------------------------------------------------------------------------
-- Formulas, Equations, and Free Algebras
-- -----------------------------------------------------------------------------
  
-- A data type for formulas to become the carrier set.
data Formula {ℓ : Level} {sig : Signature {ℓ}} (X : Set ℓ) : Set ℓ where
  var  : (x : X) →  Formula {ℓ} {sig} X
  op   : (i : (Fin (List.length sig))) 
          → (Vec (Formula {ℓ} {sig} X) (OpSig.valence (List.lookup sig i))) 
          → Formula {ℓ} {sig} X


record Equation {ℓ : Level} {sig : Signature {ℓ}} (X : Set ℓ)  : Set ℓ where
  constructor _,_
  field
    lhs : Formula {ℓ} {sig} X
    rhs : Formula {ℓ} {sig} X


-- Evaluates a formula by interpreting variables and applying the 
-- operations from a target algebraic structure.
{-# TERMINATING #-}
evalFormula : {ℓ : Level} 
  → {sig : Signature {ℓ}}
  → {X A : Set ℓ}
  → (AlgeStruct {ℓ} {sig} A)
  → (X → A)
  → Formula {ℓ} {sig} X 
  → A
evalFormula alg const (var x) = const x
evalFormula alg const (op i args) =
  AlgeStruct.ops alg i (Vec.map (evalFormula alg const) args)

-- Conditional Equation: (∏ᵢ∈[n] Φᵢ(a) = Ψᵢ(a)) ⇒ Φ₀(a) = Ψ₀(a)
-- This represents implications of the form: if all premises hold, then conclusion holds
record ConditionalEquation {ℓ : Level} {sig : Signature {ℓ}} (X : Set ℓ) (n : ℕ) : Set ℓ where
  constructor _⇒_
  field
    premises   : Vec (Equation {ℓ} {sig} X) n  -- ∏ᵢ∈[n] Φᵢ(a) = Ψᵢ(a)
    conclusion : Equation {ℓ} {sig} X           -- Φ₀(a) = Ψ₀(a)

-- Helper to convert ConditionalEquations into the proper type for QuasiVariety
toExistential : ∀ {ℓ : Level} {sig : Signature {ℓ}} {X : Set ℓ} {n : ℕ} 
  → ConditionalEquation {ℓ} {sig} X n 
  → ∃ (λ m → ConditionalEquation {ℓ} {sig} X m)
toExistential {n = n} eq = n , eq

-- -- Alternative: Using function types for the logical implication
-- ConditionalEquation' : {ℓ : Level} {sig : Signature {ℓ}} (X : Set ℓ) (n : ℕ) → Set ℓ
-- ConditionalEquation' {ℓ} {sig} X n = 
--   ((i : Fin n) → Equation {ℓ} {sig} X) →  -- ∏ᵢ∈[n] equations
--   Equation {ℓ} {sig} X                     -- conclusion

-- Semantic version: actual logical implication with evaluation
ConditionalEquationSemantic : {ℓ : Level} {sig : Signature {ℓ}} (X A : Set ℓ) (n : ℕ) → Set ℓ
ConditionalEquationSemantic {ℓ} {sig} X A n =
  (premises : Vec (Equation {ℓ} {sig} X) n) →        -- ∏ᵢ∈[n] Φᵢ = Ψᵢ  
  (conclusion : Equation {ℓ} {sig} X) →               -- Φ₀ = Ψ₀
  (alg : AlgeStruct {ℓ} {sig} A) →                   -- target algebra
  (env : X → A) →                                     -- variable assignment
  ((i : Fin n) → let eq = Vec.lookup premises i in   -- if all premises hold
                 evalFormula alg env (Equation.lhs eq) ≡ 
                 evalFormula alg env (Equation.rhs eq)) →
  evalFormula alg env (Equation.lhs conclusion) ≡     -- then conclusion holds
  evalFormula alg env (Equation.rhs conclusion)


-- A free algebra maker
FreeAlge : {ℓ : Level} 
            → {sig : Signature {ℓ}} 
            → (X : Set ℓ) 
            → AlgeStruct {ℓ} {sig} (Formula {ℓ} {sig} X)
FreeAlge {ℓ} {sig} X = record
  { ops = λ i → λ args → op i args }


-- Option II if we don't want to cheat with "terminating" pragma. --
-- evalVec : {ℓ : Level} {sig : Signature {ℓ}} {X A : Set ℓ} {n : ℕ}
--         → (AlgeStruct {ℓ} {sig} A) → (X → A) 
--         → Vec (Formula {ℓ} {sig} X) n → Vec A n
-- evalVec alg const [] = []
-- evalVec alg const (f ∷ fs) = evalFormula alg const f ∷ evalVec alg const fs

-- evalFormula : {ℓ : Level} → {sig : Signature {ℓ}} → {X A : Set ℓ}
--             → (AlgeStruct {ℓ} {sig} A) → (X → A) → Formula {ℓ} {sig} X → A
-- evalFormula alg const (var x) = const x
-- evalFormula alg const (op i args) = AlgeStruct.ops alg i (evalVec alg const args)
--

-- -----------------------------------------------------------------------------
-- Satisfaction Varieties, & Conditional Satisfaction & Quasi-Varieites
-- -----------------------------------------------------------------------------


{-- A mere proposition that states that an algebra satisfies an equation 
    for all interpretations of variables --}
SatEqProp : ∀ {ℓ : Level} {X A : Set ℓ} {sig : Signature {ℓ} }
          → (alg : AlgeStruct {ℓ} {sig} A)
          → (eq : Equation {ℓ} {sig} X)
          → Set ℓ
SatEqProp {ℓ} {X} {A} {sig} alg eq = 
  (const : X → A) → evalFormula alg const (Equation.lhs eq) ≡ evalFormula alg const (Equation.rhs eq)


{-- General proof that any algebra satisfies the reflexivity equation x = x --}
-- Need a version of x=x that levels up -- 
idEqPoly : ∀ {ℓ : Level} {sig : Signature {ℓ}} → Equation {ℓ} {sig} (Lift ℓ (Fin 1))
idEqPoly = record { lhs = var (lift (# 0)) ; rhs = var (lift (# 0)) }

reflLawGeneral : ∀ {ℓ : Level } { A : Set ℓ } { sig : Signature {ℓ} }
               → (alg : AlgeStruct {ℓ} {sig} A)
               → SatEqProp alg idEqPoly
reflLawGeneral alg = λ const → refl

-- -----------------------------------------------------------------------------
-- A variety is a collection of equations that an algebra satisfies.

-- -----------------------------------------------------------------------------

-- a bit lazy, assuming we can pad all laws to be in the same variables.
data Variety {ℓ : Level} {sig : Signature {ℓ}} (X : Set ℓ) :  Set ℓ where 
  laws : List (Equation {ℓ} {sig} X) → Variety {ℓ} {sig} X

-- "All" for dependent predicates over lists
data All {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (P : A → Set ℓ₂) : List A → Set (ℓ₁ ⊔ ℓ₂) where
  []  : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

{-- A function that takes as input an algebra and a variety and stores a type that 
if inhabited proves the algebra in the variety --}
inVariety : ∀ {ℓ} {X A : Set ℓ} → {sig : Signature {ℓ}} 
  → (V : Variety {ℓ} {sig} X)
  → (alg : AlgeStruct {ℓ} {sig} A)
  → Set ℓ
inVariety {ℓ} {X} {A} {sig} (laws eqs) alg = 
  (const : X → A) → All (λ eq → SatEqProp alg eq) eqs


-- -----------------------------------------------------------------------------
-- A quasi-variety is a collection of conditional equations that an algebra satisfies.
-- -----------------------------------------------------------------------------

-- A quasi-variety contains conditional equations with potentially different numbers of premises
data QuasiVariety {ℓ : Level} {sig : Signature {ℓ}} (X : Set ℓ) : Set ℓ where 
  conditionalLaws : List (∃ (λ n → ConditionalEquation {ℓ} {sig} X n)) → QuasiVariety {ℓ} {sig} X

{-- A function that takes as input an algebra and a quasi-variety and stores a type that 
if inhabited proves the algebra satisfies all conditional equations in the quasi-variety --}
inQuasiVariety : ∀ {ℓ} {X A : Set ℓ} → {sig : Signature {ℓ}} 
  → (QV : QuasiVariety {ℓ} {sig} X)
  → (alg : AlgeStruct {ℓ} {sig} A)
  → Set ℓ
inQuasiVariety {ℓ} {X} {A} {sig} (conditionalLaws condEqs) alg = 
  (const : X → A) → All (λ { (n , condEq) → 
    let premises = ConditionalEquation.premises condEq
        conclusion = ConditionalEquation.conclusion condEq
    in ((i : Fin n) → let eq = Vec.lookup premises i in   -- if all premises hold
                      evalFormula alg const (Equation.lhs eq) ≡ 
                      evalFormula alg const (Equation.rhs eq)) →
       evalFormula alg const (Equation.lhs conclusion) ≡     -- then conclusion holds
       evalFormula alg const (Equation.rhs conclusion)
  }) condEqs


-- -----------------------------------------------------------------------------
-- Eastern Algebras
-- -----------------------------------------------------------------------------

-- The type of subsets of a list A
Subset : ∀ {ℓ} {A : Set ℓ} → List A → Set
Subset xs = List (Fin (length xs))

-- Generate all indices for a list of given length
allFins : (n : ℕ) → List (Fin n)
allFins zero = []
allFins (suc n) = zero ∷ List.map suc (allFins n)

-- Membership predicate for finite sets
_∈ₗ_ : ∀ {n} → Fin n → List (Fin n) → Set
i ∈ₗ [] = ⊥
i ∈ₗ (j ∷ js) = (i ≡ j) ⊎ (i ∈ₗ js)

-- Decidable membership check
_∈ₗ?_ : ∀ {n} → (i : Fin n) → (xs : List (Fin n)) → Dec (i ∈ₗ xs)
i ∈ₗ? [] = no (λ ())
i ∈ₗ? (j ∷ js) with i ≟ᶠ j
... | yes i≡j = yes (inj₁ i≡j)
... | no  i≢j with i ∈ₗ? js
... | yes i∈js = yes (inj₂ i∈js)
... | no  i∉js = no λ { (inj₁ i≡j) → i≢j i≡j ; (inj₂ i∈js) → i∉js i∈js }

-- Predicate to check if a formula only uses operators within tots
{-# TERMINATING #-}
usesOnlyTotalOps : ∀ {ℓ : Level} {sig : Signature {ℓ}} {X : Set ℓ}
  → (tots : Subset sig) → Formula {ℓ} {sig} X → Set ℓ
usesOnlyTotalOps {ℓ} tots (var x) = Lift ℓ ⊤
usesOnlyTotalOps {ℓ} tots (op i args) = 
  Lift ℓ ((i ∈ₗ tots) × (All (usesOnlyTotalOps tots) (Vec.toList args)))


-- Helper function to create a signature with only the total operations
restrictToTotal : {ℓ : Level} → (sig : Signature {ℓ}) → (tots : Subset sig) → Signature {ℓ}
restrictToTotal sig [] = []
restrictToTotal sig (i ∷ rest) = (List.lookup sig i) ∷ (restrictToTotal sig rest)

-- A total equation: an equation over the restricted signature (only total operations)
record TotalEquation {ℓ : Level} {sig : Signature {ℓ}} (X : Set ℓ) (tots : Subset sig) : Set ℓ where
  field
    equation : Equation {ℓ} {restrictToTotal sig tots} X


record East {ℓ : Level} {sig : Signature {ℓ}} {X A : Set ℓ} (carrier : Set ℓ) (tots : Subset sig) : Set ℓ where
  field
    totalOps : (i : Fin (List.length sig)) → (i ∈ₗ tots) → 
          let op = List.lookup sig i 
          in Vec carrier (OpSig.valence op) → carrier
    partialOps : (i : Fin (List.length sig)) → ¬ (i ∈ₗ tots) → 
          let op = List.lookup sig i 
          in Vec (Maybe carrier) (OpSig.valence op) → Maybe carrier
    guards : (i : Fin (List.length sig)) → ¬ (i ∈ₗ tots) → (TotalEquation {ℓ} {sig} X tots)
    guardedProp : ∀ (i : Fin (List.length sig)) (i∉tots : ¬ (i ∈ₗ tots))
                    (args : Vec (Maybe carrier) (OpSig.valence (List.lookup sig i)))
                    (totalAlg : AlgeStruct {ℓ} {restrictToTotal sig tots} carrier)
                    (sub : X → carrier) →
      let guard = guards i i∉tots
          eq = TotalEquation.equation guard
          -- Evaluate guard equation using only total operations
          guardHolds = evalFormula totalAlg sub (Equation.lhs eq) ≡ 
                       evalFormula totalAlg sub (Equation.rhs eq)
          partialResult = partialOps i i∉tots args
      in -- Partial operation is defined iff guard equation holds
         (guardHolds × ∃ (λ result → partialResult ≡ just result)) ⊎ 
         (¬ guardHolds × partialResult ≡ nothing)


-- -----------------------------------------------------------------------------
-- Lifting East to AlgeStruct by adding ⊥ (bot)
-- -----------------------------------------------------------------------------

-- Extended carrier type with bottom element
data Lifted {ℓ : Level} (A : Set ℓ) : Set ℓ where
  lift : A → Lifted A
  bot  : Lifted A

-- Extend signature by adding ⊥ as a 0-ary operator at the beginning
-- (Not needed for simple lifting approach, but kept for potential future use)
liftSignature : ∀ {ℓ : Level} → Signature {ℓ} → Signature {ℓ}
liftSignature sig = record { name = "⊥" ; valence = 0 } ∷ sig

-- Check if all elements in a vector are lifted (i.e. not bot)
allLifted : ∀ {ℓ n} {A : Set ℓ} → Vec (Lifted A) n → Bool
allLifted [] = true
allLifted (lift _ ∷ vs) = allLifted vs
allLifted (bot ∷ vs) = false

-- Extract values from lifted elements (partial)
unliftVec : ∀ {ℓ n} {A : Set ℓ} → Vec (Lifted A) n → Maybe (Vec A n)
unliftVec [] = just []
unliftVec (lift a ∷ vs) with unliftVec vs
... | just as = just (a ∷ as)
... | nothing = nothing
unliftVec (bot ∷ vs) = nothing

-- Lift a Maybe value to the Lifted type
liftMaybe : ∀ {ℓ} {A : Set ℓ} → Maybe A → Lifted A
liftMaybe (just a) = lift a
liftMaybe nothing = bot

-- -----------------------------------------------------------------------------
-- Lift East to AlgeStruct directly (without extending varieties)
-- -----------------------------------------------------------------------------

-- Lift the operations themselves to work on Lifted A
liftEastToAlgeStruct : ∀ {ℓ : Level} {sig : Signature {ℓ}} {X A : Set ℓ} {tots : Subset sig}
  → East {ℓ} {sig} {X} {A} A tots
  → AlgeStruct {ℓ} {sig} (Lifted A)
liftEastToAlgeStruct {ℓ} {sig} {X} {A} {tots} east = record
  { ops = liftedOps }
  where
    liftedOps : (i : Fin (List.length sig)) → 
                let op = List.lookup sig i 
                in Vec (Lifted A) (OpSig.valence op) → Lifted A
    
    liftedOps i args with unliftVec args
    ... | nothing = bot  -- If any input is bot, output is bot
    ... | just realArgs with i ∈ₗ? tots  -- Check if operator i is total
    ... | yes i∈tots = lift (East.totalOps east i i∈tots realArgs)
    ... | no  i∉tots = liftMaybe (East.partialOps east i i∉tots (Vec.map just realArgs))

