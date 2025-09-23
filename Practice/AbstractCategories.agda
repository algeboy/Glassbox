-- open import Agda.Primitive using (Level; lsuc; lzero; _⊔_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_; lookup; length)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import CategoryExample using (compositionSig; CompositionQuasiVariety)

open import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open Eq.≡-Reasoning      -- brings begin_, _≡⟨_⟩_, _≡⟨⟩_, _∎ into scope

-- Import our algebraic structures
open import Algebras
open import Equations

module AbstractCategories where

-- -----------------------------------------------------------------------------
-- Abstract Category Signature
-- -----------------------------------------------------------------------------
    
-- Composition operations: domain (_◄), codomain (◄_), and composition (_·_)
catSig : ∀ {ℓ : Level} → Signature {ℓ}
catSig = record { name = "src" ; valence = 1 } List.∷
          record { name = "tgt" ; valence = 1 } List.∷
          record { name = "comp" ; valence = 2 } List.∷
          record { name = "null" ; valence = 0 } List.∷
          List.[]


-- Define infix operators for readability
infix 6 _·_
infix 8 _⁻¹
infix 9 e

-- Define the infix operators using direct position indices
_·_ : Formula {groupSig} (Fin 3) → Formula {groupSig} (Fin 3) → Formula {groupSig} (Fin 3)
_·_ t₁ t₂ = op (# 0) (t₁ ∷ t₂ ∷ [])

_⁻¹ : Formula {groupSig} (Fin 3) → Formula {groupSig} (Fin 3)
_⁻¹ t = op (# 2) (t ∷ [])

e : Formula {groupSig} (Fin 3)
e = op (# 1) []

-- -----------------------------------------------------------------------------
-- Group Variety
-- -----------------------------------------------------------------------------

-- Variables for group laws
X : Set
X = Fin 3

x y z : X
x = # 0
y = # 1  
z = # 2

-- Convenient variable formulas for readability
g h k : Formula {groupSig} X
g = var x
h = var y
k = var z

-- Group Axioms (unconditional equations, so n = 0)

-- Associativity: (x · y) · z = x · (y · z)
assocLaw : Equation {groupSig} X
assocLaw = (g · h) · k , g · (h · k)

-- Left identity: e · x = x
leftIdLaw : Equation {groupSig} X  
leftIdLaw = e · g , g

-- Right identity: x · e = x
rightIdLaw : Equation {groupSig} X
rightIdLaw = g · e , g

-- Left inverse: x⁻¹ · x = e
leftInvLaw : Equation {groupSig} X
leftInvLaw = (g ⁻¹) · g , e

-- Right inverse: x · x⁻¹ = e
rightInvLaw : Equation {groupSig} X
rightInvLaw = g · (g ⁻¹) , e

-- Group Variety
GroupVariety : Variety {groupSig} X
GroupVariety = laws (
    assocLaw ∷ 
    leftIdLaw ∷ 
    rightIdLaw ∷ 
    leftInvLaw ∷ 
    rightInvLaw ∷ 
    []
  )

-- -----------------------------------------------------------------------------
-- Group Type
-- -----------------------------------------------------------------------------

-- A Group is an algebraic structure that satisfies the group variety
record Group (A : Set) : Set₁ where
  field
    algebra : AlgeStruct {groupSig} A
    isGroup : inVariety GroupVariety algebra

-- Convenient constructor for groups
mkGroup : (A : Set) → (alg : AlgeStruct {groupSig} A) 
  → inVariety GroupVariety alg → Group A
mkGroup A alg proof = record { algebra = alg ; isGroup = proof }

-- Extract the underlying algebraic structure
getAlgebra : {A : Set} → Group A → AlgeStruct {groupSig} A
getAlgebra grp = Group.algebra grp

-- Extract the group proof
getGroupProof : {A : Set} → (grp : Group A) → inVariety GroupVariety (Group.algebra grp)
getGroupProof grp = Group.isGroup grp
