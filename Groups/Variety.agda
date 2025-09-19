open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _<?_; _%_)
open import Data.Fin using (Fin; toℕ; #_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function using (case_of_)

open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Vec using (Vec; []; _∷_; lookup)
-- open import Data.Integer using (ℤ; zero; suc; _+_; _*_; _-_; _<_; _≤_; _≟_; sign; abs)
open import Countable.Sets
open import Algebraic.Signatures
open import Algebraic.Equations
open import Algebraic.Structures
open import Algebraic.Varieties

module Groups.Variety where

  GroupSig : Signature
  GroupSig = (3 , λ i → lookup operations i)
    where
      operations : Vec (String × ℕ) 3
      operations = ("·" , 2) ∷ ("1" , 0) ∷ ("⁻¹" , 1) ∷ []

  -- Define infix operators for readability
  infix 6 _·_
  infix 8 _⁻¹
  infix 9 e

  -- Define the infix operators using direct position indices
  _·_ : Formula {GroupSig} (Fin 3) → Formula {GroupSig} (Fin 3) → Formula {GroupSig} (Fin 3)
  _·_ t₁ t₂ = op (# 0) (t₁ ∷ t₂ ∷ [])

  _⁻¹ : Formula {GroupSig} (Fin 3) → Formula {GroupSig} (Fin 3)
  _⁻¹ t = op (# 2) (t ∷ [])

  e : Formula {GroupSig} (Fin 3)
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
  g h k : Formula {GroupSig} X
  g = var x
  h = var y
  k = var z

  -- Group Axioms (unconditional equations, so n = 0)

  -- Associativity: (x · y) · z = x · (y · z)
  assocLaw : Equation {GroupSig} X
  assocLaw = (g · h) · k , g · (h · k)

  -- Left identity: e · x = x
  leftIdLaw : Equation {GroupSig} X
  leftIdLaw = e · g , g

  -- Right identity: x · e = x
  rightIdLaw : Equation {GroupSig} X
  rightIdLaw = g · e , g

  -- Left inverse: x⁻¹ · x = e
  leftInvLaw : Equation {GroupSig} X
  leftInvLaw = (g ⁻¹) · g , e

  -- Right inverse: x · x⁻¹ = e
  rightInvLaw : Equation {GroupSig} X
  rightInvLaw = g · (g ⁻¹) , e

  -- Group Variety
  GroupVariety : Variety {GroupSig}
  GroupVariety = (5 , X , λ i → lookup laws i)
    where
      laws : Vec (String × Equation {GroupSig} X) 5
      laws = ("assoc" , assocLaw) ∷ 
            ("leftId" , leftIdLaw) ∷ 
            ("rightId" , rightIdLaw) ∷ 
            ("leftInv" ,  leftInvLaw) ∷ 
            ("rightInv" , rightInvLaw) ∷ 
            []