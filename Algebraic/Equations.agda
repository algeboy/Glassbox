-- -----------------------------------------------------------------------------
-- Formulas, Equations, and Free Algebras
-- -----------------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc; #_)
open import Data.List as List using (List; lookup; length)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup; toList)
open import Data.Product using (proj₁; proj₂)


-- Nats for examples --
open import Data.Nat using (ℕ; _*_)
open import Data.Nat.Base using (zero; suc)

open import Algebraic.Signatures 
open import Algebraic.Structures 
open import Countable.Sets

module Algebraic.Equations where  

  {-- An inductive type for formulas to become the carrier set of a free algebra. --}
  data Formula (sig : Signature) (X : Set) : Set where
    var  : (x : X) →  Formula sig X
    op   : (i : (Fin (nOps sig))) 
            → (Vec (Formula sig X) (valence sig i))
            → Formula sig X


  {-- Although this should be a pair-type to match the definition, 
      we use a record to get named fields for easier access. --}
  record Equation (sig : Signature) (X : Set) : Set where
    constructor _,_
    field
      lhs : Formula sig X
      rhs : Formula sig X


  -- Evaluates a formula by interpreting variables and applying the 
  -- operations from a target algebraic structure.
  {-# TERMINATING #-}
  evalFormula : {sig : Signature}
    → {X : Set}
    → (alg : Structure {sig})
    → (const : X → asSet (proj₁ alg))
    → (form : Formula sig X)
    → asSet (proj₁ alg)
  evalFormula {sig} alg const (var x) = const x
  evalFormula {sig} alg const (op i args) =
    getOp sig alg i (Vec.map (evalFormula {sig} alg const) args)

  {-# TERMINATING #-}
  evalFormula₁ : {sig : Signature}
    → {X : Set}
    → (alg : Structure₁ {sig})
    → (const : X → proj₁ alg)
    → (form : Formula sig X)
    → proj₁ alg
  evalFormula₁ {sig} alg const (var x) = const x
  evalFormula₁ {sig} alg const (op i args) =
    (proj₂ alg) i (Vec.map (evalFormula₁ {sig} alg const) args)


