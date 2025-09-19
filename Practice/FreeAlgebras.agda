-- -----------------------------------------------------------------------------
-- Formulas and Equations
-- -----------------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc; #_)
open import Data.List as List using (List; lookup; length)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup; toList)
open import Data.Product using (proj₁; proj₂; _,_)

open import Signatures using (Signature; valence; nOps)
open import AlgebraicStructures using (AlgeStruct; Operator; getOp; getCarrier)
open import Equations using (Formula; Equation; var; op)

module FreeAlgebras where 
    -- A free algebra maker
    FreeAlge : {sig : Signature} 
                → (X : Set) 
                → AlgeStruct sig
    FreeAlge {sig} X = (Formula sig X , operations)
      where
        operations : (i : Fin (nOps sig)) → Operator (Formula sig X) (proj₂ sig i)
        operations i = λ args → op i args

    -- -- -----------------------------------------------------------------------------
    -- -- Satisfaction Varieties, & Conditional Satisfaction & Quasi-Varieites
    -- -- -----------------------------------------------------------------------------


