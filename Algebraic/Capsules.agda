
open import Data.Empty using (⊥-elim)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Vec using (Vec; map)


open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Algebraic.Signatures
open import Countable.Sets

{-- A minimal countable constructive set theory. --}
module Algebraic.Capsules where

    