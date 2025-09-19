-- Test file to understand +-assoc
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_)

module TestAssoc where

test : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
test x y z = +-assoc x y z
