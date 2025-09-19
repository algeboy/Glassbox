open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _<?_; _%_)
open import Data.Fin using (Fin; toℕ; #_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function using (case_of_)

open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Countable.Sets
open import Algebraic.Structures

module Algebraic.Monoids where

  MonoidSig : Signature
  MonoidSig = (2 , λ i → lookup operations i)
    where
      operations : Vec (String × ℕ) 2
      operations = ("1" , 0) ∷ ("·" , 2) ∷ []

  ℕ_+_z : Structure {MonoidSig}
  ℕ_+_z = (N , ops )
    where
      ops : (i : Fin 2) → (Operator N (proj₂ (proj₂ MonoidSig i)))
      ops Fin.zero = λ _ → zero        -- identity element (valence 0)
      ops (Fin.suc Fin.zero) = addNat  -- binary operation (valence 2)
        where
          addNat : Vec ℕ 2 → ℕ
          addNat (x ∷ y ∷ []) = x + y

  myMod : ℕ → ℕ → ℕ
  myMod x zero = x                -- if divisor is 0, return x unchanged
  myMod x (suc y) = x % (suc y)   -- if divisor is non-zero, use normal mod

  addFloop : ∀ {m n : ℕ} → Fin (m + n) → Fin (m + n) → Fin (m + n)
  addFloop {m} {0} x y = # (toℕ x + toℕ y)  -- no modulo for n=0
  addFloop {m} {suc k} x y with (toℕ x + toℕ y) <? m
  ... | yes _ = # (toℕ x + toℕ y)
  ... | no _  = # (m + ((toℕ x + toℕ y ∸ m) % suc k))

  Floop : (m n : ℕ) → Structure {MonoidSig}
  Floop m n = (F (m + n) , ops )  -- Use large bound to avoid constraint issues
    where
      ops : (i : Fin 2) → (Operator (F (m + n)) (proj₂ (proj₂ MonoidSig i)))
      ops Fin.zero = λ _ → # 0          -- identity element
      ops (Fin.suc Fin.zero) = λ x y → addFloop {m} {n} x y  -- binary operation
