-- Cyclic Monoid using ConSet framework
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Fin using (Fin; toℕ; zero; suc; fromℕ<; #_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Nat as Nat using (ℕ; _+_; zero; suc)
open import Data.Nat.DivMod using (_mod_)
open import Data.String using (String)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Algebraic.Structures
open import Algebraic.Signatures
open import Countable.Sets

module Algebraic.cyclic_monoid where


-----------------------------------------------------
-- Monoid Signature
-----------------------------------------------------

-- Monoid signature: nullary identity and binary addition
MonoidSig : Signature
MonoidSig = (2 , operations)
  where
    operations : Fin 2 → (String × ℕ)
    operations zero = ("0" , 0)       -- identity element (nullary)
    operations (suc zero) = ("+" , 2) -- binary addition
    operations (suc (suc ()))         -- impossible case

-- Helper functions to access operations
identity-op : Fin (nOps MonoidSig)
identity-op = zero

add-op : Fin (nOps MonoidSig) 
add-op = suc zero

-----------------------------------------------------
-- Monoid Laws
-----------------------------------------------------

-- MonoidLaws: a type that captures the three monoid axioms
record MonoidLaws (X : ConSet) (ops : (i : Fin (nOps MonoidSig)) → Operator X (proj₂ (proj₂ MonoidSig i))) : Set where
  field
    -- Left identity: 0 + x = x
    left-identity : (x : asSet X) → 
      ops add-op (ops identity-op [] ∷ x ∷ []) ≡ x
    
    -- Right identity: x + 0 = x  
    right-identity : (x : asSet X) → 
      ops add-op (x ∷ ops identity-op [] ∷ []) ≡ x
    
    -- Associativity: (x + y) + z = x + (y + z)
    associativity : (x y z : asSet X) → 
      ops add-op (ops add-op (x ∷ y ∷ []) ∷ z ∷ []) ≡ 
      ops add-op (x ∷ ops add-op (y ∷ z ∷ []) ∷ [])



-----------------------------------------------------
-- Cyclic Monoid Operations on Fin (suc n)
-----------------------------------------------------

-- Addition operation for Fin (suc n) (modular arithmetic)
fin-add : (n : ℕ) → Vec (Fin (suc n)) 2 → Fin (suc n)
fin-add n (a ∷ b ∷ []) = (toℕ a + toℕ b) mod (suc n)

-- Identity element for Fin (suc n)
fin-identity : (n : ℕ) → Vec (Fin (suc n)) 0 → Fin (suc n)  
fin-identity n [] = zero

-----------------------------------------------------
-- Monoid Law Lemmas for Finite Cyclic Groups
-----------------------------------------------------

-- Left identity lemma: 0 + x = x
fin-left-identity : (n : ℕ) → (x : Fin (suc n)) → 
  fin-add n (fin-identity n [] ∷ x ∷ []) ≡ x

-- Right identity lemma: x + 0 = x  
fin-right-identity : (n : ℕ) → (x : Fin (suc n)) → 
  fin-add n (x ∷ fin-identity n [] ∷ []) ≡ x

-- Associativity lemma: (x + y) + z = x + (y + z)
fin-associativity : (n : ℕ) → (x y z : Fin (suc n)) → 
  fin-add n (fin-add n (x ∷ y ∷ []) ∷ z ∷ []) ≡ 
  fin-add n (x ∷ fin-add n (y ∷ z ∷ []) ∷ [])

-- Postulates for now (to be proven later)
-- These will eventually contain actual proofs using properties of modular arithmetic
postulate
  fin-left-identity-proof : (n : ℕ) → (x : Fin (suc n)) → 
    fin-add n (fin-identity n [] ∷ x ∷ []) ≡ x
  
  fin-right-identity-proof : (n : ℕ) → (x : Fin (suc n)) → 
    fin-add n (x ∷ fin-identity n [] ∷ []) ≡ x
  
  fin-associativity-proof : (n : ℕ) → (x y z : Fin (suc n)) → 
    fin-add n (fin-add n (x ∷ y ∷ []) ∷ z ∷ []) ≡ 
    fin-add n (x ∷ fin-add n (y ∷ z ∷ []) ∷ [])

-- Define the lemmas using the postulates
fin-left-identity = fin-left-identity-proof
fin-right-identity = fin-right-identity-proof  
fin-associativity = fin-associativity-proof

 



-----------------------------------------------------
-- Cyclic Monoid Structure
-----------------------------------------------------

-- Create cyclic monoid structure for Fin (suc n) with laws
CyclicMonoid : (n : ℕ) → Σ (Structure {MonoidSig}) (λ S → MonoidLaws (proj₁ S) (proj₂ S))
CyclicMonoid n = (structure , laws)
  where
    structure : Structure {MonoidSig}
    structure = (F (suc n) , operations)
      where
        operations : (i : Fin (nOps MonoidSig)) → Operator (F (suc n)) (proj₂ (proj₂ MonoidSig i))
        operations zero = fin-identity n        -- identity operation  
        operations (suc zero) = fin-add n       -- addition operation
        operations (suc (suc ()))
    
    laws : MonoidLaws (proj₁ structure) (proj₂ structure)
    laws = record
      { left-identity = fin-left-identity n     -- Using our lemma
      ; right-identity = fin-right-identity n   -- Using our lemma  
      ; associativity = fin-associativity n     -- Using our lemma
      }






-----------------------------------------------------
-- Examples
-----------------------------------------------------

-- Cyclic monoid Z/3Z = Fin 3
Z3-with-laws : Σ (Structure {MonoidSig}) (λ S → MonoidLaws (proj₁ S) (proj₂ S))
Z3-with-laws = CyclicMonoid 2  -- This gives us Fin 3

-- Extract just the structure for convenience
Z3 : Structure {MonoidSig}
Z3 = proj₁ Z3-with-laws

-- Extract the laws
Z3-laws : MonoidLaws (proj₁ Z3) (proj₂ Z3)
Z3-laws = proj₂ Z3-with-laws

-- Extract carrier and operations
Z3-carrier : Set
Z3-carrier = asSet (proj₁ Z3)

Z3-ops : (i : Fin (nOps MonoidSig)) → Operator (proj₁ Z3) (proj₂ (proj₂ MonoidSig i))
Z3-ops = proj₂ Z3

-- Identity element
e3 : Z3-carrier
e3 = Z3-ops identity-op []

-- Addition operation
_+₃_ : Z3-carrier → Z3-carrier → Z3-carrier
a +₃ b = Z3-ops add-op (a ∷ b ∷ [])

--------
-- Example: 1 + 2 = 0 in Z/3Z
example-add : Z3-carrier
example-add = (# 1) +₃ (# 2)

-- Verify it equals 0
example-proof : example-add ≡ (# 0)
example-proof = refl

---------
-- Example: identity properties 2+0=2
example-add0 : Z3-carrier
example-add0 = (# 2) +₃ e3

-- Verify it equals 2
example-proof0 : example-add0 ≡ (# 2)
example-proof0  = refl