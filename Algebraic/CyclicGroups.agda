-- type of CyclicGroup (finite) with proof of group laws
-- main construction: CyclicGroup n gives Z/(suc n)Z see Line 300+, and examples 
-- e.g., the Cyclic group Z/4Z = Fin 4
-- -- Z4 : Σ (Structure {GroupSig}) (λ S → GroupLaws (proj₁ S) (proj₂ S))
-- -- Z4 = CyclicGroup 3  

-- file written with the help of Github Copilot and ChatGPT


-- importing necessary modules
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Fin using (Fin; toℕ; zero; suc; fromℕ<; #_)
open import Data.Fin.Properties using (toℕ<n; fromℕ<-toℕ; toℕ-injective; toℕ-fromℕ<)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Nat as Nat using (ℕ; _+_; zero; suc; _∸_; _%_; _<_; _≤_)
open import Data.Nat.DivMod using (m<n⇒m%n≡m; m%n<n; n%n≡0; %-distribˡ-+; m%n%n≡m%n)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ; m∸n+n≡m; <⇒≤; +-assoc; m+[n∸m]≡n; +-comm)
open import Data.String using (String)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)

open import Algebraic.Structures
open import Algebraic.Signatures
open import Countable.Sets using (ConSet; asSet; F)

module Algebraic.CyclicGroups where

-----------------------------------------------------
-- Group Signature using the type Signature from Algebraic.Signatures
-----------------------------------------------------

-- Group signature: nullary identity, binary addition, and unary inverse
GroupSig : Signature
GroupSig = (3 , operations)
  where
    operations : Fin 3 → (String × ℕ)
    operations zero = ("0" , 0)         -- identity element (nullary)
    operations (suc zero) = ("+" , 2)   -- binary addition
    operations (suc (suc zero)) = ("-" , 1) -- unary inverse
    operations (suc (suc (suc ())))     -- impossible case

-- Helper functions to access operations
identity-op : Fin (nOps GroupSig)
identity-op = zero

add-op : Fin (nOps GroupSig) 
add-op = suc zero

inv-op : Fin (nOps GroupSig)
inv-op = suc (suc zero)



-----------------------------------------------------
-- Group Laws
-----------------------------------------------------

-- GroupLaws: a type that captures the four group axioms
-- refers to Structure and Operator from Algebraic.Structures

record GroupLaws (X : ConSet) (ops : (i : Fin (nOps GroupSig)) → Operator X (proj₂ (proj₂ GroupSig i))) : Set where
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
    
    -- Left inverse: (-x) + x = 0
    left-inverse : (x : asSet X) → 
      ops add-op (ops inv-op (x ∷ []) ∷ x ∷ []) ≡ ops identity-op []
    
    -- Right inverse: x + (-x) = 0
    right-inverse : (x : asSet X) → 
      ops add-op (x ∷ ops inv-op (x ∷ []) ∷ []) ≡ ops identity-op []



-----------------------------------------------------
-- Cyclic Group (finite) Operations on Fin (suc n) 
-----------------------------------------------------

-- Addition operation for Fin (suc n) (modular arithmetic)
fin-add : (n : ℕ) → Vec (Fin (suc n)) 2 → Fin (suc n)
fin-add n (a ∷ b ∷ []) = fromℕ< (m%n<n (toℕ a + toℕ b) (suc n))

-- Example: fin-add 10 (3 ∷ 4 ∷ []) = fromℕ< (m%n<n (3 + 4) 11) = fromℕ< (m%n<n 7 11) = #7
-- Since 7 < 11, the result is Fin element representing 7 in Fin 11


-- Identity element for Fin (suc n)
fin-identity : (n : ℕ) → Vec (Fin (suc n)) 0 → Fin (suc n)  
fin-identity n [] = zero


-- Inverse operation for Fin (suc n) (additive inverse in modular arithmetic)
fin-inverse : (n : ℕ) → Vec (Fin (suc n)) 1 → Fin (suc n)
fin-inverse n (a ∷ []) = fromℕ< (m%n<n ((suc n) ∸ toℕ a) (suc n))


-----------------------------------------------------
-- Group Law Lemmas for Finite Cyclic Groups: types and proofs
-- stating these is just for illustrative purposes; 
-- it is not necessary to state these auxiliary lemmas
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

-- Left inverse lemma: (-x) + x = 0
fin-left-inverse : (n : ℕ) → (x : Fin (suc n)) → 
  fin-add n (fin-inverse n (x ∷ []) ∷ x ∷ []) ≡ fin-identity n []

-- Right inverse lemma: x + (-x) = 0
fin-right-inverse : (n : ℕ) → (x : Fin (suc n)) → 
  fin-add n (x ∷ fin-inverse n (x ∷ []) ∷ []) ≡ fin-identity n []


-----------------------------------------------------
-- now the proofs of the lemmas; there are some helper lemmas required  
-----------------------------------------------------

-- right inverse proof

-- Helper functions for modular arithmetic extraction
mod-extract-left : (a b : ℕ) → (n : ℕ) → (a % (suc n) + b) % (suc n) ≡ (a + b) % (suc n)
mod-extract-left a b n = 
  trans (%-distribˡ-+ (a % (suc n)) b (suc n))
        (trans (cong (λ x → (x + (b % (suc n))) % (suc n)) 
                     (m%n%n≡m%n a (suc n)))
               (sym (%-distribˡ-+ a b (suc n))))

mod-extract-right : (a b : ℕ) → (n : ℕ) → (a + b % (suc n)) % (suc n) ≡ (a + b) % (suc n)
mod-extract-right a b n = 
  trans (%-distribˡ-+ a (b % (suc n)) (suc n))
        (trans (cong (λ x → (a % (suc n) + x) % (suc n)) 
                     (m%n%n≡m%n b (suc n)))
               (sym (%-distribˡ-+ a b (suc n))))

fin-right-inverse-proof : (n : ℕ) → (x : Fin (suc n)) → 
  fin-add n (x ∷ fin-inverse n (x ∷ []) ∷ []) ≡ fin-identity n []
fin-right-inverse-proof n x = 
  toℕ-injective (trans (toℕ-fromℕ< _) 
    (trans (cong (λ y → (toℕ x + y) % (suc n)) (toℕ-fromℕ< _))
    (trans (mod-extract-right (toℕ x) ((suc n) ∸ toℕ x) n)
    (trans (cong (λ y → y % (suc n)) (m+[n∸m]≡n (<⇒≤ (toℕ<n x))))
           (n%n≡0 (suc n))))))


-- left inverse proof

fin-left-inverse-proof : (n : ℕ) → (x : Fin (suc n)) → 
  fin-add n (fin-inverse n (x ∷ []) ∷ x ∷ []) ≡ fin-identity n []
fin-left-inverse-proof n x = 
  let
    inv-x = fin-inverse n (x ∷ [])
    toℕ-inv-x = toℕ-fromℕ< (m%n<n ((suc n) ∸ toℕ x) (suc n))
    sum-eq = cong (_+ toℕ x) toℕ-inv-x
    extract-step = mod-extract-left ((suc n) ∸ toℕ x) (toℕ x) n
    final-step = trans (cong (λ y → y % (suc n)) (+-comm ((suc n) ∸ toℕ x) (toℕ x)))
                       (trans (cong (λ y → y % (suc n)) (m+[n∸m]≡n (<⇒≤ (toℕ<n x))))
                              (n%n≡0 (suc n)))
    main-eq = trans (cong (λ y → y % (suc n)) sum-eq) (trans extract-step final-step)
  in
    toℕ-injective (trans (toℕ-fromℕ< _) main-eq)


-- associativity proof; we need a helper lemma for modular arithmetic associativity

mod-assoc-lemma : (n : ℕ) → (x y z : Fin (suc n)) → 
                  ((toℕ x + toℕ y) % (suc n) + toℕ z) % (suc n) ≡ 
                  (toℕ x + (toℕ y + toℕ z) % (suc n)) % (suc n)
mod-assoc-lemma n x y z = 
  trans (mod-extract-left (toℕ x + toℕ y) (toℕ z) n)
        (trans (cong (λ w → w % (suc n)) (+-assoc (toℕ x) (toℕ y) (toℕ z)))
               (sym (mod-extract-right (toℕ x) (toℕ y + toℕ z) n)))


-- Proof for associativity: (x + y) + z = x + (y + z) using toℕ-injective approach

fin-associativity-proof : (n : ℕ) → (x y z : Fin (suc n)) → 
  fin-add n (fin-add n (x ∷ y ∷ []) ∷ z ∷ []) ≡ 
  fin-add n (x ∷ fin-add n (y ∷ z ∷ []) ∷ [])
fin-associativity-proof n x y z = 
  toℕ-injective (
    let 
      -- Left side: toℕ (fin-add n (fin-add n (x ∷ y ∷ []) ∷ z ∷ []))
      -- This equals: (toℕ (fin-add n (x ∷ y ∷ [])) + toℕ z) % (suc n)
      lhs : toℕ (fin-add n (fin-add n (x ∷ y ∷ []) ∷ z ∷ [])) ≡ (toℕ (fin-add n (x ∷ y ∷ [])) + toℕ z) % (suc n)
      lhs = toℕ-fromℕ< (m%n<n (toℕ (fin-add n (x ∷ y ∷ [])) + toℕ z) (suc n))
      
      -- We know: toℕ (fin-add n (x ∷ y ∷ [])) ≡ (toℕ x + toℕ y) % (suc n)
      xy-eq : toℕ (fin-add n (x ∷ y ∷ [])) ≡ (toℕ x + toℕ y) % (suc n)
      xy-eq = toℕ-fromℕ< (m%n<n (toℕ x + toℕ y) (suc n))
      
      -- Right side: toℕ (fin-add n (x ∷ fin-add n (y ∷ z ∷ []) ∷ []))
      -- This equals: (toℕ x + toℕ (fin-add n (y ∷ z ∷ []))) % (suc n)
      rhs : toℕ (fin-add n (x ∷ fin-add n (y ∷ z ∷ []) ∷ [])) ≡ (toℕ x + toℕ (fin-add n (y ∷ z ∷ []))) % (suc n)
      rhs = toℕ-fromℕ< (m%n<n (toℕ x + toℕ (fin-add n (y ∷ z ∷ []))) (suc n))
      
      -- We know: toℕ (fin-add n (y ∷ z ∷ [])) ≡ (toℕ y + toℕ z) % (suc n)
      yz-eq : toℕ (fin-add n (y ∷ z ∷ [])) ≡ (toℕ y + toℕ z) % (suc n)
      yz-eq = toℕ-fromℕ< (m%n<n (toℕ y + toℕ z) (suc n))
      
      -- The core insight: both sides should equal (toℕ x + toℕ y + toℕ z) % (suc n)
      -- This requires a complex proof about nested modular arithmetic operations
      -- The key lemma needed is: ((a % n) + b) % n ≡ (a + b) % n
      -- and ((a + b) % n + c) % n ≡ (a + (b + c)) % n due to associativity
      
      -- Use our modular arithmetic lemma for the key step
      assoc-key : ((toℕ x + toℕ y) % (suc n) + toℕ z) % (suc n) ≡ 
                  (toℕ x + (toℕ y + toℕ z) % (suc n)) % (suc n)
      assoc-key = mod-assoc-lemma n x y z
      
    in 
      trans lhs (trans (cong (λ w → (w + toℕ z) % (suc n)) xy-eq) 
                       (trans assoc-key 
                              (trans (cong (λ w → (toℕ x + w) % (suc n)) (sym yz-eq)) 
                                     (sym rhs))))
  )


-- proof of left identity

-- Helper lemma: for any a : Fin (suc n), we have (toℕ a) % (suc n) ≡ toℕ a
needThis : (n : ℕ) → (a : Fin (suc n)) → ((toℕ a) % (suc n)) ≡ (toℕ a)
needThis n a = m<n⇒m%n≡m (toℕ<n a)

-- Proof for left identity: 0 + x = x using toℕ-injective approach
fin-left-identity-proof : (n : ℕ) → (x : Fin (suc n)) → 
  fin-add n (fin-identity n [] ∷ x ∷ []) ≡ x
fin-left-identity-proof n x = 
  toℕ-injective (
    let 
      -- The left side is: toℕ (fromℕ< (m%n<n (0 + toℕ x) (suc n)))
      -- We can use toℕ-fromℕ< which gives: toℕ (fromℕ< prf) ≡ m % n
      lhs : toℕ (fromℕ< (m%n<n (0 + toℕ x) (suc n))) ≡ (0 + toℕ x) % (suc n)
      lhs = toℕ-fromℕ< (m%n<n (0 + toℕ x) (suc n))
      
      -- And we know that (0 + toℕ x) % (suc n) ≡ toℕ x
      mod-result : (0 + toℕ x) % (suc n) ≡ toℕ x  
      mod-result = trans (cong (λ y → y % (suc n)) (+-identityˡ (toℕ x))) (needThis n x)
      
    in 
      -- Combining: toℕ (fromℕ< ...) ≡ (0 + toℕ x) % (suc n) ≡ toℕ x
      trans lhs mod-result
  )

-- proof of right identity

-- Proof for right identity: x + 0 = x using toℕ-injective approach  
fin-right-identity-proof : (n : ℕ) → (x : Fin (suc n)) → 
  fin-add n (x ∷ fin-identity n [] ∷ []) ≡ x
fin-right-identity-proof n x = 
  toℕ-injective (
    let 
      -- The left side is: toℕ (fromℕ< (m%n<n (toℕ x + 0) (suc n)))
      -- We can use toℕ-fromℕ< which gives: toℕ (fromℕ< prf) ≡ m % n
      lhs : toℕ (fromℕ< (m%n<n (toℕ x + 0) (suc n))) ≡ (toℕ x + 0) % (suc n)
      lhs = toℕ-fromℕ< (m%n<n (toℕ x + 0) (suc n))
      
      -- And we know that (toℕ x + 0) % (suc n) ≡ toℕ x
      mod-result : (toℕ x + 0) % (suc n) ≡ toℕ x  
      mod-result = trans (cong (λ y → y % (suc n)) (+-identityʳ (toℕ x))) (needThis n x)
      
    in 
      -- Combining: toℕ (fromℕ< ...) ≡ (toℕ x + 0) % (suc n) ≡ toℕ x
      trans lhs mod-result
  )


-- now all proofs are done; use these to define lemmas
-- this step is not strictly necessary, but it helps to clarify the structure

fin-left-identity = fin-left-identity-proof
fin-right-identity = fin-right-identity-proof  
fin-associativity = fin-associativity-proof
fin-left-inverse = fin-left-inverse-proof
fin-right-inverse = fin-right-inverse-proof





-----------------------------------------------------
-- Main Construction: Cyclic Group Structure for finite cyclic groups
-----------------------------------------------------

-- Create cyclic group structure for Fin (suc n) with laws
CyclicGroup : (n : ℕ) → Σ (Structure {GroupSig}) (λ S → GroupLaws (proj₁ S) (proj₂ S))
CyclicGroup n = (structure , laws)
  where
    structure : Structure {GroupSig}
    structure = (F (suc n) , operations)
      where
        operations : (i : Fin (nOps GroupSig)) → Operator (F (suc n)) (proj₂ (proj₂ GroupSig i))
        operations zero = fin-identity n        -- identity operation  
        operations (suc zero) = fin-add n       -- addition operation
        operations (suc (suc zero)) = fin-inverse n -- inverse operation
        operations (suc (suc (suc ())))
    
    laws : GroupLaws (proj₁ structure) (proj₂ structure)
    laws = record
      { left-identity = fin-left-identity n     -- Using our lemma
      ; right-identity = fin-right-identity n   -- Using our lemma  
      ; associativity = fin-associativity n     -- Using our lemma
      ; left-inverse = fin-left-inverse n       -- Using our lemma
      ; right-inverse = fin-right-inverse n     -- Using our lemma
      }







-----------------------------------------------------
-- Examples
-----------------------------------------------------

-- Cyclic group Z/4Z = Fin 4
Z4-with-laws : Σ (Structure {GroupSig}) (λ S → GroupLaws (proj₁ S) (proj₂ S))
Z4-with-laws = CyclicGroup 3  -- This gives us Fin 4

-- Extract just the structure for convenience
Z4 : Structure {GroupSig}
Z4 = proj₁ Z4-with-laws

-- Extract the laws
Z4-laws : GroupLaws (proj₁ Z4) (proj₂ Z4)
Z4-laws = proj₂ Z4-with-laws

-- Extract carrier and operations
Z4-carrier : Set
Z4-carrier = asSet (proj₁ Z4)

Z4-ops : (i : Fin (nOps GroupSig)) → Operator (proj₁ Z4) (proj₂ (proj₂ GroupSig i))
Z4-ops = proj₂ Z4

-- Identity element
e4 : Z4-carrier
e4 = Z4-ops identity-op []

-- Addition operation
_+₄_ : Z4-carrier → Z4-carrier → Z4-carrier
a +₄ b = Z4-ops add-op (a ∷ b ∷ [])

-- Inverse operation
-₄_ : Z4-carrier → Z4-carrier
-₄ a = Z4-ops inv-op (a ∷ [])

-- Example: 1 + 3 = 0 in Z/4Z
example-add-z4 : Z4-carrier
example-add-z4 = (# 1) +₄ (# 3)

-- Verify it equals 0
example-proof-z4 : example-add-z4 ≡ (# 0)
example-proof-z4 = refl

-- Example: inverse of 3 is 1 in Z/4Z (since 3 + 1 = 0)
example-inv-z4 : Z4-carrier
example-inv-z4 = -₄ (# 3)

-- Verify it equals 1
example-inv-proof-z4 : example-inv-z4 ≡ (# 1)
example-inv-proof-z4 = refl

-- Example: left inverse property 3 + (-3) = 0
example-left-inv-z4 : Z4-carrier
example-left-inv-z4 = (-₄ (# 3)) +₄ (# 3)

-- Verify it equals 0
example-left-inv-proof-z4 : example-left-inv-z4 ≡ e4
example-left-inv-proof-z4 = refl

-- Example: right inverse property 2 + (-2) = 0
example-right-inv-z4 : Z4-carrier
example-right-inv-z4 = (# 2) +₄ (-₄ (# 2))

-- Verify it equals 0
example-right-inv-proof-z4 : example-right-inv-z4 ≡ e4
example-right-inv-proof-z4 = refl

-----------------------------------------------------
-- Cyclic group Z/6Z for comparison
-----------------------------------------------------

Z6-with-laws : Σ (Structure {GroupSig}) (λ S → GroupLaws (proj₁ S) (proj₂ S))
Z6-with-laws = CyclicGroup 5  -- This gives us Fin 6

Z6 : Structure {GroupSig}
Z6 = proj₁ Z6-with-laws

Z6-carrier : Set
Z6-carrier = asSet (proj₁ Z6)

-- Addition and inverse operations for Z/6Z
_+₆_ : Z6-carrier → Z6-carrier → Z6-carrier
a +₆ b = (proj₂ Z6) add-op (a ∷ b ∷ [])

-₆_ : Z6-carrier → Z6-carrier
-₆ a = (proj₂ Z6) inv-op (a ∷ [])

-- Example: inverse of 4 is 2 in Z/6Z (since 4 + 2 = 0)
example-inv-z6 : Z6-carrier
example-inv-z6 = -₆ (# 4)

-- Verify it equals 2
example-inv-proof-z6 : example-inv-z6 ≡ (# 2)
example-inv-proof-z6 = refl
