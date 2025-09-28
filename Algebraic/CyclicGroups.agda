-- type of CyclicGroup (finite) with proof of group laws
-- main construction: CyclicGroup n gives Z/(suc n)Z see Line 300+, and examples 
-- e.g., the Cyclic group Z/4Z = Fin 4
-- -- Z4 : Σ (Structure {GroupSig}) (λ S → GroupLaws (proj₁ S) (proj₂ S))
-- -- Z4 = CyclicGroup 3  

-- in addition to group axioms, we have lemmas of the following:
-- CyclicGroup n is commutative: Line 338 cyclic-group-abelian
-- In CyclicGroup n, inverses are unique: Line 366 cyclic-inverse-unique
-- In CyclicGroup n, inverse of sum is sum of inverses: Line 436 cyclic-inverse-distributive

-- at the end we define a homomorphism: multiplication by 2 on CyclicGroup n, see Line 601+
-- this definition used the type Hom from Algebraic.Homomorphism


-- file written with the help of Github Copilot and ChatGPT


-- importing necessary modules
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Fin using (Fin; toℕ; zero; suc; fromℕ<; #_)
open import Data.Fin.Properties using (toℕ<n; fromℕ<-toℕ; toℕ-injective; toℕ-fromℕ<)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Nat as Nat using (ℕ; _+_; zero; suc; _∸_; _%_; _<_; _≤_; _*_)
open import Data.Nat.DivMod using (m<n⇒m%n≡m; m%n<n; n%n≡0; %-distribˡ-+; m%n%n≡m%n)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ; m∸n+n≡m; <⇒≤; +-assoc; m+[n∸m]≡n; +-comm)
open import Data.String using (String)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Vec using ([]; _∷_)

open import Algebraic.Structures
open import Algebraic.Signatures
open import Countable.Sets using (ConSet; asSet; F; F←F)
open import Algebraic.Homomorphism

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
-- Additional Properties: Commutativity (Abelian Property)
-----------------------------------------------------

-----------------------------------------------------
-- Lemma: CyclicGroup n is abelian (commutative)
-----------------------------------------------------
cyclic-group-abelian : (n : ℕ) → 
                       (a b : asSet (proj₁ (proj₁ (CyclicGroup n)))) →
                       (proj₂ (proj₁ (CyclicGroup n))) add-op (a ∷ b ∷ []) ≡ 
                       (proj₂ (proj₁ (CyclicGroup n))) add-op (b ∷ a ∷ [])
cyclic-group-abelian n a b = 
  -- The addition operation grp-add is fin-add n
  -- We need to prove: grp-add (a ∷ b ∷ []) ≡ grp-add (b ∷ a ∷ [])
  -- This follows from commutativity of ℕ addition in the underlying modular arithmetic
  let
    grp-add = (proj₂ (proj₁ (CyclicGroup n))) add-op
  in
    toℕ-injective (
      trans (toℕ-fromℕ< _)                                        -- LHS: toℕ(grp-add (a ∷ b ∷ []))
      (trans (cong (λ x → x % (suc n)) (+-comm (toℕ a) (toℕ b)))  -- Use ℕ commutativity
             (sym (toℕ-fromℕ< _))))                               -- RHS: toℕ(grp-add (b ∷ a ∷ []))



-----------------------------------------------------
-- Lemma: In CyclicGroup n, inverses are unique
-- If both y and z are right inverses of g, then y ≡ z
-----------------------------------------------------
cyclic-inverse-unique : (n : ℕ) → 
                        (g y z : asSet (proj₁ (proj₁ (CyclicGroup n)))) →
                        (proj₂ (proj₁ (CyclicGroup n))) add-op (g ∷ y ∷ []) ≡ (proj₂ (proj₁ (CyclicGroup n))) identity-op [] →
                        (proj₂ (proj₁ (CyclicGroup n))) add-op (g ∷ z ∷ []) ≡ (proj₂ (proj₁ (CyclicGroup n))) identity-op [] →
                        y ≡ z
cyclic-inverse-unique n g y z gy=0 gz=0 = 
  -- Step-by-step proof that inverses are unique in CyclicGroup n
  -- If g + y = 0 and g + z = 0, then y = z
  let
    -- Abbreviations for cleaner notation
    G = CyclicGroup n
    carrier = asSet (proj₁ (proj₁ G))
    ops = proj₂ (proj₁ G)
    _+_ : carrier → carrier → carrier
    x + y = ops add-op (x ∷ y ∷ [])
    0g : carrier  
    0g = ops identity-op []
    -_ : carrier → carrier
    - x = ops inv-op (x ∷ [])
    -g = - g
    
    -- Step 1: From hypotheses g + y = 0 and g + z = 0, we get g + y = g + z
    step1 : g + y ≡ g + z
    step1 = trans gy=0 (sym gz=0)
    
    -- Step 2: Add (-g) from the left to both sides: (-g) + (g + y) = (-g) + (g + z)
    step2 : (-g) + (g + y) ≡ (-g) + (g + z)
    step2 = cong (λ w → (-g) + w) step1
    
    -- Step 3: Use associativity law to rearrange: (-g) + (g + y) = ((-g) + g) + y
    --          and (-g) + (g + z) = ((-g) + g) + z, giving us ((-g) + g) + y = ((-g) + g) + z
    step3 : ((-g) + g) + y ≡ ((-g) + g) + z
    step3 = let
              grp-laws = proj₂ G
              assoc-left : (-g) + (g + y) ≡ ((-g) + g) + y
              assoc-left = sym (GroupLaws.associativity grp-laws (-g) g y)
              
              assoc-right : (-g) + (g + z) ≡ ((-g) + g) + z  
              assoc-right = sym (GroupLaws.associativity grp-laws (-g) g z)
            in
              trans (sym assoc-left) (trans step2 assoc-right)
    
    -- Step 4: Use left inverse law: (-g) + g = 0, so ((-g) + g) + y = ((-g) + g) + z becomes 0 + y = 0 + z
    step4 : 0g + y ≡ 0g + z
    step4 = let
              grp-laws = proj₂ G
              left-inv : (-g) + g ≡ 0g
              left-inv = GroupLaws.left-inverse grp-laws g
              
              subst-left : ((-g) + g) + y ≡ 0g + y
              subst-left = cong (λ w → w + y) left-inv
              
              subst-right : ((-g) + g) + z ≡ 0g + z
              subst-right = cong (λ w → w + z) left-inv
            in
              trans (sym subst-left) (trans step3 subst-right)
    
    -- Step 5: Use left identity law: 0 + y = y and 0 + z = z, so from 0 + y = 0 + z we get y = z
    step5 : y ≡ z
    step5 = let
              grp-laws = proj₂ G
              left-id-y : 0g + y ≡ y
              left-id-y = GroupLaws.left-identity grp-laws y
              
              left-id-z : 0g + z ≡ z
              left-id-z = GroupLaws.left-identity grp-laws z
            in
              trans (sym left-id-y) (trans step4 left-id-z)
    
  in
    step5  -- The complete proof: y ≡ z

-----------------------------------------------------
-- Lemma: In CyclicGroup n, -(a+b) = (-a)+(-b)
-- Distributivity of inverse over addition
-----------------------------------------------------
cyclic-inverse-distributive : (n : ℕ) → 
                             (a b : asSet (proj₁ (proj₁ (CyclicGroup n)))) →
                             (proj₂ (proj₁ (CyclicGroup n))) inv-op ((proj₂ (proj₁ (CyclicGroup n))) add-op (a ∷ b ∷ []) ∷ []) ≡ 
                             (proj₂ (proj₁ (CyclicGroup n))) add-op ((proj₂ (proj₁ (CyclicGroup n))) inv-op (a ∷ []) ∷ (proj₂ (proj₁ (CyclicGroup n))) inv-op (b ∷ []) ∷ [])
cyclic-inverse-distributive n a b = 
  let
    -- Abbreviations for cleaner notation
    G = CyclicGroup n
    carrier = asSet (proj₁ (proj₁ G))
    ops = proj₂ (proj₁ G)
    _+_ : carrier → carrier → carrier
    x + y = ops add-op (x ∷ y ∷ [])
    -_ : carrier → carrier  
    - x = ops inv-op (x ∷ [])
    0g : carrier
    0g = ops identity-op []
      
    -- Step 1: (a+b) + ((-a)+(-b)) = (a+b) + ((-b)+(-a)) by commutativity of (-a)+(-b)
    step1 : (a + b) + ((- a) + (- b)) ≡ (a + b) + ((- b) + (- a))
    step1 = cong (λ w → (a + b) + w) (cyclic-group-abelian n (- a) (- b))
    
    -- Step 2: (a+b) + ((-b)+(-a)) = a + (b + ((-b)+(-a))) by associativity
    step2 : (a + b) + ((- b) + (- a)) ≡ a + (b + ((- b) + (- a)))
    step2 = GroupLaws.associativity (proj₂ G) a b ((- b) + (- a))
    
    -- Step 3: a + (b + ((-b)+(-a))) = a + ((b+(-b))+(-a)) by associativity
    -- We use the fact that (x + y) + z = x + (y + z), so b + ((-b) + (-a)) = (b + (-b)) + (-a)
    step3 : a + (b + ((- b) + (- a))) ≡ a + ((b + (- b)) + (- a))
    step3 = cong (λ w → a + w) (sym (GroupLaws.associativity (proj₂ G) b (- b) (- a)))
    
    -- Step 4: a + ((b+(-b))+(-a)) = a + (0+(-a)) by inverse law (b + (-b) = 0)
    step4 : a + ((b + (- b)) + (- a)) ≡ a + (0g + (- a))
    step4 = cong (λ w → a + (w + (- a))) (GroupLaws.right-inverse (proj₂ G) b)
    
    -- Step 5: a + (0+(-a)) = a + (-a) by identity law (0 + x = x)
    step5 : a + (0g + (- a)) ≡ a + (- a)
    step5 = cong (λ w → a + w) (GroupLaws.left-identity (proj₂ G) (- a))
    
    -- Step 6: a + (-a) = 0 by inverse law
    step6 : a + (- a) ≡ 0g
    step6 = GroupLaws.right-inverse (proj₂ G) a
    
    -- Chain all steps together to show (a+b) + ((-a)+(-b)) = 0
    proof-sum-equals-zero : (a + b) + ((- a) + (- b)) ≡ 0g
    proof-sum-equals-zero = trans step1 (trans step2 (trans step3 (trans step4 (trans step5 step6))))
    
    -- We also need to show that (a+b) + (-(a+b)) = 0 (by definition of inverse)
    inverse-property : (a + b) + (- (a + b)) ≡ 0g
    inverse-property = GroupLaws.right-inverse (proj₂ G) (a + b)
    
  in
    -- Apply uniqueness of inverses: since both -(a+b) and ((-a)+(-b)) are right inverses of (a+b),
    -- they must be equal
    cyclic-inverse-unique n (a + b) (- (a + b)) ((- a) + (- b)) inverse-property proof-sum-equals-zero



 
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

-----------------------------------------------------
-- Group Homomorphism: Multiplication by 2 on CyclicGroup n
-----------------------------------------------------


-- The multiplication by 2 function: x ↦ x + x
mult-by-2 : (n : ℕ) → Fin (suc n) → Fin (suc n)
mult-by-2 n x = let
    G = CyclicGroup n
    ops = proj₂ (proj₁ G)
    _+_ : Fin (suc n) → Fin (suc n) → Fin (suc n)
    a + b = ops add-op (a ∷ b ∷ [])
  in x + x

-- Homomorphism from CyclicGroup n to itself via multiplication by 2
hom-mult-by-2 : (n : ℕ) → Hom {GroupSig}
hom-mult-by-2 n = 
  let G = CyclicGroup n
      source = proj₁ G
      target = proj₁ G
  in FF (F←F (mult-by-2 n)) (mult-by-2 n) refl source target refl refl
     (λ { zero → λ { [] → 
            -- mult-by-2(0) = 0 + 0 = 0, so mult-by-2 preserves identity
            refl }
        ; (suc zero) → λ { (x ∷ y ∷ []) → 
            -- mult-by-2(x + y) = (x + y) + (x + y) = (x + x) + (y + y) = mult-by-2(x) + mult-by-2(y)
            let G = CyclicGroup n
                ops = proj₂ (proj₁ G)
                _+_ : Fin (suc n) → Fin (suc n) → Fin (suc n)
                a + b = ops add-op (a ∷ b ∷ [])
                grp-laws = proj₂ G
                
                -- Step 1: (x+y)+(x+y) = x+(y+(y+x)) by associativity and commutativity
                step1 : (x + y) + (x + y) ≡ x + (y + (y + x))
                step1 = trans (GroupLaws.associativity grp-laws x y (x + y))
                             (cong (λ w → x + (y + w)) (cyclic-group-abelian n x y))
                
                -- Step 2: x+(y+(y+x)) = x+((y+y)+x) by associativity
                step2 : x + (y + (y + x)) ≡ x + ((y + y) + x)
                step2 = cong (λ w → x + w) (sym (GroupLaws.associativity grp-laws y y x))
                
                -- Step 3: x+((y+y)+x) = x+(x+(y+y)) by commutativity
                step3 : x + ((y + y) + x) ≡ x + (x + (y + y))
                step3 = cong (λ w → x + w) (cyclic-group-abelian n (y + y) x)
                
                -- Step 4: x+(x+(y+y)) = (x+x)+(y+y) by associativity
                step4 : x + (x + (y + y)) ≡ (x + x) + (y + y)
                step4 = sym (GroupLaws.associativity grp-laws x x (y + y))
                
            in trans step1 (trans step2 (trans step3 step4))
            }
        ; (suc (suc zero)) → λ { (x ∷ []) → 
            -- mult-by-2(inv(x)) = inv(x) + inv(x) = inv(x + x) = inv(mult-by-2(x))
            -- This follows from our cyclic-inverse-distributive lemma
            sym (cyclic-inverse-distributive n x x) } })
