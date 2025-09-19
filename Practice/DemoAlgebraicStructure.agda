-- General agda --
open import Agda.Primitive using (Level; lsuc; lzero)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Fin using (Fin; toℕ; #_; zero; suc; fromℕ<)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat as Nat using (ℕ; _+_; zero; suc; _<_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin.Properties as FinProps using (toℕ-injective)
open import Data.List as List using (List; []; _∷_; lookup; length; filter)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup; toList)

-- For decision procedures and pattern matching
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Strings for operator names --
open import Data.String using (String)

-- Nats for valence --
open import Data.Nat using (ℕ)

module DemoAlgebraicStructure where



-- -----------------------------------------------------------------------------
-- Signatures
-- -----------------------------------------------------------------------------

Signature : Set 
Signature = Σ[ n ∈ ℕ ] ((Fin n) → (String × ℕ))

-- Monoid signature

MonoidSig : Signature
MonoidSig = (2 , λ i → Vec.lookup operations i)
  where
    operations : Vec (String × ℕ) 2
    operations = ("1" , 0) ∷ ("·" , 2) ∷ []


-- -----------------------------------------------------------------------------
-- Algebraic Structures
-- -----------------------------------------------------------------------------

{-- This is Definition 3.3 : Alge_Ω --}

Operator : (X : Set) → (String × ℕ) → Set
Operator X op = Vec X (proj₂ op) → X

AlgeStruct : (sig : Signature) → Set₁
AlgeStruct sig = Σ[ X ∈ Set ] ((i : Fin (proj₁ sig)) → Operator X ((proj₂ sig) i))

-- below we amend this for the monoid, because we have to add laws


-- -----------------------------------------------------
-- Modulo integer monoid: ops and laws
-- -----------------------------------------------------



-- carrier set

ℕ/ : (n : ℕ) → Set
ℕ/ Nat.zero = ℕ -- ℕ/ 0 = ℕ 
ℕ/ n = Fin n

-- operations

add : {n : ℕ} → Vec (ℕ/ n) 2 → ℕ/ n
add {Nat.zero} (a ∷ b ∷ []) = a + b -- Natural numbers
add {Nat.suc n} (a ∷ b ∷ []) = (toℕ a + toℕ b) mod (Nat.suc n)


zeta : {n : ℕ} → Vec (ℕ/ n) 0 → ℕ/ n
zeta {Nat.zero} [] = Nat.zero -- Natural numbers
zeta {Nat.suc n} [] = Fin.zero  -- Zero of Fin (suc n)

-- the laws (ops zero is 0-ary, ops suc(zero) is add

LeftIdentity
  : {X : Set}
  → ((i : Fin 2) → Operator X (proj₂ MonoidSig i))
  → Set
LeftIdentity {X} ops =
  (x : X) → ops (suc zero) (ops zero [] ∷ x ∷ []) ≡ x

RightIdentity
  : {X : Set}
  → ((i : Fin 2) → Operator X (proj₂ MonoidSig i))
  → Set
RightIdentity {X} ops =
  (x : X) → ops (suc zero) (x ∷ ops zero [] ∷ []) ≡ x

Associativity
  : {X : Set}
  → ((i : Fin 2) → Operator X (proj₂ MonoidSig i))
  → Set
Associativity {X} ops =
  (x y z : X) → ops (suc zero) (ops (suc zero) (x ∷ y ∷ []) ∷ z ∷ []) 
                 ≡ ops (suc zero) (x ∷ ops (suc zero) (y ∷ z ∷ []) ∷ [])

record MonoidLaws {X : Set} (ops : (i : Fin 2) → Operator X (proj₂ MonoidSig i)) : Set where
  field
    left  : LeftIdentity ops
    right : RightIdentity ops
    assoc : Associativity ops



-- The algebra type that includes the identity laws.

AlgeStructMonoid : Set₁
AlgeStructMonoid =
  Σ[ X ∈ Set ]
    (Σ[ ops ∈ ((i : Fin 2) → Operator X (proj₂ MonoidSig i)) ]
       MonoidLaws ops)


postulate
  add-left-identity : (n : ℕ) → (x : ℕ/ n) →
                      add {n} (zeta {n} [] ∷ x ∷ []) ≡ x


postulate
  add-right-identity : (n : ℕ) → (x : ℕ/ n) →
                      add {n} (x ∷ zeta {n} [] ∷ []) ≡ x

postulate
  add-associative : (n : ℕ) → (x y z : ℕ/ n) →
                     add {n} (add {n} (x ∷ y ∷ []) ∷ z ∷ []) 
                   ≡ add {n} (x ∷ add {n} (y ∷ z ∷ []) ∷ [])





--- the Modulo Monoid: it uses add, zeta, and the above MonoidLaws

ModuloMonoid : (n : ℕ) → AlgeStructMonoid
ModuloMonoid n = (ℕ/ n , operations , laws)
  where
    operations : (i : Fin 2) → Operator (ℕ/ n) (proj₂ MonoidSig i)
    operations zero     = zeta {n}
    operations (suc zero) = add {n}

    laws : MonoidLaws operations
    laws = record
      { left  = add-left-identity n
      ; right = add-right-identity n
      ; assoc = add-associative n
      }



-- ----------------------------------------------------- EXAMPLE:
-- Construct the modulo-13 monoid
Zm13 : AlgeStructMonoid
Zm13 = ModuloMonoid 13
carZm13 : Set
carZm13 = proj₁ Zm13


-- Extract operations
ops13 : (i : Fin 2) → Operator (carZm13) (proj₂ MonoidSig i)
ops13 = proj₁ (proj₂ Zm13)

-- Binary operation (addition modulo 13)
add13 : Vec (carZm13) 2 → carZm13
add13 = ops13 (suc zero)

-- Identity element
id13 : Vec (carZm13) 0 → carZm13
id13 = ops13 zero

-- Laws record
laws13 : MonoidLaws ops13
laws13 = proj₂ (proj₂ Zm13)

-- Example elements
a b : carZm13
a = # 7
b = # 9

-- Test addition
sumTest13 : carZm13
sumTest13 = add13 (a ∷ b ∷ [])
isRight13 : Dec (sumTest13 ≡ # 3)
isRight13 = yes refl

-- Test left-identity
leftIdTest13 : add13 (id13 [] ∷ a ∷ []) ≡ a
leftIdTest13 = MonoidLaws.left laws13 a

-- Test right-identity
rightIdTest13 : add13 (a ∷ id13 [] ∷ []) ≡ a
rightIdTest13 = MonoidLaws.right laws13 a