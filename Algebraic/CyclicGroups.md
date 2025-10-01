# Cyclic Groups

[ToC]

## Group Signature
We define a **group signature** with three operations: a nullary identity element, binary addition, and unary inverse. This captures the essential structure needed for group operations. The term `GroupSig` is of type `Signature` which is defined in Signatures.agda.

```agda
GroupSig : Signature
GroupSig = (3 , operations)
  where
    operations : Fin 3 → (String × ℕ)
    operations zero = ("0" , 0)             -- identity element (nullary)
    operations (suc zero) = ("+" , 2)       -- binary addition
    operations (suc (suc zero)) = ("-" , 1) -- unary inverse
```

Helper functions provide convenient access to the operations:
```agda
identity-op : Fin (nOps GroupSig)
identity-op = zero

add-op : Fin (nOps GroupSig) 
add-op = suc zero

inv-op : Fin (nOps GroupSig)
inv-op = suc (suc zero)
```

## Group Laws
The **GroupLaws** record captures the four group axioms that any group must satisfy:

```agda
record GroupLaws (X : ConSet) (ops : (i : Fin (nOps GroupSig)) → Operator X (proj₂ (proj₂ GroupSig i))) : Set where
  field
    left-identity : (x : asSet X) → 
         ops add-op (ops identity-op [] ∷ x ∷ []) ≡ x
    right-identity : (x : asSet X) → 
         ops add-op (x ∷ ops identity-op [] ∷ []) ≡ x
    associativity : (x y z : asSet X) → 
         ops add-op (ops add-op (x ∷ y ∷ []) ∷ z ∷ [])  ≡  ops add-op (x ∷ ops add-op (y ∷ z ∷ []) ∷ [])
    left-inverse : (x : asSet X) → 
         ops add-op (ops inv-op (x ∷ []) ∷ x ∷ []) ≡ ops identity-op []
    right-inverse : (x : asSet X) → 
         ops add-op (x ∷ ops inv-op (x ∷ []) ∷ []) ≡ ops identity-op []
```

## Finite Cyclic Group Operations
We implement group operations on `Fin (suc n)`, representing the cyclic group ℤ/(n+1)ℤ using modular arithmetic:

```agda
-- Addition operation (modular arithmetic)
fin-add : (n : ℕ) → Vec (Fin (suc n)) 2 → Fin (suc n)
fin-add n (a ∷ b ∷ []) = fromℕ< (m%n<n (toℕ a + toℕ b) (suc n))

-- Identity element
fin-identity : (n : ℕ) → Vec (Fin (suc n)) 0 → Fin (suc n)  
fin-identity n [] = zero

-- Inverse operation (additive inverse)
fin-inverse : (n : ℕ) → Vec (Fin (suc n)) 1 → Fin (suc n)
fin-inverse n (a ∷ []) = fromℕ< (m%n<n ((suc n) ∸ toℕ a) (suc n))
```

## Main Construction
The **CyclicGroup** function constructs a complete group structure with verified laws:

```agda
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
    
    laws : GroupLaws (proj₁ structure) (proj₂ structure)
    laws = record
      { left-identity = fin-left-identity n
      ; right-identity = fin-right-identity n  
      ; associativity = fin-associativity n
      ; left-inverse = fin-left-inverse n
      ; right-inverse = fin-right-inverse n
      }
```

This construction produces `Fin (suc n)` as the carrier set, representing ℤ/(n+1)ℤ, with all group axioms formally verified. The inhabitants `fin-left-identity n` etc are explicit proofs provided in the agda file.

## Examples
### ℤ/4ℤ - The Cyclic Group of Order 4

```agda
-- Create ℤ/4ℤ = Fin 4
Z4-with-laws : Σ (Structure {GroupSig}) (λ S → GroupLaws (proj₁ S) (proj₂ S))
Z4-with-laws = CyclicGroup 3  -- This gives us Fin 4

-- Extract the structure
Z4 : Structure {GroupSig}
Z4 = proj₁ Z4-with-laws

-- Convenient notation for operations
_+₄_ : Z4-carrier → Z4-carrier → Z4-carrier
a +₄ b = Z4-ops add-op (a ∷ b ∷ [])

-₄_ : Z4-carrier → Z4-carrier
-₄ a = Z4-ops inv-op (a ∷ [])
```

**Examples of computations:**
```agda
-- Addition: 1 + 3 = 0 in ℤ/4ℤ
example-add : (# 1) +₄ (# 3) ≡ (# 0)
example-add = refl

-- Inverse: -3 = 1 in ℤ/4ℤ
example-inv : -₄ (# 3) ≡ (# 1)
example-inv = refl

-- Left inverse law: (-3) + 3 = 0
example-left-inv : (-₄ (# 3)) +₄ (# 3) ≡ e4
example-left-inv = refl
```



> **Note**: The parameter `n` in `CyclicGroup n` produces the cyclic group ℤ/(n+1)ℤ with carrier `Fin (suc n)`. So `CyclicGroup 3` gives ℤ/4ℤ, and `CyclicGroup 5` gives ℤ/6ℤ.