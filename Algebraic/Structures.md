# Algebra Structures

[ToC]

You will need a [Signature](Signatures.md), a list for $n$ operators given as pairs (name, valence). This is typically an implicit parameter to all the algebraic structures.  Here is an example using the groups signature.
```agda
GroupSig : Signature
GroupSig = (3 , λ i → lookup operations i)
  where
    operations : Vec (String × ℕ) 3
    operations = ("·" , 2) ∷ ("1" , 0) ∷ ("⁻¹" , 1) ∷ []
```
Read more at [Signature](Signatures.md).

## Universe sizing

Also this would be a good time to get loosely acquainted with our [Countable Sets](../Countable/Sets.agda).  This will play the role of creating algebraic structures on countable sets only but in a way that we can decide equality between the carrier sets of the algebraic structures.  In summary, 
 * the algebraic structures such as groups, rings, modules, monoids are of type `ConSet`, 
 * categories of algebraic structures level up to `Set`.  

This causes some duplication of structures, one for small universe of countable sets and one for their categories.  We use a subscript 1 for the larger universe algebras.

> In an ideal world we would simply use Agda's universes.  However we need to maintain a decidable type equality.  Our solution is to merely make an inductive type of all type-formers we allow which allows us to pattern match on the original state that made the types and decide on those.  This is how carrier sets in algebra emerge so it is a valid solution to our needs.

## Operators and algebraic structures
An algebraic structure has an implicit signature $\Omega$, a carrier set $X$, and a function that matches each operator $\langle \omega, n\rangle :\Omega$ with an function $X^{n}\to X$.
```math
\bigsqcup_{X:Set}\bigsqcup_{\omega:\Omega}(X^{\pi_2(\omega)}\to X)
```
Now in the code $\Omega$ is not a set but a function on a range $[n]$.  So we do the same with the algebraic structure.
```math
\bigsqcup_{X:Set}\prod_{i:[n]}(X^{\pi_2(\Omega[i])}\to X)
```
In Agda we split out an operator type and then make the above type.
```agda
Operator : ConSet → ℕ → Set
Operator X n = Vec (asSet X) n → asSet X
```
Recall we need to have one for the category of all algebraic structures, so its carriers are Agda's `Set`.
```agda
Operator₁ : Set → ℕ → Set
Operator₁ X n = Vec X n → X
```
Then an algebraic structure is merely a list of operators.  To make it computable we make it an enumerated list.
```agda
Structure : {sig : Signature} → Set
Structure {sig} = Σ[ X ∈ ConSet ] 
                ((i : Fin (nOps sig) ) → Operator X (proj₂ (proj₂ sig i)))
```
(Keep in mind there is a version for sets too, just cosmetic changes.)  To inhabit an algebraic structure we create the signature as above in [signatures](#signatures) and then create an Agda `Set` with its operators.

First make a type for the carrier set of $\mathbb{N}$ modulo $n:\mathbb{N}$.
```agda
ℕ/ : (n : ℕ) → Set
ℕ/ Nat.zero = ℕ -- ℕ/ 0 = ℕ 
ℕ/ n = Fin n
```
Define its monoid operations.
```agda
add : {n : ℕ} → Vec (ℕ/ n) 2 → ℕ/ n
add {Nat.zero} (a ∷ b ∷ []) = a + b -- Natural numbers
add {Nat.suc n} (a ∷ b ∷ []) = (toℕ a + toℕ b) mod (Nat.suc n)

zeta : {n : ℕ} → Vec (ℕ/ n) 0 → ℕ/ n
zeta {Nat.zero} [] = Nat.zero -- Natural numbers
zeta {Nat.suc n} [] = Fin.zero  -- Zero of Fin (suc n)
```
Then we put these together into an algebraic structure.
```agda
ModuloMonoidUnsafe : (n : ℕ) → AlgeStruct MonoidSig
ModuloMonoidUnsafe n = (ℕ/ n , operations )
  where
    operations : (i : Fin 2) → (Operator (ℕ/ n) (proj₂ MonoidSig i))
    operations Fin.zero = zeta {n} 
    operations (Fin.suc Fin.zero) = add {n} 
```
> **TBD** This approach makes it easy to get off on the signature.  A better approach is to lookup the signature by name and fill in the correct term.  We can add helper functions for this.

Unsafe here is to indicate we have no checks of any monoid axioms.

## Homomorphisms

Once we have algebraic structures we instantly get homomorphisms.  Homomorphisms are simply functions with proofs of the homomorphism property for the operators.  
```math
Hom_{\Omega}(\langle A,\omega_A\rangle,\langle B,\omega_B\rangle) := \bigsqcup_{f:A\to B}\prod_{\omega\in \Omega} \prod_{a:A^{|\omega|}} f(\omega_A(a))=\omega_B(f(a))
```
We use a few `Vec` map utilities to do this compactly.  Notice however that the type of underlying functions depends on the universe type.  So this too splits.
```agda
Homomorphism : ∀ {sig : Signature} → Structure {sig} → Structure {sig} → Set
Homomorphism {sig} (A , opsA) (B , opsB) = 
    Σ[ f ∈ (asSet A → asSet B) ]
    ((i : Fin (nOps sig)) →
        (a : Vec (asSet A) (proj₂ (proj₂ sig i))) →
            f (opsA i a) ≡ opsB i (map f a)
    )
```
Here is an example, the identity homomorphisms.
```agda
idHom : ∀ {sig : Signature} {A : Structure {sig}} → Homomorphism {sig} A A
idHom {sig} {A , opsA} = (idFun , idPf)
  where
    idFun : asSet A → asSet A
    idFun x = x
    
    idPf : (i : Fin (nOps sig)) →
            (x : Vec (asSet A) (proj₂ (proj₂ sig i))) →
            idFun (opsA i x) ≡ opsA i (map idFun x)
    idPf i x rewrite map-id x = refl
```
Better yet, anticipating the algebraic structure on the category of homomorphisms we can create that source and target operators.
```agda
source : ∀ {sig : Signature} {A B : Structure {sig}} 
        → Homomorphism {sig} A B 
        → Homomorphism {sig} A A
source {sig} {A} {B} (f , pf) = idHom {sig} {A}
```

There isn't a need for functors because our categories are built as abstract categories so those are simply homomorphisms (but on the `Set` unverse instead of `ConFun`.)
