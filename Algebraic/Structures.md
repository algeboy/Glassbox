# Algebra Structures

[ToC]

## Signatures
We begin with a signature.  For code we assume operators are given by string names and for simplicity we assume a prefix grammar with parentheses instead of order of operations.  So we need to capture just the name and the valence.
```math
\Omega:\bigsqcup_{n:\mathbb{N}} ([n]\to \text{String}\times \mathbb{N})
```
with the interpretation that there are $n$ operators and $\Omega[i]=\langle \text{name},\text{valence}\rangle$.  Having the index over a range makes it easier to write the code but it has no role in the algebra.
```agda
Signature : Set 
Signature = Σ[ n ∈ ℕ ] ((Fin n) → (String × ℕ))
```

Here is an example using the groups signature.
```agda
MonoidSig : Signature
MonoidSig = (2 , λ i → Vec.lookup operations i)
  where
    operations : Vec (String × ℕ) 2
    operations = ("1" , 0) ∷ ("·" , 2) ∷ []
```
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
Operator : (X : Set) → (String × ℕ) → Set
Operator X op = Vec X (proj₂ op) → X

AlgeStruct : (sig : Signature) → Set₁
AlgeStruct sig = Σ[ X ∈ Set ] 
                 ((i : Fin (proj₁ sig)) 
                 → Operator X ((proj₂ sig) i))
```
To inhabit an algebraic structure we create the signature as above in [signatures](#signatures) and then create an Agda `Set` with its operators.

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