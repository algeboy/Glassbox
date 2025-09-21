# Varieties

A variety is in the sense of universal algebra which means all algebraic structures with a fixed signature $\Omega$ that satisfy a collection of equational laws. 

[ToC]

## Laws

To make it feasible to enumerate we think of laws as functions on countable sets.  Actually I will use finite laws.  As a further simplification instead of making equations on different numbers of variables I will just use the largest number of variables that occur in the finite list of laws calling that $X$.

```math
L : \bigsqcup_{Laws:FinSet}\prod_{l:Laws}\bigsqcup_{X:FinSet}\Omega\langle X\rangle \times \Omega\langle X\rangle
```
For enhanced computation let us include a name for the operators as a string.
```agda
Variety : (sig : Signature) → Set₁ 
Variety sig = Σ[ n ∈ ℕ ] Σ[ X ∈ Set ] ((Fin n) → (String × Equation sig X))
```

An $\Omega$-algebraic structure $\mathbf{A}=\langle A,\omega\rangle$ is said to satisfy the laws when
```math
(\forall i:[n])(\forall c:A^X)\qquad \lambda_i\langle c\rangle = \rho_i\langle c\rangle \text{ where }L_i=(\lambda_i\langle X\rangle,\rho_i\langle X\rangle)
```
We wrap these in propositions as types and make a command to define satisfaction of an arbitrary equation.
```agda
{-- A mere proposition that states that an algebra satisfies an equation 
    for all interpretations of variables --}
SatEqProp : ∀ {X : Set} 
            → (sig : Signature)
            → (alg : AlgeStruct sig)
            → (eq : Equation sig X)
            → Set
SatEqProp {X} sig alg eq = 
    (const : X → proj₁ alg) 
    → evalFormula alg const (Equation.lhs eq) ≡ evalFormula alg const (Equation.rhs eq)
```
Remember this function creates the proposition that the equation is satisfied, it does not prove it.  To do that you have to know the equation and your algebra and do the actual algebra.  Below is a trivial example.

## A trivial law.

So now let us show that every algebraic structure satisfies the law $x=x$.
```agda
idEqPoly : (sig : Signature) → Equation sig (Fin 1)
idEqPoly sig = record { lhs = var (# 0) ; rhs = var (# 0) }

reflLawGeneral : ( sig : Signature )
                → (alg : AlgeStruct sig)
                → SatEqProp sig alg (idEqPoly sig)
reflLawGeneral sig alg = λ const → refl
```

## Certification

The point of a variety is to know what algebras belong to it so we offer now a certificate.



> **Theorem Brikhoff-von Neumann** A class $\mathfrak{v}$ of algebraic structures with fixed signature is a variety if, and only if, it is closed to direct products, homomorphic images, and subalgebras.

