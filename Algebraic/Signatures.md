# Signatures

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
And for groups
```agda
GroupSig : Signature
GroupSig = (3 , λ i → lookup operations i)
  where
    operations : Vec (String × ℕ) 3
    operations = ("·" , 2) ∷ ("1" , 0) ∷ ("⁻¹" , 1) ∷ []
```
[Note: this is using `_∷_` from `Data.Vec` note `List`.  Check your name space.]

There are a couple helper functions in signatures.

Extract the operator name from index
```agda
name : (sig : Signature) → (i : Fin (proj₁ sig)) → String
name sig i = proj₁ (proj₂ sig i)
```

Extract the valence from index
```agda
valence : (sig : Signature) → (i : Fin (proj₁ sig)) → ℕ
valence sig i = proj₂ (proj₂ sig i)
```
