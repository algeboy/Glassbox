# Homomorphism

Homomorphisms are designed to form an abstract category.  This means they are a subtype to `ConFun` but they generate a subcategory of `ConFun`'s category.

To make an abstract category, we need to split on the case that $f\neq \bot$, which should  count as a homomorphism but not in the sense of the homomorphism property.

The first thing is to make a simple-to-read type that states the expected homomorphism condition.  As usual, the implicits are on the left-hand side.
```math
\text{hom}_{\Omega}(\langle A,\omega_A\rangle,\langle B,\omega_B\rangle) :=\sqcup_{f:A\to B} \prod_{\omega:\Omega}\prod_{a:A^{|\omega|}}f(\omega_A(a))=\omega_B(\text{map}(f,a))
```
So we build that type.
```agda
HomProof : ∀ {sig : Signature} {A B : Structure {sig}} 
        → (f : asSet (proj₁ A) → asSet (proj₁ B)) 
        → Set
HomProof {sig} {A , opsA} {B , opsB} f = 
    (i : Fin (nOps sig)) →
    (x : Vec (asSet A) (proj₂ (proj₂ sig i))) →
        f (opsA i x) ≡ opsB i (map f x)
```

Now the work of making a homomorphism is to take such a proof and guard that a given function has it.
```agda
asHom-FF : ∀ {sig : Signature} {a b : ℕ}
            → (A : Structure {sig} ) 
            → (B : Structure {sig} ) 
            → {pA : proj₁ A ≡ F a}
            → {pB : proj₁ B ≡ F b}
            → (f : asSet (proj₁ A) → asSet (proj₁ B)) 
            → (isHom : HomProof {sig} {A} {B} f)
            → ConFun
asHom-FF (F a , opsA) (F b , opsB) {refl} {refl} f isHom  = F←F {a} {b} f
```
