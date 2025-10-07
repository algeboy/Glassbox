# Countable Functions

We describe a type for functions between countable sets.  Because we are making a category, we can work up to equivalence, so we treat countable functions by their cardinality.

[ToC]

In order to treat categories as algebraic structures we have a two step process of unifying all morphisms into a single type.

It is highly probably that some of these manipulations can be repeated more efficiently and generally without the constructs used here. There are two motivations for our choice.  First, we are not native speakers of Agda and therefore are unaware of its many opportunities.  Second, we want to expose the details in a manner that a more novice user such as a member of our own community from Computational Algebra but new to theorem provers can experience some of the learning we have benefited from in creating this prototype.

## Constructive Sets

Imagine you want a category with two families of objects $\mathbb{N}$ and $[n]=\{0,\ldots, n-1\}$ and functions between these sets as the morphisms. 

First we unify the objects 
```math
\text{ConSet} := \{\mathbb{N}\}\sqcup \bigsqcup_{n:\mathbb{N}}[n]
```
There is a problem with using a $\Sigma$ type which is that the terms here are types themselves and thus comparison falls into undecidable territory.  In general, comparing $A,B:Type$ via $A=_{Type}B$ is not generally a decidable type. So a proof involving valid composition of functions becomes impossible in general.  But we are pulling back to specifically constructed set $\mathbb{N}$ and $[n]$. If we keep track of that information, we can in fact decide equality as sets because our constructors have transport and therefore
```math
    m=n \to [m]=[n]
```
As all claims are backed by evidence, in Agda this will be developed into a function of types, one that is in fact part of Agda's standard libraries.
```agda 
    cong Fin : m ≡ n → (Fin m) ≡ (Fin n)
```
This is a hint of how we should add further data types.  

**We keep track of their constructors and rely on equality of the introductory data instead of the outcome.**  

This is perhaps notationally awkward and could be done within a programming language.  But exposing things at this level is a helpful observation of the process and avoids various problems that emerge with how Agda and other type checker internally frame their Set types.

So we use an inductive type to unify the constructive sets we consider.
```agda
data ConSet where 
    N : ConSet
    F : (n : ℕ) → ConSet
```
Note, `ℕ` is a unicode character allowed in Agda, but we have it already in use since we imported it from the [standard library](https://github.com/agda/agda-stdlib) as a natural number type.  Here, we are wrapping it, so we need a new characater `N`.  When building algebraic structures, we need to convert `ConSet` into the Agda's types, so we use 
```agda
asSet : ConSet → Set
asSet N = ℕ
asSet (F n) = Fin n
```

Here is a demonstration of how one might try to make a decideable equality on `Set`:
```agda
test : (A B : Set) -> Maybe A ≡ B
test A B with Dec (A ≡ B)
...| yes proof = just proof
...| no _ = nothing
```
This one does not compile because in general type comparisons are not decidable.  

Compare this with the following which backtracks through the constructors and compares their state. Thus it is decidable.
```agda
isEqual : (A B : ConSet) -> Maybe A ≡ B
isEqual (F a) (F b) = with a ≟ b
...| yes proof = just (refl : F a = F a)
...| no _ = nothing
isEqual N N = just refl
isEqual _ _ = nothing
```
Obviously the complexity is in length of code as we now have to carry out all the case distinctions, but mismatches in the cases lead to failures, so it is somewhat manageable.

> **Remark** It may seem ironic that Agda has carefully curated an environment where types are so specific that you cannot even attempt to compose functions with mismatched types.  Here, we are attempting to erase this difference but not without a purpose however.  We are interested in extending composition of functions from the *partial* binary operator to a *total* binary operator with an explicit error token.  This allows us to then model the category of sets within a variety rather than in a quasi-variety.  This allows us to begin performing computations on categories as algebras in their own right.  As a foundation for mathematics or programming one of course should stick with Agda universes.

### Expanding the constructive sets.

> **[TBD]** Someone should try this out to get the syntax right.

Imagine we now want to extend our types to include ordered pairs.  We would need to extend our cases.
```agda
data ConSet where 
    N : ConSet
    F : (n : ℕ) → ConSet
    P : (L R : ConSet) → ConSet
```
This would trigger us to add to `isEqual` a branching recursive call.
```agda
isEqual (P a b) (P c d) with (isEqual a b) ∧ᵈ (isEqual b d)
...| yes p = just p
...| no _  = nothing
```
Once more we will soon switch to just considering functions at which point we will consider functions on pairs not pairs directly.  So extensions here are mostly to gain some familiarity with the objective consequences.

## Functions

The morphisms are thus unified as well.
```math
\text{ConFun} := \begin{array}{c}
\{f:\mathbb{N}\to \mathbb{N}\}\\ 
\sqcup \\
\{f:[m]\to \mathbb{N}\}\\
\sqcup \\
\{f:\mathbb{N}\to [n]\}\\
\sqcup\\
\{f:[m]\to [n]\}
\end{array}
```
We develop this as a further inductive type.  Anticipating that composition is a partial function that we want to explicitly make total, we add an error marker.  (Note Agda uses $\bot$ for its void type, and although it is not in our scope, it is still too common to find exercises and help in agda with this assigned role, so it is safer from our perspective to introduce a different symbol `▦` for error marking.)
```agda
data ConFun : Set where
    ℕ←ℕ : (f : ℕ → ℕ) → ConFun
    ℕ←F : ∀ {n : ℕ} → (f : (Fin n) → ℕ) → ConFun
    F←ℕ : ∀ {n : ℕ} → (f : ℕ → (Fin n)) → ConFun
    F←F : ∀ {m n : ℕ} → (f : (Fin m) → (Fin n)) → ConFun
    ▦ : ConFun
```
Notice this type does not directly reference the object type `ConSet`.  This can be added with an internal pattern match to extract the information but this just causes more work in future code so already we see our rationale in moving towards a single sorted category.

### Example functions

You can now make any Agda function of type $\mathbb{N}\to \mathbb{N}$, $\mathbb{N}\to [n]$, $[m]\to\mathbb{N}$ or $[m]\to [n]$ and develop it as a `ConFun` type.  Here are some examples.
```agda 
    ff : ConFun
    ff = F←F {3} {4} (λ x → # zero)

    gg : ConFun
    gg = ℕ←F {4} (λ x → toℕ x)
```

### Composing 

Now our composition is meant to take place on all functions with the understanding that illegal compositions are given the error token.  This give a simple signature.
```agda
    _←_ : ConFun → ConFun → ConFun
```
Now as we split this into cases some are straight-forward because the types in the middle are  equal without transporting any data.  These are the cases with `N` in the middle.
```agda
    _←_ (ℕ←ℕ g) (ℕ←ℕ f) = ℕ←ℕ (g ∘ f)
    _←_ (ℕ←ℕ g) (ℕ←F f) = ℕ←F (g ∘ f)
    _←_ (F←ℕ g) (ℕ←F f) = F←F (g ∘ f)
    _←_ (F←ℕ g) (ℕ←ℕ f) = F←ℕ (g ∘ f)
```
We can also place errors where we know the composition is illegal, such as `N` matched with an `F`.  
```agda
    _←_ (ℕ←ℕ g) (F←ℕ f) = ▦
    _←_ (ℕ←ℕ g) (F←F f) = ▦
    ...
    _←_ (F←F g) (ℕ←F f) = ▦
```
As a convenience, we omit all of these nonsense cases by setting the default to return our error:
```agda
    _←_ _ _ = ▦
```
So now let us look at the places we need to decide on composability.  These occur when two `F` `F` meet in the middle since we have a parameter to compare.  Recall we have transport:
```agda
    cong Fin : m ≡ n → (Fin m) ≡ (Fin n)
```
And `m ≡ n` is decidable via `m ≟ n`.  So we just need to pass along the evidence of this decision.
```agda
    _←_ (F←F {c} {d} g) (F←F {a} {b} f) with b ≟ c
    ... | yes p = F←F (g ∘ subst Fin p ∘ f)
    ... | no _ = ▦
```
We explain a bit of the Agda notation.  Notice that the evidence that $b=c$ is decided at the function call.  Agda therefore breaks into two cases anticipating the possible outcomes (i.e. `yes` or `no`).  When $b=c$, we have not told all the types about the equality.  What we have is
```agda 
f : (Fin a) → (Fin b)
g : (Fin c) → (Fin d)
p : b ≡ c
```
The intuition of the next stage of the proof is perhaps clear: transport the proof that $b=c$ to make `Fin b ≡ Fin c`, but this still has to be used to transport `g` from `(Fin c) → (Fin d)` to `(Fin b) → (Fin d)` via the evidence `cong Fin p : Fin b ≡ Fin c`.  Agda has built in functions to do this transporting `subst Fin p` which is syntatically placed between the composition of `g` after `f`.  Hence the syntax of our solution.

There are 4 cases with `F` in the middle and they all follow this pattern.  Here is the complete type.
```agda
    infix 50 _←_. -- Setup infix notation 

    _←_ : ConFun → ConFun → ConFun
    _←_ (ℕ←ℕ g) (ℕ←ℕ f) = ℕ←ℕ (g ∘ f)
    _←_ (ℕ←ℕ g) (ℕ←F f) = ℕ←F (g ∘ f)
    _←_ (F←ℕ g) (ℕ←F f) = F←F (g ∘ f)
    _←_ (F←ℕ g) (ℕ←ℕ f) = F←ℕ (g ∘ f)

    _←_ (F←F {c} {d} g) (F←F {a} {b} f) with b ≟ c
    ... | yes p = F←F (g ∘ subst Fin p ∘ f)
    ... | no _ = ▦
    _←_ (ℕ←F {c} g) (F←F {a} {b} f) with b ≟ c
    ... | yes p = ℕ←F (g ∘ subst Fin p ∘ f)
    ... | no _ = ▦
    _←_ (F←F {b} {c} g) (F←ℕ {a} f) with a ≟ b
    ... | yes p = F←ℕ (g ∘ subst Fin p ∘ f)
    ... | no _ = ▦
    _←_ (ℕ←F {b} g) (F←ℕ {a} f) with a ≟ b
    ... | yes p = ℕ←ℕ (g ∘ subst Fin p ∘ f)
    ... | no _ = ▦
    _←_ _ _ = ▦
```

> **TBD** this notation could be unfortunate.  We have Agda formating f : A -> B but composition is g f : A -> D where g : C -> D and B = C.  So the constructor `F {m} {n} f` is in the order of the Agda syntax but it means an awkward outer order in this composition.

Here we can test our composition on the functions created.  Try some others.
```agda
    gf : ConFun
    gf = gg ← ff
```
Note that this case is in fact going through the tough case where we have forgotten the middle `Fin 4` identical in a way that Agda can be certain.

### Heteromorphism property

In order to form proofs of the axioms of a category, we will need to relate the composition as Agda functions with the composition as `ConFun`.  The fundamental extension is that we have make illegal compositions legal via the error tag.  However in Agda illegal compositions do not compile.  Therefore must form the claims of compatibility only partial.

Let us begin by reflecting the state independent cases.  These can appeal to `refl` as proof because they simply use pattern matching and reduce both sides to the same normal form.  For example,
```agda
    isHom-ℕℕℕ : (g f : ℕ → ℕ) 
              → ( (ℕ←ℕ g) ← (ℕ←ℕ f) ≡ (ℕ←ℕ (g ∘ f)) )
    isHom-ℕℕℕ g f = refl
```
Agda looks up the composition pattern 
```agda
    (ℕ←ℕ g) ← (ℕ←ℕ f) = (ℕ←ℕ (g ∘ f))
```
which clearly matches the RHS and so `refl` is a proof.  The same process matches all other patterns without state as listed here.  E.g. 
```agda
    isHom-ℕℕF : ∀ {a : ℕ} (g : ℕ → ℕ) (f : Fin a → ℕ) 
              → ( (ℕ←ℕ g) ← (ℕ←F {a} f) ≡ (ℕ←F {a} (g ∘ f)) )
    isHom-ℕℕF {a} g f = refl
```
There are 4 such cases but it makes sense to organize them in some systematic pattern so we leave the rest to be included later.

Now let us consider valid compositions with state, our `F` cases.  The signature is immediate, replacing natural numbers with Fin sets.  In part to help us imaging this as a proposition instead of a function we use the $\forall$ notation which Agda permits.
```agda 
    isHom-ℕFℕ : ∀ {b c : ℕ} (g : (Fin c) → ℕ) (f : ℕ → (Fin b)) → (p : b ≡ c)
              → ( (ℕ←F {c} g) ← (F←ℕ {b} f) ≡ (ℕ←ℕ (g ∘ subst Fin p ∘ f)) )
```
To be clear this says
```math
(\forall b,c\in \mathbb{N})(\forall g:[c]\to \mathbb{N})(\forall f:\mathbb{N}\to [b])\qquad [g]\circ [f] = [ g\circ f]
```
where $[f]$ indicates the effect of wrapping $f$ as a term of type `ConSet`.

Notice we give Agda the confidence to compose `g` after `f` by providing a proof of `b ≡ c` and as before when defining composition we use the builtin tools to transport that proof to the correct form of composition.  When using this lemma we will provide the evidence of `b ≡ c` via a pattern match on the decidable `b ≟ c` test.

Now consider the challenge of proving this claim.  It is clear that to begin we need to text that $b=c$ which we do with the the `with` pattern which can call our decision to test equality and direct us to the valid outcome.
```agda
    isHom-ℕFℕ : ∀ {b c : ℕ} (g : (Fin c) → ℕ) (f : ℕ → (Fin b)) → (p : b ≡ c)
              → ( (ℕ←F {c} g) ← (F←ℕ {b} f) ≡ (ℕ←ℕ (g ∘ subst Fin p ∘ f)) )
    isHom-ℕFℕ {b} {c} g f p with b ≟ c
    ... | yes q = {!liftIfValid!}
    ... | no _ = {!errorStateValid!}
```
We now have to fill our two holes.  Now here enters a new wrinkle.  We have a proof `p : b ≡ c` which was used to define the output type `ℕ←ℕ (g ∘ subst Fin p ∘ f)` on the right hand side of target equation.  But within the `with` clause we ask the runtime to secure a decision of equality and if it does it produces its own evidence `p : b ≡ c`.  This is precisely where equality takes on its characteristic complexity.  Should $p=q$?  That is, are we to say that there is only ever one proof of equality?  This gets into axiomatic concerns such as UIP (Uniqueness of Identity Proof) vs. Higher Type Theories and Univalence.  In the case we have before us the answer seems avoidable because we are comparing natural numbers.  For natural numbers equality is truncated at the first level giving us a unique proof of equality `refl`. That is `p ≡ refl ≡ q` and we just need to provide this argument to Agda to move forward.  Since we will also use this to lift to the `Fin` type composition we combine this into one helper function.
```agda
    transport-uniq-Fin : ∀ {b c : ℕ} (p q : b ≡ c) (x : Fin b)
                       → subst Fin q x ≡ subst Fin p x
    transport-uniq-Fin refl refl x = refl
```
One further nuance is that we need to now be clear about what we intend "equal functions" to mean.  In this context we are extensional in that we don't campare functions as equal or unequal based on programs.  If you compose with the identity function you get a different program but not different results.  Agda can reduce programs to normal form and compare that but to understand equality as same values is beyond computation.  So one has to include this form as an axiom of extensionality.  
```agda
-- Tell Agda what we mean "equal functions" to be. 
postulate 
    funExt : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g
```
If we assume univalence then this postulate is a theorem, but I will leave this as a postulate.

Given this support we now know what to do with a `yes`
```agda
    isHom-ℕFℕ {b} {c} g f p with b ≟ c
    ... | yes q = cong ℕ←ℕ (funExt λ x → cong g (transport-uniq-Fin p q (f x)))
    ... | no _ = {!!}
```
Finally to fill the `no` hole we again have the issue of the miss-matched `q` and `p` but this time we can eliminate the evidence of `¬q` to eliminate the existence of `p` and thus convince Agda that this case does not actually occur.
```agda
     ... | no ¬q = ⊥-elim (¬q p)
```
You cannot eliminate the void $\bot$ so this isn't reached, but now Agda knows this too.

Here is the resulting heteromorphism behavior.

---
```agda 
{-- 
    Show ConFun constructors are a 
    homomorphism _←_ to _∘_ 
--}
isHom-ℕℕℕ : (g f : ℕ → ℕ) 
            → ( (ℕ←ℕ g) ← (ℕ←ℕ f) ≡ (ℕ←ℕ (g ∘ f)) )
isHom-ℕℕℕ g f = refl

isHom-ℕℕF : ∀ {a : ℕ} (g : ℕ → ℕ) (f : Fin a → ℕ) 
            → ( (ℕ←ℕ g) ← (ℕ←F {a} f) ≡ (ℕ←F {a} (g ∘ f)) )
isHom-ℕℕF {a} g f = refl

-- Transport along different proofs b ≡ c is pointwise equal for Fin
transport-uniq-Fin : ∀ {b c : ℕ} (p q : b ≡ c) (x : Fin b)
                    → subst Fin q x ≡ subst Fin p x
transport-uniq-Fin refl refl x = refl

isHom-ℕFℕ : ∀ {b c : ℕ} (g : (Fin c) → ℕ) (f : ℕ → (Fin b)) → (p : b ≡ c)
            → ( (ℕ←F {c} g) ← (F←ℕ {b} f) ≡ (ℕ←ℕ (g ∘ subst Fin p ∘ f)) )
isHom-ℕFℕ {b} {c} g f p with b ≟ c
... | yes q = cong ℕ←ℕ (funExt λ x → cong g (transport-uniq-Fin p q (f x)))
... | no ¬q = ⊥-elim (¬q p)

isHom-ℕFF : ∀ {a b c : ℕ} (g : (Fin c) → ℕ) (f : (Fin a) → (Fin b)) → (p : b ≡ c)
            → ( (ℕ←F {c} g) ← (F←F {a} {b} f) ≡ (ℕ←F {a} (g ∘ subst Fin p ∘ f)) )
isHom-ℕFF {a} {b} {c} g f p with b ≟ c
... | yes q = cong ℕ←F (funExt λ x → cong g (transport-uniq-Fin p q (f x)))
... | no ¬q = ⊥-elim (¬q p)

isHom-Fℕℕ : ∀ {d : ℕ} (g : ℕ → (Fin d)) (f : ℕ → ℕ)
            → ( (F←ℕ {d} g) ← (ℕ←ℕ f) ≡ (F←ℕ {d} (g ∘ f)) )
isHom-Fℕℕ {d} g f = refl

isHom-FℕF : ∀ {a d : ℕ} (g : ℕ → (Fin d)) (f : (Fin a) → ℕ)
            → ( (F←ℕ {d} g) ← (ℕ←F {a} f) ≡ (F←F {a} {d} (g ∘ f)) )
isHom-FℕF {d} g f = refl

isHom-FFℕ : ∀ {b c d : ℕ} (g : (Fin c) → (Fin d)) (f : ℕ → (Fin b)) → (p : b ≡ c)
            → ( (F←F {c} {d} g) ← (F←ℕ {b} f) ≡ (F←ℕ {d} (g ∘ subst Fin p ∘ f)) )
isHom-FFℕ {b} {c} {d} g f p with b ≟ c
... | yes q = cong F←ℕ (funExt λ x → cong g (transport-uniq-Fin p q (f x)))
... | no ¬q = ⊥-elim (¬q p)

isHom-FFF : ∀ {a b c d : ℕ} (g : (Fin c) → (Fin d)) (f : (Fin a) → (Fin b)) → (p : b ≡ c)
            → ( (F←F {c} {d} g) ← (F←F {a} {b} f) ≡ (F←F {a} {d} (g ∘ subst Fin p ∘ f)) )
isHom-FFF {a} {b} {c} {d} g f p with b ≟ c
... | yes q = cong F←F (funExt λ x → cong g (transport-uniq-Fin p q (f x)))
... | no ¬q = ⊥-elim (¬q p)
```
---

### Extending functions
If we add pairs then we would add cases to the constructors.  These become recursively defined.


## Adding source & Target data
 
To form a category it is necessary to reflect the source identity and target identity maps as well.  So we add these.

```agda
    -- Valence 1 operators have higher 
    -- precedence than composition
    infix 99 _◄
    infix 99 ◄_

    {-- In operators --}
    _◄ : ConFun → ConFun
    _◄ (F←F {a} {b} f) = F←F {a} (λ x → x)
    _◄ (F←ℕ {b} f)     = ℕ←ℕ (λ x → x)
    _◄ (ℕ←F {a} f)     = F←F {a} (λ x → x)
    _◄ (ℕ←ℕ f)         = ℕ←ℕ (λ x → x)
    _◄ (▦)             = ▦

    {-- Out operators --}
    ◄_ : ConFun → ConFun
    ◄_ (F←F {a} {b} f) = F←F {b} (λ x → x)
    ◄_ (F←ℕ {b} f)     = F←F {b} (λ x → x)
    ◄_ (ℕ←F {a} f)     = ℕ←ℕ (λ x → x)
    ◄_ (ℕ←ℕ f)         = ℕ←ℕ (λ x → x)
    ◄_ (▦)             = ▦
```
The relevant laws of these operators takes us towards inhabiting our category type.

## Axioms

These are done in [Axioms](ConFunCat.md)
