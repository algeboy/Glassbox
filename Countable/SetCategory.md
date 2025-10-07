# Constructive Function Category

[ToC]

## Target-Source proofs

The source and target operators give out identities which must satisfy the laws given in the paper.  To inhabit these equations we must do so for all cases of the inductive type `ConFun` which in this prototype are the four functions between $\mathbb{N}$ and $[m]$.  Most of these are proved directly by reflexivity which means the normal formal form reduces to identical terms on each side of the equation.  For example,
```agda
    tgtSrcProof : (f : ConFun) → (◄ (f ◄) ≡ (f ◄))
    tgtSrcProof (ℕ←ℕ f₀) = refl
```
this works because $f :\mathbb{N}\to \mathbb{N}$ and invoking the constructors 
```agda
    _◄ (ℕ←ℕ f₀) = ℕ←ℕ (λ x → x)
    ◄_ (ℕ←ℕ f₀) = ℕ←ℕ (λ x → x)
```
So the riight, resp. left, hand side reduces identically.
```agda
    f ◄ = ℕ←ℕ (λ x → x)
◄ (f ◄) = (◄ (ℕ←ℕ (λ x → x)) = ℕ←ℕ (λ x → x)
```
So `refl`, more precisely 
```agda
    refl : ℕ←ℕ (λ x → x) = ℕ←ℕ (λ x → x)
```
suffices.

The remaining case are the same except that the refl now types to the various identity types of `F←F` or `ℕ←ℕ` or 
the error state as necessary.
```agda
tgtSrcProof : (f : ConFun) → (◄ (f ◄) ≡ (f ◄))
tgtSrcProof (F←F {m} {n} f₀) = refl
tgtSrcProof (F←ℕ {n} f₀) = refl
tgtSrcProof (ℕ←F {m} f₀) = refl
tgtSrcProof (ℕ←ℕ f₀) = refl
tgtSrcProof ▦ = refl
```
So these `refl` are not all the same type.  We get a similar proof for source-targets.
```agda
srcTgtProof : (f : ConFun) → ((◄ f) ◄ ≡ (◄ f))
srcTgtProof (F←F {m} {n} f₀) = refl
srcTgtProof (F←ℕ {n} f₀) = refl
srcTgtProof (ℕ←F {m} f₀) = refl
srcTgtProof (ℕ←ℕ f₀) = refl
srcTgtProof ▦ = refl
```

## Left/Right identities

Now when we turn to the other laws they each involve composition which is where equality and transport laws become essential.  We begin by case-splitting.

### Identities without state
Here is a case which does not involve equality but requires our function extensionality postulate.
```agda
tgtOrgProof : (f : ConFun) → ((◄ f) ← f ≡ f)
tgtOrgProof (ℕ←ℕ f₀) = {!!}  
```
Once more what we have here is Agda reducing `(◄ f)` to 
`ℕ←ℕ (λ x → x)` before composing with `f₀`.  Here Agda is more aggressive than we might expect because as programs we now have
```agda
LHS: ℕ←ℕ ((λ x → x) ∘ f₀ )
RHS: ℕ←ℕ f₀
```
It is no surprise that composing a function with the identity it does not change the values but it is perhaps a surprise that these two different looking programs are equated as this is an extensional position.  We can introduce a helper function.  We prove `(λ x → x) ∘ f ≡ f` for all functions by invoking extension which in effect applies the composition and thus goes beyond $\beta$-reduction.  
```agda
left-id-comp : ∀ {A B : Set} (f₀ : A → B) 
             → (id ∘ f₀) ≡ f
left-id-comp f₀ = funExt (λ x → refl)
```
Since application of `(λ z → z)` (not the variable name change to avoid trapping `x`) to `f₀ x` is `f₀ x`, the left-hand side and right-hand sides are now identically `f₀ x` and so equality is inhabited by `refl`.  So we return `λ x → refl : f₀ x ≡ f₀ x` as the function that verifies function extensionality of `(id ∘ f₀) ≡ f₀`.

Now returning to our test we simply need to transfer the proof to our type `ConFun` by `cong` which transports `ℕ←ℕ` across the proof of equality.
```agda
tgtOrgProof (ℕ←ℕ f₀) = cong ℕ←ℕ (left-id-comp f₀)
```
Other stateless examples are 
```agda
tgtOrgProof (ℕ←F {m} f₀) = cong ℕ←F (left-id-comp f₀)
tgtOrgProof ▦ = refl
```

### Identities with state
The remaining cases involve state, i.e. we work with ranges $[n]$ where $n$ can vary. This means that when we create $f:\mathbb{N}\to [n]$ and consider target $(\triangleleft f):[n]\to [n]$ we know by construction that $n=m$, i.e. `refl : n ≡ n` but we must transport  that evidence to the function composition to enable the proof.  Here is the case setup.
```agda
tgtOrgProof (F←F {m} {n} f₀) = helper where
    helper : (F←F {n} id ← F←F {m} {n} f₀) ≡ F←F {m} {n} f₀
    helper = {!!}
```
To fill the hole we simply use the decidable equality tests $n=n$ thus removing the dependence on state.  We then continue with to transport that evidence to the function extensionality method as in the stateless case.
```agda
tgtOrgProof (F←F {m} {n} f₀) = helper where
    helper : (F←F {n} id ← F←F {m} {n} f₀) ≡ F←F {m} {n} f₀
    helper with n ≟ n
    ... | yes refl = cong F←F (left-id-comp f₀)
    ... | no ¬p = ⊥-elim (¬p refl)
```
Once more the case `no` is never reached and we indicate that in our code/proof by assigning the return type as eliminating data from the void.  There is not such data which confirms this case is never reached but the type checker is therefore complete.

The remaining stateful case is similar.
```agda
tgtOrgProof (F←ℕ {n} f₀) = 
    helper where
    helper : (F←F {n} id ← F←ℕ {n} f₀) ≡ F←ℕ {n} f₀  
    helper with n ≟ n
    ... | yes refl = cong F←ℕ (left-id-comp f₀)
    ... | no ¬p = ⊥-elim (¬p refl)
```
The proofs of `(f ← (f ◄) ≡ f)` are symmetric using a right-sided helper function
```agda
right-id-comp : ∀ {A B : Set} (f₀ : A → B) → (f₀ ∘ id) ≡ f₀
right-id-comp f₀ = funExt (λ x → refl)
```

## Targets of compositions

Now we look at the rules for taking target of a composition.  Once more we have stateless version first.
```agda
tgtCompProof : (g f : ConFun) 
             → ((◄ (g ← f)) ≡ (◄ (g ← (◄ f))))
tgtCompProof (ℕ←ℕ g₀) (ℕ←ℕ f₀) = refl
```
This works though once more it is worthwhile observing that the results in fact reduce directly to the same normal form.
```agda
RHS: ◄ ((ℕ←ℕ g₀) ← (ℕ←ℕ f₀))
     ◄ ((ℕ←ℕ g₀ ∘ f₀))
     ℕ←ℕ (λ x → x)
LHS: ◄ ((ℕ←ℕ g₀) ← (◄ (ℕ←ℕ f₀)))
     ◄ ((ℕ←ℕ g₀) ← (ℕ←ℕ (λ x → x)))
     ◄ (ℕ←ℕ g₀ ∘ (λ x → x))
     ℕ←ℕ (λ x → x)
```
These are identical so 
```agda
refl : ℕ←ℕ (λ x → x) ≡ ℕ←ℕ (λ x → x)
```
suffices as proof.
Likewise
```agda
tgtCompProof (ℕ←ℕ g) (ℕ←F {a} f) = refl
```

### Stateful cases

Suppose now compose function over ranges.  As above, we use a helper function and `with` clause to decide `b=c` and use that evidence to guarantee we can reduce.  
```agda
-- F←F g cases
tgtCompProof (F←F {c} {d} g₀) (F←F {a} {b} f₀) 
    = helper where
    helper : (◄ (F←F {c} {d} g₀ ← F←F {a} {b} f₀)) 
    ≡ (◄ (F←F {c} {d} g₀ ← (◄ (F←F {a} {b} f₀))))
    helper with b ≟ c
    ... | yes refl = refl -- When b ≡ c, both sides work out to be equal
    ... | no _ = refl     -- When b ≢ c, both sides give ▦
```
Because this is ultimately about targets it will not depend on this evidence, it just needs the evidence to move further into the proof.  Without this the type checker is faced with the option of outputting the error marker instead of the composition.  This is why it is necessary.

From here we simply need to consider all 27 cases.

```agda
tgtCompProof : (g f : ConFun) → ((◄ (g ← f)) ≡ (◄ (g ← (◄ f))))
tgtCompProof (ℕ←ℕ g₀) (ℕ←ℕ f₀) = refl
tgtCompProof (ℕ←ℕ g₀) (ℕ←F {a} f₀) = refl

-- F←F g₀ cases
tgtCompProof (F←F {c} {d} g₀) (F←F {a} {b} f₀) = helper where
    helper : (◄ (F←F {c} {d} g₀ ← F←F {a} {b} f₀)) ≡ (◄ (F←F {c} {d} g₀ ← (◄ (F←F {a} {b} f₀))))
    helper with b ≟ c
    ... | yes refl = refl -- When b ≡ c, both sides work out to be equal
    ... | no _ = refl     -- When b ≢ c, both sides give ▦
tgtCompProof (F←F {c} {d} g₀) (F←ℕ {b} f₀) = helper where
    helper : (◄ (F←F {c} {d} g₀ ← (F←ℕ {b} f₀)) ≡ (◄ ((F←F {c} {d} g₀) ← (◄ (F←ℕ {b} f₀)))))
    helper with b ≟ c
    ... | yes refl = refl -- When b ≡ c, both sides work out to be equal
    ... | no _ = refl     -- When b ≢ c, both sides give ▦
-- ℕ←F g₀ cases
tgtCompProof (ℕ←F {c} g) (F←F {a} {b} f) = helper where
    helper : (◄ (ℕ←F {c} g ← F←F {a} {b} f)) ≡ (◄ (ℕ←F {c} g ← (◄ (F←F {a} {b} f))))
    helper with b ≟ c
    ... | yes refl = refl -- When b ≡ c, both sides work out to be equal
    ... | no _ = refl     -- When b ≢ c, both sides give ▦
tgtCompProof (ℕ←F {c} g₀) (F←ℕ {b} f₀) = helper where
    helper : (◄ (ℕ←F {c} g₀ ← (F←ℕ {b} f₀)) ≡ (◄ ((ℕ←F {c} g₀) ← (◄ (F←ℕ {b} f₀)))))
    helper with b ≟ c
    ... | yes refl = refl -- When b ≡ c, both sides work out to be equal
    ... | no _ = refl     -- When b ≢ c, both sides give ▦
-- F←ℕ g₀ cases
tgtCompProof (F←ℕ g₀) (ℕ←ℕ f₀) = refl
tgtCompProof (F←ℕ g₀) (ℕ←F f₀) = refl
-- Error cases
tgtCompProof (ℕ←ℕ g₀) (F←ℕ f₀) = refl
tgtCompProof (ℕ←ℕ g₀) (F←F f₀) = refl
tgtCompProof (ℕ←F g₀) (ℕ←ℕ f₀) = refl
tgtCompProof (ℕ←F g₀) (ℕ←F f₀) = refl
tgtCompProof (F←ℕ g₀) (F←ℕ f₀) = refl
tgtCompProof (F←ℕ g₀) (F←F f₀) = refl
tgtCompProof (F←F g₀) (ℕ←ℕ f₀) = refl
tgtCompProof (F←F g₀) (ℕ←F f₀) = refl
tgtCompProof _ ▦ = refl
tgtCompProof ▦ _ = refl
```



> **TBD** Surely a bit of thought and these can be refactored into one-line calls with a common helper.

The `srcCompProof` follows symmetrically with a special exception that helps us practice what we are seeing develop.  Consider the following case.
```agda
srcCompProof : (g f : ConFun) 
                → ((g ← f) ◄ ≡ ((g ◄) ← f) ◄)
srcCompProof _ ▦ = refl
srcCompProof _ _ = {!!}
```
If we type check this we get the following error.
```agda
g != g ◄ of type ConFun
when checking that the expression refl has type
(g ← ▦) ◄ ≡ (g ◄ ← ▦) ◄
```
What this shows is that the order of $\beta$-reduction is outer-most-left-most so it replace $f$ with the error state `▦` which is enough to trigger reductions but in this order these are already reduced.
```agda
RHS: (g ← ▦) ◄ 
LHS: (g ◄ ← ▦) ◄
```
It is clear that if we first removed the source and compared we would make some progress
```agda
RHS: g ← ▦
     ▦
LHS: g ◄ ← ▦
     ▦
```
So we need to do this in this order, composing with the constructo `(_◄)` after the fact with the source.   This requires turning the constructor into a function which can be done with a lambda which might look strange but simply takes in `q` and returns `q ◄`.  That might look like
```agda
p : (g ← ▦) ≡ (g ◄ ← ▦)
cong (λ q → (q ◄)) p 
```
Fortunately since `p` is filled by `refl` this bottoms out to `cong` of a `refl` which is in fact another `refl`.  So this thing can at times be proved by the compiler directly.  But you will need to give it hints by case splitting a bit more.  Here is what worked for me.
```agda
srcCompProof (F←F g₀) ▦ = refl
srcCompProof (F←ℕ g₀) ▦ = refl
srcCompProof (ℕ←F g₀) ▦ = refl
srcCompProof (ℕ←ℕ g₀) ▦ = refl
```
By exposing the inner term `g₀` the compiler can properly predict which reduction to apply when resolving the equation. As usual, all these `refl` look the same which muddies our understanding as readers but if you got in to the types you would see each is a different variation based on `cong (λ q₀ → (F←F {m} {n} q₀ ◄)) p`, etc. for each constructor, which are the right ones for the return type.

## Associativity

There is an straight-forward Agda ready proof of associativity of composition with the partial composition.
```agda
∘-assoc : ∀ {A B C D : Set} {h : C → D} {g : B → C} {f : A → B} 
        → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f) 
∘-assoc = refl
```
Our job is to wrap it.  We can allow Agda to fill in proofs that don't need many hints like some of the fail cases.
```agda
wrap-∘-assoc : (h g f : ConFun)
                → ((h ← (g ← f)) ≡ ((h ← g) ← f))
wrap-∘-assoc ▦ _ _ = refl
```

### Composing with ▦

After this we have number of similar cases that need light hints.
```agda
wrap-∘-assoc (ℕ←ℕ h₀) ▦ _ = refl
```
Filling in the first terms constructor here gives enough data for the reduction algorithm to fill in the middle composition as a ▦ so `refl` works.
You can replace this with all the necessary constructors, and you can put two constructors in with a single ▦.  
```agda 
wrap-∘-assoc (ℕ←ℕ h₀) (ℕ←ℕ g₀) ▦ = refl
```
Now when we have stateful compositions we reach a brittle bit of coding where two places can fail for different reasons.  Here is a demonstration.
```agda
wrap-∘-assoc (ℕ←F {y} h₀) (F←ℕ {x} g₀) ▦ with x ≟ y  
    ... | yes q = refl
    ... | no ¬q = refl
```
Instead of a single `refl` we first have to resolve where the failure is with a decidable equality test.  If that passes the reduction continues and eventually both sides are ▦ so `refl` applies.  If the decision fails, then the composition of the h and g fails as well, which of course still reduces to ▦ but in a different way and hence we have to follow that case through.

### Composing impossible

There are numerous incompatible composition based purely on constructors.  For example `ℕ←F` composed with `ℕ←F`.  These are mostly `relf`.  As above there are cases that need to break down based on who failure emerges, i.e. is it because stateful compositions can fail?  If so you need to make a decidable check like this.
```agda
wrap-∘-assoc (ℕ←ℕ h₀) (ℕ←F {w} g₀) (F←ℕ {v} f₀) with v ≟ w
... | yes p = refl
... | no ¬p = refl
```
### Double States.
The hardest case is when there are two compositions that are stateful.  Here we of course need to decidable test, which Agda can do.  However, this actually splits into cases like branching tree
```agda
wrap-∘-assoc (ℕ←F {y} h₀) (F←F {w} {x} g₀) (F←ℕ {v} f₀)  with v ≟ w | x ≟ y
... | yes p | yes q = {!!}
```
If we inspect the hole we find that we need to transport the proof `p` into the composition to change the types and so `refl` gets stuck being of the wrong type.  This is because these are nested, as in `p` gets decided, changes the types because of the `with` clause and then `q`.  What we actually need is to pair the proof `(p,q)`, make a single with, and project out to each individual proof.  So we introduce pairwise test to do that.
```agda
pairwiseEq : (v w x y : ℕ) → Dec ((v ≡ w) × (x ≡ y))
pairwiseEq v w x y with v ≟ w | x ≟ y
... | yes p | yes q = yes (p , q)
... | no ¬p | _     = no (λ { (p , _) → ¬p p })
... | _     | no ¬q = no (λ { (_ , q) → ¬q q })
```
Now we modify the `with` clause to decide both equalities as one case.
```agda
wrap-∘-assoc (ℕ←F {y} h₀) (F←F {w} {x} g₀) (F←ℕ {v} f₀)  with pairwiseEq v w x y
... | yes (p , q) =  {!!}
```
The hole now will depend on `p` and `q` simultaneously and so we can transport them all at once which prevents trapping `refl`.  Of course we still have to do the transporting, which our helper `hom-XYZ` functions do.
```agda
wrap-∘-assoc (ℕ←F {y} h₀) (F←F {w} {x} g₀) (F←ℕ {v} f₀)  with pairwiseEq v w x y
... | yes (p , q) =  trans (cong (ℕ←F h₀ ←_) (isHom-FFℕ g₀ f₀ p))
        (trans (isHom-ℕFℕ h₀ (g₀ ∘ subst Fin p ∘ f₀) q)
                (sym (trans (cong (_← F←ℕ f₀) (isHom-ℕFF h₀ g₀ q))
                            (isHom-ℕFℕ (h₀ ∘ subst Fin q ∘ g₀) f₀ p))))
```
Now there is an annoying issue I have not figured out.  When this fails it can fail for 3 reasons: $\neg p$, $\neg q$ or both.  This means that the way we fail is different.  So once more we trap ourselves with partial cases.   But all of these are going to bottom out as ▦ which means these will be `refl`.  However having paired the `p,q` is now seems trapped.  So `refl` alone doesn't quit do it.  But you can simply eliminate the contradiction.
```agda
wrap-∘-assoc (ℕ←F {y} h₀) (F←F {w} {x} g₀) (F←ℕ {v} f₀)  with pairwiseEq v w x y
... | yes (p , q) =  trans (cong (ℕ←F h₀ ←_) (isHom-FFℕ g₀ f₀ p))
        (trans (isHom-ℕFℕ h₀ (g₀ ∘ subst Fin p ∘ f₀) q)
                (sym (trans (cong (_← F←ℕ f₀) (isHom-ℕFF h₀ g₀ q))
                            (isHom-ℕFℕ (h₀ ∘ subst Fin q ∘ g₀) f₀ p))))
... | no contra = ⊥-elim (contra impossible)
    where
    impossible : (v ≡ w) × (x ≡ y)
    impossible = {!!} -- Don't fill a hole that can't be reached.
```
The only subtle point is that you need to inhabit the proof of the impossible type (the false claim of a pair of equalities.). That is impossible so we inhabit with a hole! 

This feels like a hack but I read Agda permits it.

Now, a back of the envelope calculation: if you fix h and g types there are still 5 cases for 5, namely the 5 types of `ConFun` so you have 125 cases, and very few can be packaged by wildcards but it does seem like a bit of refactoring would be possible or some tactics.  


