
  
  
    rightNull : (h : ConFun) → (h ← ▦) ≡ ▦
    rightNull (F←F {c} {d} h) = refl
    rightNull (F←ℕ {c} h) = refl
    rightNull (ℕ←F {c} h) = refl
    rightNull (ℕ←ℕ h) = refl
    rightNull ▦ = refl

    {-- Helper lemmas for composition when types align --}


    {-- left nullity of composition --}
    leftNull : (h : ConFun) → (▦ ← h)  ≡ ▦
    leftNull (F←F {a} {b} h) = refl
    leftNull (F←ℕ {b} h) = refl
    leftNull (ℕ←F {a} h) = refl
    leftNull (ℕ←ℕ h) = refl
    leftNull ▦ = refl


    -- Right helpers.
    rightMidNull : (h f : ConFun) → ▦ ≡ ((h ← ▦) ← f)  
    rightMidNull (F←F {a} {b} h) (F←F {c} {d} f) = refl
    rightMidNull (F←F {a} {b} h) (F←ℕ {c} f) = refl
    rightMidNull (F←F {a} {b} h) ▦ = refl

    rightMidNull (F←ℕ {a} h) (F←F {c} {d} f) = refl
    rightMidNull (F←ℕ {a} h) (F←ℕ {c} f) = refl
    rightMidNull (F←ℕ {a} h) ▦ = refl

    rightMidNull (ℕ←F {a} h) (F←F {c} {d} f) = refl
    rightMidNull (ℕ←F {a} h) (F←ℕ {c} f) = refl
    rightMidNull (ℕ←F {a} h) ▦ = refl

    rightMidNull (ℕ←ℕ h) _ = refl
    -- (F←F {c} {d} f) = refl
    -- rightMidNull (ℕ←ℕ h) (F←ℕ {c} f) = refl
    -- rightMidNull (ℕ←ℕ h) ▦  = refl

    rightMidNull ▦ f = refl


    rightRightNull : (h g : ConFun) → ▦ ≡ ((h ← g) ← ▦) 
    rightRightNull (F←F {w} {x} h) (F←F {u} {v} g) with w ≟ u
    ... | yes refl = refl
    ... | no _ = refl
    rightRightNull _ _ = refl


    -- Helper: subst with refl is identity
    subst-id : ∀ {A : Set} {x : A} → subst (λ _ → A) refl x ≡ x
    subst-id = refl
    
    -- Composition associativity for F←F when types align
    -- assocF←F : ∀ {a b c d : ℕ} (h : Fin c → Fin d) (g : Fin b → Fin c) (f : Fin a → Fin b) 
    --          → (F←F h ← (F←F g ← F←F f)) ≡ ((F←F h ← F←F g) ← F←F f)
    -- assocF←F {a} {b} {c} {d} h g f = 
    --     trans (cong (F←F h ←_) (compProof g f)) 
    --           (trans (compProof h (g ∘ f))
    --                  (trans (cong F←F (funExt λ x → refl))
    --                         (sym (compProof (h ∘ g) f))))    
                            
                     
    -- ascCompProof (ℕ←ℕ h) (ℕ←F {u} g) (F←ℕ {t} f) = helper where 
    --     helper : ((ℕ←ℕ h ← (ℕ←F {u} g ← F←ℕ {t} f)) ≡ ((ℕ←ℕ h ← (ℕ←F {u} g)) ← F←ℕ {t} f))
    --     helper with u ≟ t
    --     ... | yes refl = refl
    --     ... | no _ = refl
    -- ascCompProof (ℕ←ℕ h) (ℕ←F {u} g) (F←F {s} {t} f) = helper where
    --     helper : ((ℕ←ℕ h ← (ℕ←F {u} g ← F←F {s} {t} f)) ≡ ((ℕ←ℕ h ← (ℕ←F {u} g)) ← F←F {s} {t} f))
    --     helper with (u ≟ t)
    --     ... | yes refl = refl
    --     ... | no _ = refl

    -- ascCompProof (ℕ←F {w} h) (F←ℕ {v} g) (ℕ←ℕ f) = helper where
    --     helper : ((ℕ←ℕ h ← (ℕ←F {w} g ← F←ℕ {v} f)) ≡ ((ℕ←ℕ h ← (ℕ←F {w} g)) ← F←ℕ {v} f))
    --     helper with w ≟ v
    --     ... | yes refl = refl
    --     ... | no _ = refl

    -- Now we can use our helper for F←F cases
    -- ascCompProof (F←F {w} {x} h) (F←F {u} {v} g) (F←F {s} {t} f) = assocF←F h g f

    -- ascCompProof (ℕ←ℕ h) (ℕ←ℕ g) (ℕ←F {s} f) = refl
    -- ascCompProof (ℕ←ℕ h) (ℕ←F {u} g) (F←ℕ {t} f) = helper where 
    --     helper : ((ℕ←ℕ h ← (ℕ←F {u} g ← F←ℕ {t} f)) ≡ ((ℕ←ℕ h ← (ℕ←F {u} g)) ← F←ℕ {t} f))
    --     helper with u ≟ t
    --     ... | yes refl = refl
    --     ... | no _ = refl
    -- ascCompProof (ℕ←ℕ h) (ℕ←F {u} g) (F←F {s} {t} f) = helper where
    --     helper : ((ℕ←ℕ h ← (ℕ←F {u} g ← F←F {s} {t} f)) ≡ ((ℕ←ℕ h ← (ℕ←F {u} g)) ← F←F {s} {t} f))
    --     helper with (u ≟ t)
    --     ... | yes refl = refl
    --     ... | no _ = refl

    -- ascCompProof (F←F {w} {x} h) (F←F {u} {v} g) (F←F {s} {t} f) = helper where
    --     helper : ((F←F {w} {x} h ← (F←F {u} {v} g ← F←F {s} {t} f)) ≡ ((F←F {w} {x} h ← (F←F {u} {v} g)) ← F←F {s} {t} f))
    --     helper with (t ≟ u,v ≟ w)
    --     ... | yes (p1,p2) = refl
    --     ... | no _ = refl
    -- ascCompProof (F←F {w} {x} h) (F←ℕ {v} g) (ℕ←F {s} f) = helper where
    --     helper : ((F←F {w} {x} h ← (F←ℕ {v} g ← ℕ←F {s} f)) ≡ ((F←F {w} {x} h ← (F←ℕ {v} g)) ← ℕ←F {s} f))
    --     helper with v ≟ w
    --     ... | yes refl = refl
    --     ... | no _ = refl
    -- ascCompProof (F←ℕ {a} h) (F←F {b} {c} g) (F←F {d} {e} f) = helper where
    --     helper : ((F←ℕ {a} h ← (F←F {b} {c} g ← F←F {d} {e} f)) ≡ ((F←ℕ {a} h ← (F←F {b} {c} g)) ← F←F {d} {e} f))
    --     helper with c ≟ aß
    --     ... | yes refl = refl
    --     ... | no _ = refl
    