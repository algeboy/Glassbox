
open import Data.Nat using (ℕ; _≟_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)


open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl; subst; _≡_; cong; sym; trans; subst-∘)
open import Relation.Nullary using (yes; no; Dec)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import Function using (_∘_; id)


open import Algebraic.Signatures
open import Countable.Sets
open import Algebraic.Structures



{-- A minimal countable constructive set category. --}
module Countable.SetLaws where

    {-- Laws --}
    {-- target of source = source --}
    tgtSrcProof : (f : ConFun) → (◄ (f ◄) ≡ (f ◄))
    tgtSrcProof (F←F {m} {n} f) = refl
    tgtSrcProof (F←ℕ {n} f) = refl
    tgtSrcProof (ℕ←F {m} f) = refl
    tgtSrcProof (ℕ←ℕ f) = refl
    tgtSrcProof ▦ = refl

    {-- source of target = target --}
    srcTgtProof : (f : ConFun) → ((◄ f) ◄ ≡ (◄ f))
    srcTgtProof (F←F {m} {n} f) = refl
    srcTgtProof (F←ℕ {n} f) = refl
    srcTgtProof (ℕ←F {m} f) = refl
    srcTgtProof (ℕ←ℕ f) = refl
    srcTgtProof ▦ = refl


    -- Left Identity composition law: (λ x → x) ∘ f ≡ f
    left-id-comp : ∀ {A B : Set} (f : A → B) → (id ∘ f) ≡ f
    left-id-comp f = funExt (λ x → refl)


    
    {-- target of origin = origin --}
    tgtOrgProof : (f : ConFun) → ((◄ f) ← f ≡ f)
    tgtOrgProof (ℕ←ℕ f) = cong ℕ←ℕ (left-id-comp f)
    tgtOrgProof (ℕ←F {m} f) = cong ℕ←F (left-id-comp f)

    tgtOrgProof (F←F {m} {n} f) = 
        helper where
        helper : (F←F {n} id ← F←F {m} {n} f) ≡ F←F {m} {n} f
        helper with n ≟ n
        ... | yes refl = cong F←F (left-id-comp f)
        ... | no ¬p = ⊥-elim (¬p refl)
    
    tgtOrgProof (F←ℕ {n} f) = 
        helper where
        helper : (F←F {n} id ← F←ℕ {n} f) ≡ F←ℕ {n} f  
        helper with n ≟ n
        ... | yes refl = cong F←ℕ (left-id-comp f)
        ... | no ¬p = ⊥-elim (¬p refl)
    
    tgtOrgProof ▦ = refl

    -- Right Identity composition law: f ∘ (λ x → x) ≡ f
    right-id-comp : ∀ {A B : Set} (f : A → B) → (f ∘ id) ≡ f
    right-id-comp f = funExt (λ x → refl)

    {-- origin of source = origin --}
    orgSrcProof : (f : ConFun) → (f ← (f ◄) ≡ f)
    orgSrcProof (ℕ←ℕ f) = refl 
    orgSrcProof (F←ℕ {n} f) = refl
    orgSrcProof ▦ = refl
    orgSrcProof (F←F {m} {n} f) = 
        helper where
        helper : (F←F {m} {n} f ← F←F {m} {m} id) ≡ F←F {m} {n} f
        helper with m ≟ m
        ... | yes refl = cong F←F (right-id-comp f)
        ... | no ¬p = ⊥-elim (¬p refl)
    orgSrcProof (ℕ←F {m} f) = helper where
        helper : (ℕ←F {m} f ← F←F {m} id) ≡ ℕ←F {m} f
        helper with m ≟ m
        ... | yes refl = cong ℕ←F (right-id-comp f)
        ... | no ¬p = ⊥-elim (¬p refl)

       
    {-- target of composite = target of first composed with target of last --}
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
    tgtCompProof (ℕ←F {c} g₀) (F←F {a} {b} f₀) = helper where
        helper : (◄ (ℕ←F {c} g₀ ← F←F {a} {b} f₀)) ≡ (◄ (ℕ←F {c} g₀ ← (◄ (F←F {a} {b} f₀))))
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

    {-- source of composite = source of source of first composed with orginal --}
    srcCompProof : (g f : ConFun) 
                    → ((g ← f) ◄ ≡ ((g ◄) ← f) ◄)
    srcCompProof (ℕ←ℕ g₀) (ℕ←ℕ f₀) = refl
    srcCompProof (ℕ←ℕ g₀) (ℕ←F {a} f₀) = refl

    -- F←F g₀ cases
    srcCompProof (F←F {c} {d} g₀) (F←F {a} {b} f₀) = helper where
        helper : ((F←F {c} {d} g₀ ← F←F {a} {b} f₀) ◄) ≡
                ((F←F {c} {d} g₀) ◄ ← F←F {a} {b} f₀ ) ◄
        helper with b ≟ c
        ... | yes refl = refl -- When b ≡ c, both sides work out to be equal
        ... | no _ = refl     -- When b ≢ c, both sides give ▦
    srcCompProof (F←F {c} {d} g₀) (F←ℕ {b} f₀) = helper where
        helper : ((F←F {c} {d} g₀ ← F←ℕ {b} f₀) ◄) ≡
                ((F←F {c} {d} g₀) ◄ ← F←ℕ {b} f₀) ◄
        helper with b ≟ c
        ... | yes refl = refl -- When b ≡ c, both sides work out to be equal
        ... | no _ = refl     -- When b ≢ c, both sides give ▦
    -- ℕ←F g₀ cases
    srcCompProof (ℕ←F {c} g₀) (F←F {a} {b} f₀) = helper where
        helper : ((ℕ←F {c} g₀ ← F←F {a} {b} f₀) ◄) ≡
                ((ℕ←F {c} g₀) ◄ ← F←F {a} {b} f₀ ) ◄
        helper with b ≟ c
        ... | yes refl = refl -- When b ≡ c, both sides work out to be equal
        ... | no _ = refl     -- When b ≢ c, both sides give ▦
    srcCompProof (ℕ←F {c} g₀) (F←ℕ {b} f₀) = helper where
        helper : ((ℕ←F {c} g₀ ← F←ℕ {b} f₀) ◄) ≡
                ((ℕ←F {c} g₀) ◄ ← F←ℕ {b} f₀) ◄
        helper with b ≟ c
        ... | yes refl = refl -- When b ≡ c, both sides work out to be equal
        ... | no _ = refl     -- When b ≢ c, both sides give ▦
    -- F←ℕ g₀ cases
    srcCompProof (F←ℕ g₀) (ℕ←ℕ f₀) = refl
    srcCompProof (F←ℕ g₀) (ℕ←F f₀) = refl
    -- Error cases
    srcCompProof (ℕ←ℕ g₀) (F←ℕ f₀) = refl
    srcCompProof (ℕ←ℕ g₀) (F←F f₀) = refl
    srcCompProof (ℕ←F g₀) (ℕ←ℕ f₀) = refl
    srcCompProof (ℕ←F g₀) (ℕ←F f₀) = refl
    srcCompProof (F←ℕ g₀) (F←ℕ f₀) = refl
    srcCompProof (F←ℕ g₀) (F←F f₀) = refl
    srcCompProof (F←F g₀) (ℕ←ℕ f₀) = refl
    srcCompProof (F←F g₀) (ℕ←F f₀) = refl
    srcCompProof ▦ _ = refl
    srcCompProof (F←F g₀) ▦ = refl
    srcCompProof (F←ℕ g₀) ▦ = refl
    srcCompProof (ℕ←F g₀) ▦ = refl
    srcCompProof (ℕ←ℕ g₀) ▦ = refl

    {-- Associativity of ConFun --}

    pairwiseEq : (v w x y : ℕ) → Dec ((v ≡ w) × (x ≡ y))
    pairwiseEq v w x y with v ≟ w | x ≟ y
    ... | yes p | yes q = yes (p , q)
    ... | no ¬p | _     = no (λ { (p , _) → ¬p p })
    ... | _     | no ¬q = no (λ { (_ , q) → ¬q q })

    {-- Wrap ∘-assoc for ConFun --}
    ∘-assoc : (h g f : ConFun)
                 → ((h ← (g ← f)) ≡ ((h ← g) ← f))
    ∘-assoc ▦ _ _ = refl
    
    ---ℕ←ℕ--------------
    -- ℕ←ℕ ▦ _
    ∘-assoc (ℕ←ℕ h₀) ▦ _ = refl
    
    -- ℕ←ℕ ℕ←ℕ ▦
    ∘-assoc (ℕ←ℕ h₀) (ℕ←ℕ g₀) ▦ = refl
    -- ℕ←ℕ ℕ←ℕ ℕ←ℕ
    ∘-assoc (ℕ←ℕ h₀) (ℕ←ℕ g₀) (ℕ←ℕ f₀) = refl
    -- ℕ←ℕ ℕ←ℕ ℕ←F
    ∘-assoc (ℕ←ℕ h₀) (ℕ←ℕ g₀) (ℕ←F f₀) = refl
    -- ℕ←ℕ ℕ←ℕ F←ℕ
    ∘-assoc (ℕ←ℕ h₀) (ℕ←ℕ g₀) (F←ℕ f₀) = refl
    -- ℕ←ℕ ℕ←ℕ F←F
    ∘-assoc (ℕ←ℕ h₀) (ℕ←ℕ g₀) (F←F f₀) = refl

    -- ℕ←ℕ ℕ←F ▦
    ∘-assoc (ℕ←ℕ h₀) (ℕ←F {w} g₀) ▦ = refl
    -- ℕ←ℕ ℕ←F ℕ←ℕ
    ∘-assoc (ℕ←ℕ h₀) (ℕ←F {w} g₀) (ℕ←ℕ f₀) = refl
    -- ℕ←ℕ ℕ←F ℕ←F
    ∘-assoc (ℕ←ℕ h₀) (ℕ←F {w} g₀) (ℕ←F f₀) = refl
    -- ℕ←ℕ ℕ←F F←ℕ
    ∘-assoc (ℕ←ℕ h₀) (ℕ←F {w} g₀) (F←ℕ {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl
    -- ℕ←ℕ ℕ←F F←F
    ∘-assoc (ℕ←ℕ h₀) (ℕ←F {w} g₀) (F←F {u} {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl

    -- ℕ←ℕ F←ℕ ▦
    ∘-assoc (ℕ←ℕ h₀) (F←ℕ g₀) ▦ = refl
    -- ℕ←ℕ F←ℕ ℕ←ℕ
    ∘-assoc (ℕ←ℕ h₀) (F←ℕ g₀) (ℕ←ℕ f₀) = refl
    -- ℕ←ℕ F←ℕ ℕ←F
    ∘-assoc (ℕ←ℕ h₀) (F←ℕ g₀) (ℕ←F f₀) = refl
    -- ℕ←ℕ F←ℕ F←ℕ
    ∘-assoc (ℕ←ℕ h₀) (F←ℕ g₀) (F←ℕ f₀) = refl
    -- ℕ←ℕ F←ℕ F←F
    ∘-assoc (ℕ←ℕ h₀) (F←ℕ g₀) (F←F f₀ ) = refl
    
    -- ℕ←ℕ F←F ▦
    ∘-assoc (ℕ←ℕ h₀) (F←F g₀) ▦ = refl
    -- ℕ←ℕ F←F ℕ←ℕ
    ∘-assoc (ℕ←ℕ h₀) (F←F g₀) (ℕ←ℕ f₀) = refl
    -- ℕ←ℕ F←F ℕ←F
    ∘-assoc (ℕ←ℕ h₀) (F←F g₀) (ℕ←F f₀) = refl
    -- ℕ←ℕ F←F F←ℕ
    ∘-assoc (ℕ←ℕ h₀) (F←F {w} {x} g₀) (F←ℕ {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl
    -- ℕ←ℕ F←F F←F
    ∘-assoc (ℕ←ℕ h₀) (F←F {w} {x} g₀) (F←F {u} {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl

    ---ℕ←F--------------
    -- ℕ←F ▦ _
    ∘-assoc (ℕ←F {y} h₀) ▦ _ = refl

    -- Non composable cases
    -- ℕ←F ℕ←ℕ ▦
    ∘-assoc (ℕ←F h₀) (ℕ←ℕ g₀) ▦ = refl
    -- ℕ←F ℕ←ℕ ℕ←ℕ
    ∘-assoc (ℕ←F h₀) (ℕ←ℕ g₀) (ℕ←ℕ f₀) = refl
    -- ℕ←F ℕ←ℕ ℕ←F
    ∘-assoc (ℕ←F h₀) (ℕ←ℕ g₀) (ℕ←F f₀) = refl
    -- ℕ←F ℕ←ℕ F←ℕ
    ∘-assoc (ℕ←F h₀) (ℕ←ℕ g₀) (F←ℕ f₀) = refl
    -- ℕ←F ℕ←ℕ F←F
    ∘-assoc (ℕ←F h₀) (ℕ←ℕ g₀) (F←F f₀) = refl

    -- ℕ←F ℕ←F ▦
    ∘-assoc (ℕ←F h₀) (ℕ←F g₀) ▦ = refl
    -- ℕ←F ℕ←F ℕ←ℕ
    ∘-assoc (ℕ←F h₀) (ℕ←F g₀) (ℕ←ℕ f₀) = refl
    -- ℕ←F ℕ←F ℕ←F
    ∘-assoc (ℕ←F h₀) (ℕ←F g₀) (ℕ←F f₀) = refl
    -- ℕ←F ℕ←F F←ℕ
    ∘-assoc (ℕ←F h₀) (ℕ←F {w} g₀) (F←ℕ {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl
    -- ℕ←F ℕ←F F←F
    ∘-assoc (ℕ←F h₀) (ℕ←F {w} g₀) (F←F {u} {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl

    -- ℕ←F F←ℕ ▦
    ∘-assoc (ℕ←F {y} h₀) (F←ℕ {x} g₀) ▦ with x ≟ y  
    ... | yes q = refl
    ... | no ¬q = refl
    -- ℕ←F F←ℕ ℕ←ℕ
    ∘-assoc (ℕ←F {y} h₀) (F←ℕ {x} g₀) (ℕ←ℕ f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- ℕ←F F←ℕ ℕ←F
    ∘-assoc (ℕ←F {y} h₀) (F←ℕ {x} g₀) (ℕ←F f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- ℕ←F F←ℕ F←ℕ
    ∘-assoc (ℕ←F {y} h₀) (F←ℕ {x} g₀) (F←ℕ {v} f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- ℕ←F F←ℕ F←F
    ∘-assoc (ℕ←F {y} h₀) (F←ℕ {x} g₀) (F←F {u} {v} f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl

    -- ℕ←F F←F ▦
    ∘-assoc (ℕ←F {y} h₀) (F←F {w} {x} g₀) ▦ with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- ℕ←F F←F ℕ←ℕ
    ∘-assoc (ℕ←F {y} h₀) (F←F {w} {x} g₀) (ℕ←ℕ f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- ℕ←F F←F ℕ←F
    ∘-assoc (ℕ←F {y} h₀) (F←F {w} {x} g₀) (ℕ←F f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- ℕ←F F←F F←ℕ
    ∘-assoc (ℕ←F {y} h₀) (F←F {w} {x} g₀) (F←ℕ {v} f₀)  with pairwiseEq v w x y
    ... | yes (p , q) =  trans (cong (ℕ←F h₀ ←_) (isHom-FFℕ g₀ f₀ p))
            (trans (isHom-ℕFℕ h₀ (g₀ ∘ subst Fin p ∘ f₀) q)
                   (sym (trans (cong (_← F←ℕ f₀) (isHom-ℕFF h₀ g₀ q))
                               (isHom-ℕFℕ (h₀ ∘ subst Fin q ∘ g₀) f₀ p))))
    ... | no contra = ⊥-elim (contra impossible)
      where
        impossible : (v ≡ w) × (x ≡ y)
        impossible = {!!} -- Don't fill a hole that can't be reached.
    -- ℕ←F F←F F←F
    ∘-assoc (ℕ←F {y} h₀) (F←F {w} {x} g₀) (F←F {u} {v} f₀) with pairwiseEq v w x y
    ... | yes (p , q) =  trans (cong (ℕ←F h₀ ←_) (isHom-FFF g₀ f₀ p))
            (trans (isHom-ℕFF h₀ (g₀ ∘ subst Fin p ∘ f₀) q)
                   (sym (trans (cong (_← F←F f₀) (isHom-ℕFF h₀ g₀ q))
                               (isHom-ℕFF (h₀ ∘ subst Fin q ∘ g₀) f₀ p))))
    ... | no contra = ⊥-elim (contra impossible)
      where
        impossible : (v ≡ w) × (x ≡ y)
        impossible = {!!} -- Don't fill a hole that can't be reached.

    ---F←ℕ--------------
    -- F←ℕ ▦ _
    ∘-assoc (F←ℕ h₀) ▦ _ = refl

    -- F←ℕ ℕ←ℕ ▦
    ∘-assoc (F←ℕ h₀) (ℕ←ℕ g₀) ▦ = refl
    -- F←ℕ ℕ←ℕ ℕ←ℕ
    ∘-assoc (F←ℕ h₀) (ℕ←ℕ g₀) (ℕ←ℕ f₀) = refl
    -- F←ℕ ℕ←ℕ ℕ←F
    ∘-assoc (F←ℕ h₀) (ℕ←ℕ g₀) (ℕ←F f₀) = refl
    -- F←ℕ ℕ←ℕ F←ℕ
    ∘-assoc (F←ℕ h₀) (ℕ←ℕ g₀) (F←ℕ f₀) = refl
    -- F←ℕ ℕ←ℕ F←F
    ∘-assoc (F←ℕ h₀) (ℕ←ℕ g₀) (F←F f₀) = refl

    -- F←ℕ ℕ←F ▦
    ∘-assoc (F←ℕ h₀) (ℕ←F g₀) ▦ = refl
    -- F←ℕ ℕ←F ℕ←ℕ
    ∘-assoc (F←ℕ h₀) (ℕ←F g₀) (ℕ←ℕ f₀) = refl
    -- F←ℕ ℕ←F ℕ←F
    ∘-assoc (F←ℕ h₀) (ℕ←F g₀) (ℕ←F f₀) = refl
    -- F←ℕ ℕ←F F←ℕ
    ∘-assoc (F←ℕ h₀) (ℕ←F {w} g₀) (F←ℕ {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl
    -- F←ℕ ℕ←F F←F
    ∘-assoc (F←ℕ h₀) (ℕ←F {w} g₀) (F←F {u} {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl

    -- F←ℕ F←ℕ ▦
    ∘-assoc (F←ℕ h₀) (F←ℕ g₀) ▦ = refl
    -- F←ℕ F←ℕ ℕ←ℕ
    ∘-assoc (F←ℕ h₀) (F←ℕ g₀) (ℕ←ℕ f₀) = refl
    -- F←ℕ F←ℕ ℕ←F
    ∘-assoc (F←ℕ h₀) (F←ℕ g₀) (ℕ←F f₀) = refl
    -- F←ℕ F←ℕ F←ℕ 
    ∘-assoc (F←ℕ h₀) (F←ℕ g₀) (F←ℕ f₀) = refl
    -- F←ℕ F←ℕ F←F
    ∘-assoc (F←ℕ h₀) (F←ℕ g₀) (F←F f₀) = refl
    
    -- All failed
    -- F←ℕ F←F ▦
    ∘-assoc (F←ℕ h₀) (F←F g₀) ▦ = refl
    -- F←ℕ F←F ℕ←ℕ  
    ∘-assoc (F←ℕ h₀) (F←F g₀) (ℕ←ℕ f₀) = refl
    -- F←ℕ F←F ℕ←F
    ∘-assoc (F←ℕ h₀) (F←F g₀) (ℕ←F f₀) = refl
    -- F←ℕ F←F F←ℕ
    ∘-assoc (F←ℕ h₀) (F←F {w} g₀) (F←ℕ {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl
    -- F←ℕ F←F F←F
    ∘-assoc (F←ℕ h₀) (F←F {w} g₀) (F←F {u} {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl
    
    ---F←F--------------
    -- F←F ▦ _
    ∘-assoc (F←F {y} h₀) ▦ _ = refl

    -- F←F ℕ←ℕ ▦. -- All fail at h g 
    ∘-assoc (F←F {y} h₀) (ℕ←ℕ g₀) ▦ = refl
    -- F←F ℕ←ℕ ℕ←ℕ
    ∘-assoc (F←F {y} h₀) (ℕ←ℕ g₀) (ℕ←ℕ f₀) = refl
    -- F←F ℕ←ℕ ℕ←F
    ∘-assoc (F←F {y} h₀) (ℕ←ℕ g₀) (ℕ←F f₀) = refl
    -- F←F ℕ←ℕ F←ℕ
    ∘-assoc (F←F {y} h₀) (ℕ←ℕ g₀) (F←ℕ f₀) = refl
    -- F←F ℕ←ℕ F←F
    ∘-assoc (F←F {y} h₀) (ℕ←ℕ g₀) (F←F f₀) = refl


    -- F←F ℕ←F ▦
    ∘-assoc (F←F {y} h₀) (ℕ←F g₀) ▦ = refl
    -- F←F ℕ←F ℕ←ℕ
    ∘-assoc (F←F {y} h₀) (ℕ←F g₀) (ℕ←ℕ f₀) = refl
    -- F←F ℕ←F ℕ←F
    ∘-assoc (F←F {y} h₀) (ℕ←F g₀) (ℕ←F f₀) = refl
    -- F←F ℕ←F F←ℕ
    ∘-assoc (F←F {y} h₀) (ℕ←F {w} g₀) (F←ℕ {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl
    -- F←F ℕ←F F←F
    ∘-assoc (F←F {y} h₀) (ℕ←F {w} g₀) (F←F {u} {v} f₀) with v ≟ w
    ... | yes p = refl
    ... | no ¬p = refl


    -- F←F F←ℕ ▦
    ∘-assoc (F←F {y} h₀) (F←ℕ {x} g₀) ▦ with x ≟ y  
    ... | yes q = refl
    ... | no ¬q = refl
    -- F←F F←ℕ ℕ←ℕ
    ∘-assoc (F←F {y} h₀) (F←ℕ {x} g₀) (ℕ←ℕ f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- F←F F←ℕ ℕ←F
    ∘-assoc (F←F {y} h₀) (F←ℕ {x} g₀) (ℕ←F f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- F←F F←ℕ F←ℕ
    ∘-assoc (F←F {y} h₀) (F←ℕ {x} g₀) (F←ℕ {v} f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- F←F F←ℕ F←F
    ∘-assoc (F←F {y} h₀) (F←ℕ {x} g₀) (F←F {u} {v} f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl


    -- F←F F←F ▦
    ∘-assoc (F←F {y} {z} h₀) (F←F {w} {x} g₀) ▦ with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- F←F F←F ℕ←ℕ
    ∘-assoc (F←F {y} {z} h₀) (F←F {w} {x} g₀) (ℕ←ℕ f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- F←F F←F ℕ←F
    ∘-assoc (F←F {y} {z} h₀) (F←F {w} {x} g₀) (ℕ←F f₀) with x ≟ y
    ... | yes q = refl
    ... | no ¬q = refl
    -- F←F F←F F←ℕ
    ∘-assoc (F←F {y} {z} h₀) (F←F {w} {x} g₀) (F←ℕ {v} f₀) with pairwiseEq v w x y
    ... | yes (p , q) = trans (cong (F←F h₀ ←_) (isHom-FFℕ g₀ f₀ p))
            (trans (isHom-FFℕ h₀ (g₀ ∘ subst Fin p ∘ f₀) q)
                   (sym (trans (cong (_← F←ℕ f₀) (isHom-FFF h₀ g₀ q))
                               (isHom-FFℕ (h₀ ∘ subst Fin q ∘ g₀) f₀ p))))
    ... | no contra = ⊥-elim (contra impossible)
      where
        impossible : (v ≡ w) × (x ≡ y)
        impossible = {!!} -- Don't fill a hole that can't be reached
    -- F←F←F←F
    ∘-assoc (F←F {y} {z} h₀) (F←F {w} {x} g₀) (F←F {u} {v} f₀) with pairwiseEq v w x y
    ... | yes (p , q) =  trans (cong (F←F h₀ ←_) (isHom-FFF g₀ f₀ p))
            (trans (isHom-FFF h₀ (g₀ ∘ subst Fin p ∘ f₀) q)
                   (sym (trans (cong (_← F←F f₀) (isHom-FFF h₀ g₀ q))
                               (isHom-FFF (h₀ ∘ subst Fin q ∘ g₀) f₀ p))))
    ... | no contra = ⊥-elim (contra impossible)
      where
        impossible : (v ≡ w) × (x ≡ y)
        impossible = {!!} -- Don't fill a hole that can't be reached

