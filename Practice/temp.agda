
open import Data.Nat using (ℕ; _≟_)
open import Data.Fin using (Fin)

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl; subst; _≡_; cong; sym; trans; subst-∘)
open import Relation.Nullary using (yes; no; Dec)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import Function using (_∘_; id)


open import ConSet 

{-- A minimal countable constructive set category. --}
module ConSetCat where

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

    {-- Generic associativity of partial composition --}
    ∘-assoc : ∀ {A B C D : Set} {h : C → D} {g : B → C} {f : A → B} 
            → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f) 
    ∘-assoc = refl

    leftLiftAsc-FFFF : ∀ {u w y z : ℕ}
                (h₀ : Fin y → Fin z)
                (g₀ : Fin w → Fin y)
                (f₀ : Fin u → Fin w)
                 → ((F←F {y} {z} h₀ ← (F←F {w} {y} g₀ ← F←F {u} {w} f₀)) 
                 ≡ F←F {u} {z} (h₀ ∘ (g₀ ∘ f₀)))
    leftLiftAsc-FFFF h₀ g₀ f₀ = 
      trans (cong (λ x → F←F h₀ ← x) (isHom-FFF g₀ f₀ refl))
            (isHom-FFF h₀ (g₀ ∘ f₀) refl)

    rightLiftAsc-FFFF : ∀ (u w y z : ℕ)
                (h₀ : Fin y → Fin z)
                (g₀ : Fin w → Fin y)
                (f₀ : Fin u → Fin w)
                 → (((F←F {y} {z} h₀ ← F←F {w} {y} g₀) ← F←F {u} {w} f₀)) 
                 ≡ F←F {u} {z} ((h₀ ∘ g₀) ∘ f₀)
    rightLiftAsc-FFFF u w y z h₀ g₀ f₀ = 
      trans (cong (λ x → x ← F←F {u} {w} f₀) (isHom-FFF {w} {y} {y} {z} h₀ g₀ refl))
            (isHom-FFF {u} {w} {w} {z} (h₀ ∘ g₀) f₀ refl)

    babyStep1 : ∀ (u v w y x z : ℕ)
               (h₀ : Fin y → Fin z)
               (g₀ : Fin w → Fin x)
               (f₀ : Fin u → Fin v)
               → (p1 : v ≡ w)
               → (p2 : x ≡ y)
               → (F←F {u} {z} ((h₀ ∘ (subst (λ T → Fin w → Fin T) p2 g₀)) ∘ (subst (λ S → Fin u → Fin S) p1 f₀)) 
                  ≡ F←F {u} {z} (h₀ ∘ ((subst (λ T → Fin w → Fin T) p2 g₀) ∘ (subst (λ S → Fin u → Fin S) p1 f₀))))
    babyStep1 u v w y x z h₀ g₀ f₀ p1 p2 = 
            cong (λ q → F←F {u} {z} q) 
              (∘-assoc {A = Fin u} {B = Fin w} {C = Fin y} {D = Fin z} 
                       {h = h₀} 
                       {g = subst (λ T → Fin w → Fin T) p2 g₀} 
                       {f = subst (λ S → Fin u → Fin S) p1 f₀})
