open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Set)
open import Data.Empty using (⊥-elim)

open import Data.Nat using (ℕ; _≟_)
open import Data.Fin using (Fin)


open import Relation.Binary.PropositionalEquality using (refl; subst; _≡_; cong; sym; trans; subst-∘)
open import Relation.Nullary using (yes; no; Dec)
-- open import Axiom.Extensionality.Propositional using (Extensionality)

open import Function using (_∘_; id)


{-- A minimal countable constructive set theory. --}
module Countable.Sets where


    data ConSet : Set where 
        N : ConSet
        F : (n : ℕ) → ConSet
    
    asSet : ConSet → Set
    asSet N = ℕ
    asSet (F n) = Fin n

    -- Define infix operators for readability
    -- Valence 1 operators have higher precedent than composition
    infix 99 _◄
    infix 99 ◄_
    infix 50 _←_
    
    -----------------------------------------------------
    --- Carrier: Fin n and Nat                        ---
    -----------------------------------------------------

    {-- Carrier: Functions between the allowed types --}
    data ConFun : Set where
        F←F : ∀ {m n : ℕ} → (f : (Fin m) → (Fin n)) → ConFun
        F←ℕ : ∀ {n : ℕ} → (f : ℕ → (Fin n)) → ConFun
        ℕ←F : ∀ {n : ℕ} → (f : (Fin n) → ℕ) → ConFun
        ℕ←ℕ : (f : ℕ → ℕ) → ConFun
        ▦ : ConFun

    -----------------------------------------------------
    --- Make a micro universe tower.                  ---
    -----------------------------------------------------
    -- {-- Universe levels --}
    -- data Types : Set where 
    --     ConSets : Types
    --     -- ConFuns : Types
    --     Sets : Types

    -- asUniverse : Types → Set₁
    -- asUniverse Sets = Set
    -- asUniverse ConSets = Lift lzero ConSet
    -- asUniverse ConFuns = Lift lzero ConFun

    -----------------------------------------------------
    --- Operators for composition and identity        ---
    -----------------------------------------------------
    {-- In / Out operators --}
    _◄ : ConFun → ConFun
    _◄ (F←F {a} {b} f) = F←F {a} (λ x → x)
    _◄ (F←ℕ {b} f)     = ℕ←ℕ (λ x → x)
    _◄ (ℕ←F {a} f)     = F←F {a} (λ x → x)
    _◄ (ℕ←ℕ f)         = ℕ←ℕ (λ x → x)
    _◄ (▦)             = ▦

    {-- In / Out operators --}
    ◄_ : ConFun → ConFun
    ◄_ (F←F {a} {b} f) = F←F {b} (λ x → x)
    ◄_ (F←ℕ {b} f)     = F←F {b} (λ x → x)
    ◄_ (ℕ←F {a} f)     = ℕ←ℕ (λ x → x)
    ◄_ (ℕ←ℕ f)         = ℕ←ℕ (λ x → x)
    ◄_ (▦)             = ▦

    {-- Case splitting on the types of functions. --}
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

    {-- Composition rules --} 


    {-- Show ConFun constructors are a homomorphism _←_ to _∘_ --}
    isHom-ℕℕℕ : (g f : ℕ → ℕ) 
              → ( (ℕ←ℕ g) ← (ℕ←ℕ f) ≡ (ℕ←ℕ (g ∘ f)) )
    isHom-ℕℕℕ g f = refl
    isHom-ℕℕF : ∀ {a : ℕ} (g : ℕ → ℕ) (f : Fin a → ℕ) 
              → ( (ℕ←ℕ g) ← (ℕ←F {a} f) ≡ (ℕ←F {a} (g ∘ f)) )
    isHom-ℕℕF {a} g f = refl

    -- Transport along different proofs b ≡ c is pointwise equal for Fin
    -- This requires UIP (Uniqueness of Identity Proofs)
    postulate
        transport-uniq-Fin : ∀ {b c : ℕ} (p q : b ≡ c) (x : Fin b)
                           → subst Fin q x ≡ subst Fin p x

    -- Function extensionality assumption 
    -- i.e. tell Agda what we mean "equal functions" to be. 
    postulate 
        funExt : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

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

