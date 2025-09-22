open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Set)
open import Data.Empty using (⊥-elim)

open import Data.Nat using (ℕ; _≟_)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality using (refl; subst; _≡_; cong; sym; trans; subst-∘)
open import Relation.Nullary using (yes; no; Dec)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import Function using (_∘_; id)


{-- A minimal countable constructive set theory. --}
module Countable.SmallFunctions where

    postulate funExt : Extensionality lzero lzero
    -- Define infix operators for readability
    -- Valence 1 operators have higher precedent than composition
    infix 99 _◄
    infix 99 ◄_
    infix 50 _←_

    data SmallFun : Set where
        noFun : SmallFun
        makeFun : (f : ℕ → ℕ) → (lMax rMax : Maybe ℕ) → SmallFun

    -- Helper function to compare Maybe ℕ values
    -- Returns true if both are nothing, or both are just n and just m where n ≡ m
    compareMaybeℕ : (m n : Maybe ℕ) → Dec (m ≡ n)
    compareMaybeℕ nothing nothing = yes refl
    compareMaybeℕ (just n) (just m) with n ≟ m
    ... | yes p = yes (cong just p)
    ... | no ¬p = no (λ q → ¬p (helper q))
      where
        helper : just n ≡ just m → n ≡ m
        helper refl = refl
    compareMaybeℕ nothing (just m) = no (λ ())
    compareMaybeℕ (just n) nothing = no (λ ())

    _←_ : SmallFun → SmallFun → SmallFun
    _←_ noFun g = noFun
    _←_ f noFun = noFun
    _←_ (makeFun f lMaxf rMaxf) (makeFun g lMaxg rMaxg) with compareMaybeℕ rMaxf lMaxg
    ... | yes p = makeFun (f ∘ g) lMaxf rMaxg
    ... | no ¬p = noFun

    _◄ : SmallFun → SmallFun
    _◄ noFun = noFun
    _◄ (makeFun f lMax rMax) = makeFun (λ x → x) rMax rMax

    ◄_ : SmallFun → SmallFun
    ◄_ noFun = noFun
    ◄_ (makeFun f lMax rMax) = makeFun (λ x → x) lMax lMax

    {-- target of source = source --}
    tgtSrcProof : (f : SmallFun) → (◄ (f ◄) ≡ (f ◄))
    tgtSrcProof noFun = refl
    tgtSrcProof (makeFun f lMax rMax) = refl

    {-- source of target = target --}
    srcTgtProof : (f : SmallFun) → ((◄ f) ◄ ≡ (◄ f))
    srcTgtProof noFun = refl
    srcTgtProof (makeFun f lMax rMax) = refl

    -- Helper lemma: identity composed with any function equals that function
    id-comp : (f : ℕ → ℕ) → ((λ x → x) ∘ f) ≡ f
    id-comp f = funExt (λ x → refl)

    -- {-- target of origin = origin --}
    tgtOrgProof : (f : SmallFun) → ((◄ f) ← f ≡ f)
    tgtOrgProof noFun = refl
    tgtOrgProof (makeFun f lMax rMax) = cong (λ g → makeFun g lMax rMax) (id-comp f)

    -- {-- composition is associative --}
    -- compAssoc : (f g h : SmallFun) → ((f ← g) ← h ≡ f ← (g ← h))
    -- compAssoc noFun g h = refl
    -- compAssoc (makeFun f lMaxf rMaxf) noFun h = refl
    -- compAssoc (makeFun f lMaxf rMaxf) (makeFun g lMaxg rMaxg) noFun 
    --     with compareMaybeℕ rMaxf lMaxg
    -- ... | yes p = refl
    -- ... | no ¬p = refl
    -- compAssoc (makeFun f lMaxf rMaxf) (makeFun g lMaxg rMaxg) (makeFun h lMaxh rMaxh) 
    --     with compareMaybeℕ rMaxf lMaxg | compareMaybeℕ rMaxg lMaxh 
    -- ... | yes p | yes q = {!!}
    -- ... | yes p | no ¬q = {!!}
    -- ... | no ¬p | yes q = {!!}
    -- ... | no ¬p | no ¬q = {!!}

