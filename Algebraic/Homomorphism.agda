
open import Agda.Primitive using (Set)
open import Data.Empty using (⊥-elim)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Vec using (Vec; map)
open import Data.Vec.Properties using (map-id)

open import Function using (_|>_)
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; subst; sym; trans )
open import Relation.Binary.PropositionalEquality.Properties using ( subst-sym-subst )
open import Axiom.Extensionality.Propositional using ( Extensionality )

open import Algebraic.Signatures
open import Countable.Sets
open import Algebraic.Structures

{-- A minimal countable constructive set theory. --}
module Algebraic.Homomorphism where

    -- Identity functions for different ConFun types
    id-fun : ConFun → ConFun
    id-fun ▦ = ▦
    id-fun (ℕ←ℕ f) = ℕ←ℕ (λ x → x)
    id-fun (F←F {a} {b} f) = F←F {a} {a} (λ x → x)
    id-fun (F←ℕ {a} f) = ℕ←ℕ (λ x → x)
    id-fun (ℕ←F {a} f) = F←F {a} {a} (λ x → x)

    {-- Homomorphisms as a subcategory --}

    data Hom {sig : Signature} : ConFun → Set where
        null : Hom ▦
        NN : (f : ℕ → ℕ) → (A B : Structure {sig}) → 
             (pA : proj₁ A ≡ N) → (pB : proj₁ B ≡ N) →
             ((i : Fin (nOps sig)) →
                 (x : Vec (asSet (proj₁ A)) (proj₂ (proj₂ sig i))) →
                     subst asSet (sym pB) (f (subst asSet pA (proj₂ A i x))) ≡ 
                     proj₂ B i (map (λ y → subst asSet (sym pB) (f (subst asSet pA y))) x)
             ) → Hom (ℕ←ℕ f)

        FF : {a b : ℕ} → (f : Fin a → Fin b) → (A B : Structure {sig}) → 
             (pA : proj₁ A ≡ F a) → (pB : proj₁ B ≡ F b) →
             ((i : Fin (nOps sig)) →
                 (x : Vec (asSet (proj₁ A)) (proj₂ (proj₂ sig i))) →
                     subst asSet (sym pB) (f (subst asSet pA (proj₂ A i x))) ≡ 
                     proj₂ B i (map (λ y → subst asSet (sym pB) (f (subst asSet pA y))) x)
             ) → Hom (F←F {a} {b} f)
        
        FN : {a : ℕ} → (f : ℕ → Fin a) → (A B : Structure {sig}) → 
             (pA : proj₁ A ≡ N) → (pB : proj₁ B ≡ F a) →
             ((i : Fin (nOps sig)) →
                 (x : Vec (asSet (proj₁ A)) (proj₂ (proj₂ sig i))) →
                     subst asSet (sym pB) (f (subst asSet pA (proj₂ A i x))) ≡ 
                     proj₂ B i (map (λ y → subst asSet (sym pB) (f (subst asSet pA y))) x)
             ) → Hom (F←ℕ {a} f)
        
        NF : {a : ℕ} → (f : Fin a → ℕ) → (A B : Structure {sig}) → 
             (pA : proj₁ A ≡ F a) → (pB : proj₁ B ≡ N) →
             ((i : Fin (nOps sig)) →
                 (x : Vec (asSet (proj₁ A)) (proj₂ (proj₂ sig i))) →
                     subst asSet (sym pB) (f (subst asSet pA (proj₂ A i x))) ≡ 
                     proj₂ B i (map (λ y → subst asSet (sym pB) (f (subst asSet pA y))) x)
             ) → Hom (ℕ←F {a} f)
        



    {-- source of Homomorphism returns identity on domain --}
    source : ∀ {sig : Signature} {f : ConFun} → Hom {sig} f → Hom {sig} (id-fun f)
    source {sig} null = null
    source {sig} (NN f A B pA pB pf) = NN (λ x → x) A A pA pA (λ i x → {!!})
    source {sig} (FF f A B pA pB pf) = FF (λ x → x) A A pA pA (λ i x → {!!})
    source {sig} (FN f A B pA pB pf) = {!!}
    source {sig} (NF f A B pA pB pf) = {!!}


    -- {-- target of Homomorphism returns identity on codomain --}
    -- target : ∀ {sig : Signature} {A B : Structure {sig}} → Homomorphism {sig} A B → Homomorphism {sig} B B
    -- target {sig} {A} {B} (f , pf) = idHom {sig} {B} 

    -- {-- Composition of homomorphisms --}
    -- _∘_ : ∀ {sig : Signature} {A B C : Structure {sig}} 
    --       → Homomorphism {sig} B C 
    --       → Homomorphism {sig} A B
    --       → Homomorphism {sig} A C
    -- _∘_ {sig} {A} {B} {C} (g , pfG) (f , pfF) = (g ← f , {!!})

    {-- Test Cases --}
    
    -- Test: Create a simple homomorphism between ℕ structures
    module Test where
        open import Data.Vec using ([]; _∷_)
        
        -- Simple signature with one binary operation
        testSig : Signature
        testSig = (1 , λ _ → ("+" , 2))
        
        -- ℕ structure for addition
        ℕ-struct : Structure {testSig}
        ℕ-struct = (N , λ _ → λ { (x ∷ y ∷ []) → x Data.Nat.+ y })
        
        -- Another ℕ structure (could be different operation, but same for test)
        ℕ-struct2 : Structure {testSig}
        ℕ-struct2 = (N , λ _ → λ { (x ∷ y ∷ []) → x Data.Nat.+ y })
        
        -- Identity function ℕ → ℕ
        idFun : ℕ → ℕ
        idFun x = x
        
        -- Test that we can construct a homomorphism
        test-hom : Hom {testSig} (ℕ←ℕ idFun)
        test-hom = NN idFun ℕ-struct ℕ-struct2 refl refl 
                   (λ i → λ { (x ∷ y ∷ []) → refl })
