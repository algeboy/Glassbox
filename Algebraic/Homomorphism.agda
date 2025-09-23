
open import Agda.Primitive using (Set)
open import Data.Empty using (⊥-elim)

open import Data.Nat using (ℕ; _≟_)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Vec using (Vec; map)
open import Data.Vec.Properties using (map-id; map-cong)

open import Function using (_|>_)
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; subst; sym; trans; cong )
open import Relation.Binary.PropositionalEquality.Properties using ( subst-sym-subst )
open import Relation.Nullary using (yes; no)
open import Axiom.Extensionality.Propositional using ( Extensionality )

open import Algebraic.Signatures
open import Countable.Sets
open import Algebraic.Structures

{-- A minimal countable constructive set theory. --}
module Algebraic.Homomorphism where

    {-- Homomorphisms as a subcategory --}

    data Hom {sig : Signature} : Set where
        null : (cf : ConFun) → (p : cf ≡ ▦) → Hom
        
        NN : (cf : ConFun) → (f : ℕ → ℕ) → (p : cf ≡ ℕ←ℕ f) → (A B : Structure {sig}) → 
             (pA : proj₁ A ≡ N) → (pB : proj₁ B ≡ N) →
             ((i : Fin (nOps sig)) →
                 (x : Vec (asSet (proj₁ A)) (proj₂ (proj₂ sig i))) →
                     subst asSet (sym pB) (f (subst asSet pA (proj₂ A i x))) ≡ 
                     proj₂ B i (map (λ y → subst asSet (sym pB) (f (subst asSet pA y))) x)
             ) → Hom

        FF : (cf : ConFun) → {a b : ℕ} → (f : Fin a → Fin b) → (p : cf ≡ F←F {a} {b} f) → (A B : Structure {sig}) → 
             (pA : proj₁ A ≡ F a) → (pB : proj₁ B ≡ F b) →
             ((i : Fin (nOps sig)) →
                 (x : Vec (asSet (proj₁ A)) (proj₂ (proj₂ sig i))) →
                     subst asSet (sym pB) (f (subst asSet pA (proj₂ A i x))) ≡ 
                     proj₂ B i (map (λ y → subst asSet (sym pB) (f (subst asSet pA y))) x)
             ) → Hom
        
        FN : (cf : ConFun) → {a : ℕ} → (f : ℕ → Fin a) → (p : cf ≡ F←ℕ {a} f) → (A B : Structure {sig}) → 
             (pA : proj₁ A ≡ N) → (pB : proj₁ B ≡ F a) →
             ((i : Fin (nOps sig)) →
                 (x : Vec (asSet (proj₁ A)) (proj₂ (proj₂ sig i))) →
                     subst asSet (sym pB) (f (subst asSet pA (proj₂ A i x))) ≡ 
                     proj₂ B i (map (λ y → subst asSet (sym pB) (f (subst asSet pA y))) x)
             ) → Hom
        
        NF : (cf : ConFun) → {a : ℕ} → (f : Fin a → ℕ) → (p : cf ≡ ℕ←F {a} f) → (A B : Structure {sig}) → 
             (pA : proj₁ A ≡ F a) → (pB : proj₁ B ≡ N) →
             ((i : Fin (nOps sig)) →
                 (x : Vec (asSet (proj₁ A)) (proj₂ (proj₂ sig i))) →
                     subst asSet (sym pB) (f (subst asSet pA (proj₂ A i x))) ≡ 
                     proj₂ B i (map (λ y → subst asSet (sym pB) (f (subst asSet pA y))) x)
             ) → Hom
        



    {-- source of Homomorphism returns identity on domain --}
    _◄◄ : ∀ {sig : Signature} → Hom {sig} → Hom {sig}
    _◄◄  {sig} (null cf p) = null (cf ◄) (trans (cong _◄ p) refl)
    _◄◄  {sig} (NN cf f p A B pA pB pf) = NN (cf ◄) (λ x → x) (trans (cong _◄ p) refl) A A pA pA (λ i x → {!!})
    _◄◄  {sig} (FF cf f p A B pA pB pf) = FF (cf ◄) (λ x → x) (trans (cong _◄ p) refl) A A pA pA (λ i x → {!!})
    _◄◄  {sig} (FN cf f p A B pA pB pf) = NN (cf ◄) (λ x → x) (trans (cong _◄ p) refl) A A pA pA (λ i x → {!!})
    _◄◄  {sig} (NF cf f p A B pA pB pf) = FF (cf ◄) (λ x → x) (trans (cong _◄ p) refl) A A pA pA (λ i x → {!!})

    {-- target of Homomorphism returns identity on codomain --}
    ◄◄_ : ∀ {sig : Signature} → Hom {sig} → Hom {sig}
    ◄◄_ {sig} (null cf p) = null (◄ cf) (trans (cong (◄_) p) refl)
    ◄◄_ {sig} (NN cf f p A B pA pB pf) = NN (◄ cf) (λ x → x) (trans (cong (◄_) p) refl) B B pB pB (λ i x → {!!})
    ◄◄_ {sig} (FF cf f p A B pA pB pf) = FF (◄ cf) (λ x → x) (trans (cong (◄_) p) refl) B B pB pB (λ i x → {!!})
    ◄◄_ {sig} (FN cf f p A B pA pB pf) = FF (◄ cf) (λ x → x) (trans (cong (◄_) p) refl) B B pB pB (λ i x → {!!})
    ◄◄_ {sig} (NF cf f p A B pA pB pf) = NN (◄ cf) (λ x → x) (trans (cong (◄_) p) refl) B B pB pB (λ i x → {!!})

    {-- Composition of homomorphisms --}
    _∘_ : ∀ {sig : Signature} → Hom {sig} → Hom {sig} → Hom {sig}
    -- null cases
    _∘_ {sig} (null cf₁ p₁) (null cf₂ p₂) = null ▦ refl
    _∘_ {sig} (null cf₁ p₁) (NN cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (null cf₁ p₁) (FF cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (null cf₁ p₁) (FN cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (null cf₁ p₁) (NF cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    
    -- NN cases
    _∘_ {sig} (NN cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (null cf₂ p₂) = null ▦ refl
    _∘_ {sig} (NN cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (NN cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) 
        = NN (cf₁ ← cf₂) (λ x → f₁ (f₂ x)) {!!} A₂ B₁ pA₂ pB₁ (λ i x → {!!})
    _∘_ {sig} (NN cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (FF cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (NN cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (FN cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (NN cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (NF cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) 
        = NF (cf₁ ← cf₂) (λ x → f₁ (f₂ x)) {!!} A₂ B₁ pA₂ pB₁ (λ i x → {!!})
    
    -- FF cases  
    _∘_ {sig} (FF cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (null cf₂ p₂) = null ▦ refl
    _∘_ {sig} (FF cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (NN cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} 
        (FF cf₁ {a₁} {b₁} f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) 
        (FF cf₂ {a₂} {b₂} f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) 
        with b₂ ≟ a₁
    _∘_ {sig} (FF cf₁ {a₁} {b₁} f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (FF cf₂ {a₂} {.a₁} f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) | yes refl = 
        FF (cf₁ ← cf₂) (λ x → f₁ (f₂ x)) {!!} A₂ B₁ pA₂ pB₁ (λ i x → {!!})
    _∘_ {sig} (FF cf₁ {a₁} {b₁} f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (FF cf₂ {a₂} {b₂} f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) | no ¬eq = 
        null ▦ refl
    _∘_ {sig} (FF cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (FN cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (FF cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (NF cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    
    -- FN cases
    _∘_ {sig} (FN cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (null cf₂ p₂) = null ▦ refl
    _∘_ {sig} (FN cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (NN cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) 
        = FN (cf₁ ← cf₂) (λ x → f₁ (f₂ x)) {!!} A₂ B₁ pA₂ pB₁ (λ i x → {!!})
    _∘_ {sig} (FN cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (FF cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (FN cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (FN cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (FN cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (NF cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) 
        = FF (cf₁ ← cf₂) (λ x → f₁ (f₂ x)) {!!} A₂ B₁ pA₂ pB₁ (λ i x → {!!})
    
    -- NF cases
    _∘_ {sig} (NF cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (null cf₂ p₂) = null ▦ refl
    _∘_ {sig} (NF cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (NN cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (NF cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (FF cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (NF cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (FN cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl
    _∘_ {sig} (NF cf₁ f₁ p₁ A₁ B₁ pA₁ pB₁ pf₁) (NF cf₂ f₂ p₂ A₂ B₂ pA₂ pB₂ pf₂) = null ▦ refl

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
        test-hom : Hom {testSig}
        test-hom = NN (ℕ←ℕ idFun) idFun refl ℕ-struct ℕ-struct2 refl refl 
                   (λ i → λ { (x ∷ y ∷ []) → refl })
