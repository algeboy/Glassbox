open import Agda.Primitive using (Level; lsuc; lzero; _⊔_)
open import Level using (Lift; lift)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup)
open import Data.List as List using (List; []; _∷_; length)
open import Data.Fin using (Fin; zero; suc; #_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_)

-- Import the necessary definitions from West module
open import West using (OpSig; Signature; AlgeStruct; East; Subset; _∈ₗ_; TotalEquation; Formula; op; var; Equation; toExistential; restrictToTotal; evalFormula)
open import CategoryExample using (compositionSig; _◄; ◄_; _·_)

module Hom where

-- -----------------------------------------------------------------------------
-- Homomorphism Property
-- -----------------------------------------------------------------------------

-- The homomorphism property: f(ω(a₁,...,aₙ)) ≡ ω(f(a₁),...,f(aₙ))
HomProp : ∀ {ℓ : Level} {sig : Signature {ℓ}} {A B : Set ℓ}
  → (algA : AlgeStruct {ℓ} {sig} A)
  → (algB : AlgeStruct {ℓ} {sig} B)
  → (f : A → B)
  → Set ℓ
HomProp {ℓ} {sig} {A} {B} algA algB f =
  (i : Fin (List.length sig)) →
  (args : Vec A (OpSig.valence (List.lookup sig i))) →
  f (AlgeStruct.ops algA i args) ≡ AlgeStruct.ops algB i (Vec.map f args)

-- -----------------------------------------------------------------------------
-- Homomorphism Data Type
-- -----------------------------------------------------------------------------

data Hom {ℓ : Level} {sig : Signature {ℓ}} : Set (lsuc ℓ) where
  makeHom : {A B : Set ℓ}
          → (algA : AlgeStruct {ℓ} {sig} A)
          → (algB : AlgeStruct {ℓ} {sig} B)
          → (f : A → B)
          → (isHom : HomProp {ℓ} {sig} algA algB f)
          → Hom {ℓ} {sig}

-- -----------------------------------------------------------------------------
-- Homomorphism Accessor Functions
-- -----------------------------------------------------------------------------

-- Extract the source algebra
source : ∀ {ℓ : Level} {sig : Signature {ℓ}} → Hom {ℓ} {sig} → ∃ (AlgeStruct {ℓ} {sig})
source (makeHom {A} algA algB f isHom) = A , algA

-- Extract the target algebra
target : ∀ {ℓ : Level} {sig : Signature {ℓ}} → Hom {ℓ} {sig} → ∃ (AlgeStruct {ℓ} {sig})
target (makeHom {B = B} algA algB f isHom) = B , algB

-- Extract the underlying function
homFun : ∀ {ℓ : Level} {sig : Signature {ℓ}} → (h : Hom {ℓ} {sig}) →
  let (A , algA) = source h
      (B , algB) = target h
  in A → B
homFun (makeHom algA algB f isHom) = f

-- Extract the homomorphism property proof
-- Not sure if needed
homProperty : ∀ {ℓ : Level} {sig : Signature {ℓ}} → (h : Hom {ℓ} {sig}) →
  let (A , algA) = source h
      (B , algB) = target h
      f = homFun h
  in HomProp algA algB f
homProperty (makeHom algA algB f isHom) = isHom

-- -----------------------------------------------------------------------------
-- Homomorphism Composition (when types allow)
-- -----------------------------------------------------------------------------

-- Check if two homomorphisms are composable and compose them
-- For simplicity, we assume the user provides composable homomorphisms
-- In practice, this would need more sophisticated type checking
composeHom : ∀ {ℓ : Level} {sig : Signature {ℓ}} 
           → (h₁ h₂ : Hom {ℓ} {sig}) 
           → Maybe (Hom {ℓ} {sig})
composeHom (makeHom {A = Y} {B = Z} algY algZ f isHomF) (makeHom {A = X} {B = Y} algX algY g isHomG) = 
  -- If the types match (Y = Y), we can compose
  just (makeHom algX algZ (λ x → f (g x)) composedHomProp)
  where
    composedHomProp : HomProp algX algZ (λ x → f (g x))
    composedHomProp i args = 
      begin
        f (g (AlgeStruct.ops algX i args))
      ≡⟨ cong f (isHomG i args) ⟩
        f (AlgeStruct.ops algY i (Vec.map g args))
      ≡⟨ isHomF i (Vec.map g args) ⟩
        AlgeStruct.ops algZ i (Vec.map f (Vec.map g args))
      ≡⟨ cong (AlgeStruct.ops algZ i) (mapCompose args) ⟩
        AlgeStruct.ops algZ i (Vec.map (λ x → f (g x)) args)
      ∎
      where
        mapCompose : ∀ {n : ℕ} (v : Vec X n) → Vec.map f (Vec.map g v) ≡ Vec.map (λ x → f (g x)) v
        mapCompose [] = refl
        mapCompose (x ∷ xs) = cong (f (g x) ∷_) (mapCompose xs)

composeHom _ _ = nothing  -- Default case: not composable


idHom : ∀ {ℓ : Level} {sig : Signature {ℓ}} {A : Set ℓ}
      → (alg : AlgeStruct {ℓ} {sig} A)
      → Hom {ℓ} {sig}
idHom {ℓ} {sig} {A} alg = makeHom alg alg (λ x → x) idHomProp
  where
    idHomProp : HomProp alg alg (λ x → x)
    idHomProp i args = cong (AlgeStruct.ops alg i) (sym (mapId args))
      where
        -- We need to prove that Vec.map id ≡ id for vectors
        mapId : ∀ {n : ℕ} (v : Vec A n) → Vec.map (λ x → x) v ≡ v
        mapId [] = refl
        mapId (x ∷ xs) = cong (x ∷_) (mapId xs)
