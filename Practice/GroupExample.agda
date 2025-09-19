open import Agda.Primitive using (Level; lsuc; lzero; _⊔_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_; lookup; length)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import CategoryExample using (compositionSig; CompositionQuasiVariety)

open import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open Eq.≡-Reasoning      -- brings begin_, _≡⟨_⟩_, _≡⟨⟩_, _∎ into scope

-- Import our algebraic structures
open import Algebras
open import Equations

module GroupExample where

-- -----------------------------------------------------------------------------
-- Group Signature
-- -----------------------------------------------------------------------------

-- Group operations: multiplication (·), identity (e), and inverse (⁻¹)
groupSig : Signature {lzero}
groupSig = record { name = "mult" ; valence = 2 } ∷
           record { name = "id" ; valence = 0 } ∷  
           record { name = "inv" ; valence = 1 } ∷
           []

-- Define infix operators for readability
infix 6 _·_
infix 8 _⁻¹
infix 9 e

-- Define the infix operators using direct position indices
_·_ : Formula {lzero} {groupSig} (Fin 3) → Formula {lzero} {groupSig} (Fin 3) → Formula {lzero} {groupSig} (Fin 3)
_·_ t₁ t₂ = op (# 0) (t₁ ∷ t₂ ∷ [])

_⁻¹ : Formula {lzero} {groupSig} (Fin 3) → Formula {lzero} {groupSig} (Fin 3)
_⁻¹ t = op (# 2) (t ∷ [])

e : Formula {lzero} {groupSig} (Fin 3)
e = op (# 1) []

-- -----------------------------------------------------------------------------
-- Group Variety
-- -----------------------------------------------------------------------------

-- Variables for group laws
X : Set
X = Fin 3

x y z : X
x = # 0
y = # 1  
z = # 2

-- Convenient variable formulas for readability
g h k : Formula {lzero} {groupSig} X
g = var x
h = var y
k = var z

-- Group Axioms (unconditional equations, so n = 0)

-- Associativity: (x · y) · z = x · (y · z)
assocLaw : Equation {lzero} {groupSig} X
assocLaw = (g · h) · k , g · (h · k)

-- Left identity: e · x = x
leftIdLaw : Equation {lzero} {groupSig} X  
leftIdLaw = e · g , g

-- Right identity: x · e = x
rightIdLaw : Equation {lzero} {groupSig} X
rightIdLaw = g · e , g

-- Left inverse: x⁻¹ · x = e
leftInvLaw : Equation {lzero} {groupSig} X
leftInvLaw = (g ⁻¹) · g , e

-- Right inverse: x · x⁻¹ = e
rightInvLaw : Equation {lzero} {groupSig} X
rightInvLaw = g · (g ⁻¹) , e

-- Group Variety
GroupVariety : Variety {lzero} {groupSig} X
GroupVariety = laws (
    assocLaw ∷ 
    leftIdLaw ∷ 
    rightIdLaw ∷ 
    leftInvLaw ∷ 
    rightInvLaw ∷ 
    []
  )

-- -----------------------------------------------------------------------------
-- Group Type
-- -----------------------------------------------------------------------------

-- A Group is an algebraic structure that satisfies the group variety
record Group (A : Set) : Set₁ where
  field
    algebra : AlgeStruct {lzero} {groupSig} A
    isGroup : inVariety GroupVariety algebra

-- Convenient constructor for groups
mkGroup : (A : Set) → (alg : AlgeStruct {lzero} {groupSig} A) 
  → inVariety GroupVariety alg → Group A
mkGroup A alg proof = record { algebra = alg ; isGroup = proof }

-- Extract the underlying algebraic structure
getAlgebra : {A : Set} → Group A → AlgeStruct {lzero} {groupSig} A
getAlgebra grp = Group.algebra grp

-- Extract the group proof
getGroupProof : {A : Set} → (grp : Group A) → inVariety GroupVariety (Group.algebra grp)
getGroupProof grp = Group.isGroup grp

-- -----------------------------------------------------------------------------
-- Group Homomorphisms
-- -----------------------------------------------------------------------------

-- A group homomorphism is a function that preserves the group structure
record GroupHomomorphism {A B : Set} (G : Group A) (H : Group B) : Set where
  field
    map : A → B
    -- Preserve multiplication: f(x · y) = f(x) ·' f(y)
    preserveMult : (x y : A) → 
      let _·ᴳ_ = AlgeStruct.ops (Group.algebra G) (# 0)
          _·ᴴ_ = AlgeStruct.ops (Group.algebra H) (# 0)
      in map (_·ᴳ_ (x ∷ y ∷ [])) ≡ (_·ᴴ_ (map x ∷ map y ∷ []))
    -- Preserve identity: f(e) = e'
    preserveId : 
      let eᴳ = AlgeStruct.ops (Group.algebra G) (# 1) []
          eᴴ = AlgeStruct.ops (Group.algebra H) (# 1) []
      in map eᴳ ≡ eᴴ
    -- Preserve inverse: f(x⁻¹) = f(x)⁻¹
    preserveInv : (x : A) → 
      let invᴳ = AlgeStruct.ops (Group.algebra G) (# 2)
          invᴴ = AlgeStruct.ops (Group.algebra H) (# 2)
      in map (invᴳ (x ∷ [])) ≡ (invᴴ (map x ∷ []))

-- Group homomorphisms from G to H (using exponential notation H^G)
_^_ : {A B : Set} → Group B → Group A → Set
H ^ G = GroupHomomorphism G H

-- Identity homomorphism
idHom : {A : Set} → (G : Group A) → G ^ G
idHom G = record
  { map = λ x → x
  ; preserveMult = λ x y → refl
  ; preserveId = refl  
  ; preserveInv = λ x → refl
  }

-- Composition of homomorphisms
composeHom : {A B C : Set} → {G : Group A} {H : Group B} {K : Group C}
  → (K ^ H) → (H ^ G) → (K ^ G)
composeHom {G = G} {H = H} {K = K} φ ψ = record
  { map = λ x → GroupHomomorphism.map φ (GroupHomomorphism.map ψ x)
  ; preserveMult = λ x y → 
      let f = GroupHomomorphism.map ψ
          g = GroupHomomorphism.map φ
          _·ᴳ_ = AlgeStruct.ops (Group.algebra G) (# 0)
          _·ᴴ_ = AlgeStruct.ops (Group.algebra H) (# 0) 
          _·ᴷ_ = AlgeStruct.ops (Group.algebra K) (# 0)
      in begin
        g (f (_·ᴳ_ (x ∷ y ∷ [])))
          ≡⟨ cong g (GroupHomomorphism.preserveMult ψ x y) ⟩
        g (_·ᴴ_ (f x ∷ f y ∷ []))
          ≡⟨ GroupHomomorphism.preserveMult φ (f x) (f y) ⟩
        _·ᴷ_ (g (f x) ∷ g (f y) ∷ [])
      ∎
  ; preserveId = 
      let f = GroupHomomorphism.map ψ
          g = GroupHomomorphism.map φ
          eᴳ = AlgeStruct.ops (Group.algebra G) (# 1) []
          eᴴ = AlgeStruct.ops (Group.algebra H) (# 1) []
          eᴷ = AlgeStruct.ops (Group.algebra K) (# 1) []
      in begin
        g (f eᴳ)
          ≡⟨ cong g (GroupHomomorphism.preserveId ψ) ⟩
        g eᴴ
          ≡⟨ GroupHomomorphism.preserveId φ ⟩
        eᴷ
      ∎
  ; preserveInv = λ x → 
      let f = GroupHomomorphism.map ψ
          g = GroupHomomorphism.map φ
          invᴳ = AlgeStruct.ops (Group.algebra G) (# 2)
          invᴴ = AlgeStruct.ops (Group.algebra H) (# 2)
          invᴷ = AlgeStruct.ops (Group.algebra K) (# 2)
      in begin
        g (f (invᴳ (x ∷ [])))
          ≡⟨ cong g (GroupHomomorphism.preserveInv ψ x) ⟩
        g (invᴴ (f x ∷ []))
          ≡⟨ GroupHomomorphism.preserveInv φ (f x) ⟩
        invᴷ (g (f x) ∷ [])
      ∎
  }

-- -----------------------------------------------------------------------------
-- Group Category
-- -----------------------------------------------------------------------------

-- For the category of groups, we need to work with a universe of groups
-- We'll represent morphisms using a data type instead of a record to handle implicit parameters
data GroupMorphism : Set₁ where
  mkMor : {A B : Set} → (source : Group A) → (target : Group B) → (morphism : target ^ source) → GroupMorphism

-- Extract components from a group morphism
getSource : GroupMorphism → ∃ (λ A → Group A)
getSource (mkMor {A} G _ _) = A , G

getTarget : GroupMorphism → ∃ (λ B → Group B) 
getTarget (mkMor {B = B} _ H _) = B , H

-- Direct accessors for the groups (using existential to hide types)
sourceOf : (f : GroupMorphism) → Group (proj₁ (getSource f))
sourceOf (mkMor G _ _) = G

targetOf : (f : GroupMorphism) → Group (proj₁ (getTarget f))
targetOf (mkMor _ H _) = H

getMorphism : (f : GroupMorphism) → let (A , G) = getSource f
                                        (B , H) = getTarget f
                                    in H ^ G
getMorphism (mkMor _ _ φ) = φ

-- Identity morphism for a group  
id : {A : Set} → (G : Group A) → GroupMorphism
id G = mkMor G G (idHom G)

-- Simple composition: Given f : G → H and g : H → K, return g ∘ f : G → K
-- The proof is that both morphisms share the same middle group H
composeMorphisms : {A B C : Set} (G : Group A) (H : Group B) (K : Group C)
  → (φ : K ^ H) → (ψ : H ^ G) → GroupMorphism
composeMorphisms G H K φ ψ = mkMor G K (composeHom φ ψ)

-- Example usage: If we have groups G, H, K and morphisms φ : H → K, ψ : G → H
-- Then we can compose them as: composeMorphisms G H K φ ψ : G → K
-- The type system ensures they're composable!

-- Wrapper for composing GroupMorphism data when we know they're composable
composeIfCompatible : GroupMorphism → GroupMorphism → Maybe GroupMorphism
composeIfCompatible (mkMor {A} {B} H K φ) (mkMor {A'} {B'} G H' ψ) = 
  -- In practice, we'd check if A ≡ B' and H ≡ H' here
  -- For now, assume they match and compose
  just (mkMor G K (composeHom φ ψ))

-- Define which operations are total in the composition signature
totalOps : Subset compositionSig
totalOps = (# 0) ∷ (# 1) ∷ []  -- Domain and codomain are total, composition is partial

-- The algebraic structure on group morphisms as an East
GroupCategoryEast : East {lsuc lzero} {compositionSig} {Fin 3} {Fin 3} GroupMorphism totalOps
GroupCategoryEast = record 
  { totalOps = λ { # 0 → λ pf → λ { (f ∷ []) → id (sourceOf f) }  -- Domain operation f◄
                 ; # 1 → λ pf → λ { (f ∷ []) → id (targetOf f) }  -- Codomain operation ►f
                 ; # 2 → λ ()
                 }
  ; partialOps = λ { # 0 → λ ()
                   ; # 1 → λ ()
                   ; # 2 → λ pf → λ { (just f ∷ just g ∷ []) → composeIfCompatible f g
                                    ; _ → nothing
                                    }
                   }
  ; guards = λ { # 0 → λ ()
               ; # 1 → λ ()
               ; # 2 → λ pf → {!!}  -- Guard conditions for composition
               }
  }

