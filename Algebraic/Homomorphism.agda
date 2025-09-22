
open import Agda.Primitive using (Set)
open import Data.Empty using (⊥-elim)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Vec using (Vec; map)
open import Data.Vec.Properties using (map-id)

open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

open import Algebraic.Signatures
open import Countable.Sets
open import Algebraic.Structures

{-- A minimal countable constructive set theory. --}
module Algebraic.Homomorphism where

    test : (A B : Set) -> Maybe A ≡ B
    test A B with Dec (A ≡ B)
    ...| yes proof = just proof
    ...| no _ = nothing

    {-- Sub categories are implemented as guards --}
    IsHom : (f : ConFun) 
            → ( A B : Structure {sig} ) 
            → ( p : (f ◄) = id A )
            → ( q : (◄ f) = id B )
            → ( p : ¬( f = ▦ ) ) 
            → (i : Fin (nOps sig)) 
            → (x : Vec (asSet A) (proj₂ (proj₂ sig i))) →
            f (opsA i x) ≡ opsB i (map f x)


    HomProof : ∀ {sig : Signature} {A B : Structure {sig}} 
            → (f : asSet (proj₁ A) → asSet (proj₁ B)) 
            → Set
    HomProof {sig} {A , opsA} {B , opsB} f = 
        (i : Fin (nOps sig)) →
        (x : Vec (asSet A) (proj₂ (proj₂ sig i))) →
            f (opsA i x) ≡ opsB i (map f x)

    

    asHom-FF : ∀ {sig : Signature} {a b : ℕ}
                → (A : Structure {sig} ) 
                → (B : Structure {sig} ) 
                → {pA : proj₁ A ≡ F a}
                → {pB : proj₁ B ≡ F b}
                → (f : asSet (proj₁ A) → asSet (proj₁ B)) 
                → (isHom : HomProof {sig} {A} {B} f)
                → ConFun
    asHom-FF (F a , opsA) (F b , opsB) {refl} {refl} f isHom  = F←F {a} {b} f

    {-- Operators on Hom --}



    -- {-- This is Definition 3.?? : Homomorphism --}
    -- Homomorphism : ∀ {sig : Signature} → Set
    -- Homomorphism {sig} =
    --     Σ[ algA : Structure {sig} ]
    --     Σ[ algB : Structure {sig} ]
    --     Σ[ f ∈ ConFun ]
    --     pf :  where 
    --     ( idFun : asSet (proj₁ algA) → asSet (proj₁ algA) )
    --     ( pf :
    --     ((i : Fin (nOps sig)) →
    --         (x : Vec (asSet A) (proj₂ (proj₂ sig i))) →
    --             f (opsA i x) ≡ opsB i (map f x)
    --     )
    -- record Homomorphism where
    --     constructor □ | H
    --     field
    --         algA : Structure {sig}
    --         algB : Structure {sig}
    --         homAB : realHomomorphism algA algB

    {-- This is Definition 3.?? : Homomorphism --}
    -- Homomorphism₁ : ∀ {sig : Signature} → Structure₁ {sig} → Structure₁ {sig} → Set
    -- Homomorphism₁ {sig} (A , opsA) (B , opsB) = 
    --     Σ[ f ∈ (A → B) ]
    --     ((i : Fin (nOps sig)) →
    --         (x : Vec A (proj₂ (proj₂ sig i))) →
    --             f (opsA i x) ≡ opsB i (map f x)
    --     )        

    -- {-- Proof that identity function on any set is a homomorphism --}
    -- idHom : ∀ {sig : Signature} {A : Structure {sig}} → Homomorphism {sig} A A
    -- idHom {sig} {A , opsA} = (idFun , idPf)
    --   where
    --     idFun : asSet A → asSet A
    --     idFun x = x
        
    --     idPf : (i : Fin (nOps sig)) →
    --            (x : Vec (asSet A) (proj₂ (proj₂ sig i))) →
    --            idFun (opsA i x) ≡ opsA i (map idFun x)
    --     idPf i x rewrite map-id x = refl

    -- {-- source of Homomorphism returns identity on domain --}
    -- source : ∀ {sig : Signature} {A B : Structure {sig}} → Homomorphism {sig} A B → Homomorphism {sig} A A
    -- source {sig} {A} {B} (f , pf) = idHom {sig} {A}

    -- {-- target of Homomorphism returns identity on codomain --}
    -- target : ∀ {sig : Signature} {A B : Structure {sig}} → Homomorphism {sig} A B → Homomorphism {sig} B B
    -- target {sig} {A} {B} (f , pf) = idHom {sig} {B} 

    -- {-- Composition of homomorphisms --}
    -- _∘_ : ∀ {sig : Signature} {A B C : Structure {sig}} 
    --       → Homomorphism {sig} B C 
    --       → Homomorphism {sig} A B
    --       → Homomorphism {sig} A C
    -- _∘_ {sig} {A} {B} {C} (g , pfG) (f , pfF) = (g ← f , {!!})
