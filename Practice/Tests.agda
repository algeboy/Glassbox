open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Set)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
import Data.Nat as ℕ
import Data.Bool as Bool
import Data.Fin as Fin
import Data.String as String

module Practice.Tests where
    
    {- TYPES THAT SUPPORT DECIDABLE EQUALITY (Dec):
    
    1. ℕ (Natural numbers) - Data.Nat._≟_
    2. Bool (Booleans) - Data.Bool._≟_  
    3. Fin n (Finite types) - Data.Fin._≟_
    4. String - Data.String._≟_
    5. ⊤ (Unit type) - Data.Unit._≟_
    6. ⊥ (Empty type) - Data.Empty._≟_ (vacuously true)
    7. Char - Data.Char._≟_
    8. Product types A × B - if both A and B have decidable equality
    9. Sum types A ⊎ B - if both A and B have decidable equality  
    10. List A - if A has decidable equality
    11. Vec A n - if A has decidable equality
    12. Maybe A - if A has decidable equality
    
    You CANNOT use Dec on:
    - Arbitrary Set types (like Set, Set₁, etc.)
    - Function types (A → B)
    - Most custom datatypes unless you define decidable equality for them
    -}
    
    -- Examples of types with decidable equality:
    
    -- 1. Natural numbers
    testNat : ℕ.ℕ → ℕ.ℕ → Maybe (ℕ.ℕ ≡ ℕ.ℕ) 
    testNat n m with n ℕ.≟ m
    ... | yes proof = just refl  -- n ≡ m implies ℕ ≡ ℕ
    ... | no _ = nothing
    
    -- 2. Booleans  
    testBool : Bool.Bool → Bool.Bool → Maybe (Bool.Bool ≡ Bool.Bool)
    testBool b1 b2 with b1 Bool.≟ b2
    ... | yes proof = just refl
    ... | no _ = nothing
    
    -- 3. Finite types (Fin n)
    testFin : {n : ℕ.ℕ} → Fin.Fin n → Fin.Fin n → Maybe (Fin.Fin n ≡ Fin.Fin n)
    testFin x y with x Fin.≟ y  
    ... | yes proof = just refl
    ... | no _ = nothing
    
    -- 4. Strings
    testString : String.String → String.String → Maybe (String.String ≡ String.String)
    testString s1 s2 with s1 String.≟ s2
    ... | yes proof = just refl
    ... | no _ = nothing
    
    -- More examples of types with Dec:
    
    -- 5. Unit type (⊤)
    open import Data.Unit using (⊤; tt; _≟_)
    testUnit : ⊤ → ⊤ → Maybe (⊤ ≡ ⊤)
    testUnit x y with x ≟ y
    ... | yes proof = just refl
    ... | no _ = nothing
    
    -- 6. Empty type (⊥) - no values to test, but has decidable equality
    open import Data.Empty using (⊥; ⊥-elim)
    -- testEmpty : ⊥ → ⊥ → Maybe (⊥ ≡ ⊥)  -- Can't actually call this!
    
    -- 7. Products/Pairs (if components have decidable equality)
    open import Data.Product using (_×_; _,_)
    testPair : ℕ.ℕ × Bool.Bool → ℕ.ℕ × Bool.Bool → Maybe ((ℕ.ℕ × Bool.Bool) ≡ (ℕ.ℕ × Bool.Bool))
    testPair (n1 , b1) (n2 , b2) with n1 ℕ.≟ n2 | b1 Bool.≟ b2
    ... | yes _ | yes _ = just refl
    ... | _ | _ = nothing
    
    -- 8. Lists (if element type has decidable equality)
    open import Data.List using (List; []; _∷_)
    import Data.List.Properties as ListProps
    testList : List ℕ.ℕ → List ℕ.ℕ → Maybe (List ℕ.ℕ ≡ List ℕ.ℕ)
    testList xs ys with ListProps.≡-dec ℕ._≟_ xs ys
    ... | yes proof = just refl
    ... | no _ = nothing