-- General agda --
open import Data.Product using (_,_)
open import Data.List as List using (List; []; _∷_; lookup; length; filter)
-- -- For decision procedures and pattern matching
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Vec as Vec using (Vec; []; _∷_; toList)
open import Data.Fin using (Fin; zero; suc; #_; cast; toℕ)
open import Data.Nat as Nat using (ℕ; _+_; suc)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin.Properties as FinProps using (toℕ-injective)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)


open import Algebras
-- open import GroupBasic


Arithmetic : Signature 
Arithmetic = ("0" ∷ "+" ∷ [] , valence)
  where
    valence : String → ℕ
    valence "0" = 0
    valence "+" = 2
    valence _ = 0  -- default


-- Define Zmodn monoid as inhabitant of AlgeStruct
-- input n yields Z mod (n+1) Z 
-- annoying hack to make sure we're not calling Fin 0

-- -- first Fin 
-- makeZn : ℕ → Set
-- makeZn n = Fin (suc n)

-- -- now zero op
-- makeZnZero : (n : ℕ) → Vec (makeZn n) 0 → (makeZn n)
-- makeZnZero n _ = # 0

-- -- this is plus op
-- makeZnPlus : (n : ℕ) → Vec (makeZn n) 2 → (makeZn n)
-- makeZnPlus n (x ∷ y ∷ []) = (toℕ x + toℕ y) mod (suc n)


-- -- here is the AlgeStruct for ZmodnZ
-- ZmodnZ : (n : ℕ) → (AlgeStruct {lzero} {Arithmetic} (makeZn n))
-- ZmodnZ n = record
--     { car = (makeZn n)
--       ops = λ { zero → (makeZnZero n) ;
--                         (suc zero) → (makeZnPlus n) }
--     }


-- -- EXAMPLE: Zmod17Z
-- -- first the whole AlgeStruct
-- Zmod17Z : AlgeStruct {lzero} {Arithmetic} (makeZn 16)
-- Zmod17Z = ZmodnZ 16
-- -- now the carrier
-- Z17 : Set
-- Z17 = AlgeStruct.car Zmod17Z
-- -- here is the addition
-- plusZ17 : Vec Z17 2 → Z17
-- plusZ17 = AlgeStruct.ops Zmod17Z (suc zero)
-- -- example addition
-- testsum : Z17
-- testsum = plusZ17 (# 14 ∷ # 6 ∷ [])
-- isRight : Dec (testsum ≡ # 3)
-- isRight = yes refl

