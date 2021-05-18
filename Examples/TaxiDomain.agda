module Examples.TaxiDomain where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level hiding (suc)
-- open import Tactic.Deriving.Eq
open import Data.Nat hiding (suc ; zero ; _<_; _≟_) renaming (ℕ to Nat)
import Data.Nat.Literals as NatLiterals
open import Data.Fin using (Fin; #_; fromℕ<; toℕ)
open import Data.Fin.Patterns
import Data.Fin.Literals as FinLiterals
open import Relation.Nullary.Decidable using (True)
open import Data.Nat using (suc; _≤?_) 
open import Agda.Builtin.Unit

--  taxi : ∀ (i : Fin 4) -> C taxi
-- Data.Fin.Literals or Patterns

-- Types for out domai

-- Types for out domain.
data Type : Set where
  taxi : Type
  location : Type
  person : Type


numberOfTaxis : Nat
numberOfTaxis = 3

numberOfLocations : Nat
numberOfLocations = 3

numberOfPeople : Nat
numberOfPeople = 3

-- A list of typed constants. 
data C : Type -> Set where
  taxi : Fin numberOfTaxis -> C taxi
  location : Fin numberOfLocations -> C location
  person : Fin numberOfPeople -> C person

data R : Set where
  taxiIn : C taxi → C location → R
  personIn : C person -> C location -> R

data Action : Set where
  drivePassenger : C taxi → C person → C location → C location → Action
  drive : C taxi → C location → C location → Action

open import Examples.Gender
open import Agda.Builtin.FromNat

instance
  NumNat : Number Nat
  NumNat = NatLiterals.number
  
instance
  NumFin : ∀ {n} → Number (Fin n)
  NumFin {n} = FinLiterals.number n

-- Assign all taxis to a gender
getGender : C taxi -> Gender
getGender (taxi 0F) = male
getGender (taxi 1F) = female
getGender (taxi 2F) = male

-- Generate list of all possible taxis
allTaxis : List (C taxi)
allTaxis = Data.List.map taxi (allFin numberOfTaxis)

-- return the number of taxis of a specific gender 
noGender : Gender -> Nat
noGender g = length (filter (λ t → decGender g (getGender t)) allTaxis)

-----------------------------------------------------------------------------------
-- The rest is proving decidable equality for all of the above data types.

Type? : (x y : Type) → Dec (x ≡ y)
Type? taxi taxi = yes refl
Type? taxi location = no (λ ())
Type? taxi person = no (λ ())
Type? location taxi = no (λ ())
Type? location location = yes refl
Type? location person = no (λ ())
Type? person taxi = no (λ ())
Type? person location = no (λ ())
Type? person person = yes refl

isDECT : IsDecEquivalence {zero} {zero} (_≡_ {A = Type})
isDECT = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = Type?  }

open import Data.Fin.Properties using (_≟_)

C? : {t : Type} -> (x y : C t) → Dec (x ≡ y)
C? (taxi x) (taxi x₁) with x ≟ x₁
... | no ¬p = no (λ { refl → ¬p refl})
... | yes refl = yes refl
C?  (location x) (location x₁) with x ≟ x₁
... | no ¬p = no (λ { refl → ¬p refl})
... | yes refl = yes refl
C?  (person x) (person x₁) with x ≟ x₁
... | no ¬p = no (λ { refl → ¬p refl})
... | yes refl = yes refl

isDEC : (t : Type) -> IsDecEquivalence {zero} {zero} (_≡_ {A = C t})
isDEC t = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = C? }

open IsDecEquivalence isDECT hiding (refl ; sym ; trans) renaming (_≟_ to _≟ₜ_)
open import Relation.Nullary

decSingleC : (t : Type) -> (x y : C t) -> Dec (x ≡ y)
decSingleC t x y = x ≟c y
  where open IsDecEquivalence (isDEC t) renaming (_≟_ to _≟c_)

R? : (x y : R) → Dec (x ≡ y)
R? (taxiIn x x₁) (taxiIn x₂ x₃) with C? x x₂ | C? x₁ x₃
... | no ¬p | no ¬p₁ = no (λ { refl → ¬p₁ refl})
... | no ¬p | yes p = no (λ { refl → ¬p refl})
... | yes p | no ¬p = no (λ { refl → ¬p refl})
... | yes refl | yes refl = yes refl
R? (taxiIn x x₁) (personIn x₂ x₃) = no (λ ())
R? (personIn x x₁) (taxiIn x₂ x₃) = no (λ ())
R? (personIn x x₁) (personIn x₂ x₃) with C? x x₂ | C? x₁ x₃
... | no ¬p | no ¬p₁ = no (λ { refl → ¬p₁ refl})
... | no ¬p | yes p = no (λ { refl → ¬p refl})
... | yes p | no ¬p = no (λ { refl → ¬p refl})
... | yes refl | yes refl = yes refl

isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = R})
isDecidable = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
 _≟_ = R?  }



