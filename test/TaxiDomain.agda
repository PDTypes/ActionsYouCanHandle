open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level hiding (suc)
open import Data.Nat hiding (suc ; zero ; _<_; _≟_) renaming (ℕ to Nat)
import Data.Nat.Literals as NatLiterals
open import Data.Fin using (Fin; #_; fromℕ<; toℕ)
open import Data.Fin.Patterns
import Data.Fin.Literals as FinLiterals
open import Relation.Nullary.Decidable using (True)
open import Data.Nat using (suc; _≤?_) 
open import Agda.Builtin.Unit

open import Plans.Domain

module TaxiDomain where

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
data Object : Type -> Set where
  taxi : Fin numberOfTaxis -> Object taxi
  location : Fin numberOfLocations -> Object location
  person : Fin numberOfPeople -> Object person

data Predicate : Set where
  taxiIn : Object taxi → Object location → Predicate
  personIn : Object person -> Object location -> Predicate

data Action : Set where
  drivePassenger : Object taxi → Object person → Object location → Object location → Action
  drive : Object taxi → Object location → Object location → Action

open import Agda.Builtin.FromNat

instance
  NumNat : Number Nat
  NumNat = NatLiterals.number
  
instance
  NumFin : ∀ {n} → Number (Fin n)
  NumFin {n} = FinLiterals.number n


-- Generate list of all possible taxis
allTaxis : List (Object taxi)
allTaxis = Data.List.map taxi (allFin numberOfTaxis)


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

Object? : {t : Type} -> (x y : Object t) → Dec (x ≡ y)
Object? (taxi x) (taxi x₁) with x ≟ x₁
... | no ¬p = no (λ { refl → ¬p refl})
... | yes refl = yes refl
Object?  (location x) (location x₁) with x ≟ x₁
... | no ¬p = no (λ { refl → ¬p refl})
... | yes refl = yes refl
Object?  (person x) (person x₁) with x ≟ x₁
... | no ¬p = no (λ { refl → ¬p refl})
... | yes refl = yes refl

isDEC : (t : Type) -> IsDecEquivalence {zero} {zero} (_≡_ {A = Object t})
isDEC t = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = Object? }

open IsDecEquivalence isDECT hiding (refl ; sym ; trans) renaming (_≟_ to _≟ₜ_)
open import Relation.Nullary

decSingleC : (t : Type) -> (x y : Object t) -> Dec (x ≡ y)
decSingleC t x y = x ≟c y
  where open IsDecEquivalence (isDEC t) renaming (_≟_ to _≟c_)

Predicate? : (x y : Predicate) → Dec (x ≡ y)
Predicate? (taxiIn x x₁) (taxiIn x₂ x₃) with Object? x x₂ | Object? x₁ x₃
... | no ¬p | no ¬p₁ = no (λ { refl → ¬p₁ refl})
... | no ¬p | yes p = no (λ { refl → ¬p refl})
... | yes p | no ¬p = no (λ { refl → ¬p refl})
... | yes refl | yes refl = yes refl
Predicate? (taxiIn x x₁) (personIn x₂ x₃) = no (λ ())
Predicate? (personIn x x₁) (taxiIn x₂ x₃) = no (λ ())
Predicate? (personIn x x₁) (personIn x₂ x₃) with Object? x x₂ | Object? x₁ x₃
... | no ¬p | no ¬p₁ = no (λ { refl → ¬p₁ refl})
... | no ¬p | yes p = no (λ { refl → ¬p refl})
... | yes p | no ¬p = no (λ { refl → ¬p refl})
... | yes refl | yes refl = yes refl

isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = Predicate})
isDecidable = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
 _≟_ = Predicate?  }

-----------------------------------------------------------------------------------
-- Domain

taxiDomain : Domain
taxiDomain = record
  { Type = Type
  ; Action = Action
  ; Predicate = Predicate
  ; _≟ₚ_ = Predicate?
  }


