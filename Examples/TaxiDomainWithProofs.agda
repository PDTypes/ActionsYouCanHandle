module Examples.TaxiDomainWithProofs where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Tactic.Deriving.Eq

--  taxi : ∀ (i : Fin 4) -> C taxi
-- Data.Fin.Literals or Patterns

-- Types for out domai

-- Types for out domain.
data Type : Set where
  taxi : Type
  location : Type
  person : Type

-- A list of typed constants. 
data C : Type -> Set where
  taxi1 taxi2 taxi3 : C taxi
  location1 location2 location3 : C location
  person1 person2 person3 : C person

-- Predicates 
data R : Set where
  taxiIn : C taxi → C location → R
  personIn : C person -> C location -> R

-- Actions
data Action : Set where
  drivePassenger : C taxi → C person → C location → C location → Action
  drive : C taxi → C location → C location → Action

-----------------------------------------------------------------------------------
-- The rest is proving decidable equality for all of the above data types.


-- Automatically derive decidable equality of the above types
unquoteDecl EqT = deriveEq EqT (quote Type)
unquoteDecl EqC = deriveEq EqC (quote C)
unquoteDecl EqR = deriveEq EqR (quote R)
unquoteDecl EqAction = deriveEq EqAction (quote Action)

open import Mangle using (mangle)

isDECT : IsDecEquivalence {zero} {zero} (_≡_ {A = Type})
isDECT = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }

isDEC : (t : Type) -> IsDecEquivalence {zero} {zero} (_≡_ {A = C t})
isDEC t = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }

open IsDecEquivalence isDECT hiding (refl ; sym ; trans) renaming (_≟_ to _≟ₜ_)
open import Relation.Nullary

decSingleC : (t : Type) -> (x y : C t) -> Dec (x ≡ y)
decSingleC t x y = x ≟c y
  where open IsDecEquivalence (isDEC t) renaming (_≟_ to _≟c_)

isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = R})
isDecidable = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
 _≟_ = mangle  }

isDECA : IsDecEquivalence {zero} {zero} (_≡_ {A = Action})
isDECA = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }
