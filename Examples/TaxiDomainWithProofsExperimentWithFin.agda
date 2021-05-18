module Tutorial.TaxiDomainWithProofsExperimentWithFin where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level hiding (suc)
-- open import Tactic.Deriving.Eq
open import Data.Nat hiding (suc ; zero ; _<_) renaming (ℕ to Nat)
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

open import Tutorial.Gender
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


-- Automatically derive decidable equality of the above types
{-
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

-}
