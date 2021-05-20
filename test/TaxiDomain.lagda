\begin{code}
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level hiding (suc)
open import Data.Nat hiding (suc ; zero ; _<_; _≟_) renaming (ℕ to Nat)
open import Data.Fin using (Fin; #_; fromℕ<; toℕ)
open import Data.Fin.Patterns
open import Relation.Nullary.Decidable using (True)
open import Data.Nat using (suc; _≤?_) 
open import Data.Unit using (⊤)
open import Data.Product using (_,_)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary

open import Plans.Domain
open import Plans.Domain.Core

module TaxiDomain where

-- Types for the domain.
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

-- Predicates

data Predicate : Set where
  taxiIn : Object taxi → Object location → Predicate
  personIn : Object person -> Object location -> Predicate

-- Actions

data Action : Set where
  drivePassenger :
    Object taxi →
    Object person →
    Object location →
    Object location →
    Action
  drive :
    Object taxi →
    Object location →
    Object location →
    Action

Γ : Action → ActionDescription Type Action Predicate
Γ (drivePassenger t1 p1 l1 l2) = record {
  preconditions =
    (+ , taxiIn t1 l1) ∷
    (+ , personIn p1 l1) ∷ [] ;
  effects =
    (- , taxiIn t1 l1) ∷
    (- , personIn p1 l1) ∷
    (+ , taxiIn t1 l2) ∷
    (+ , personIn p1 l2) ∷ [] }
Γ (drive t1 l1 l2) = record {
  preconditions =
    (+ , taxiIn t1 l1) ∷ [] ;
  effects =
    (- , taxiIn t1 l1) ∷ (+ , taxiIn t1 l2) ∷ [] }

-----------------------------------------------------------------------------------
-- Proving decidable equality for all of the above data types.

Type? : DecidableEquality Type
Type? taxi taxi = yes refl
Type? taxi location = no (λ ())
Type? taxi person = no (λ ())
Type? location taxi = no (λ ())
Type? location location = yes refl
Type? location person = no (λ ())
Type? person taxi = no (λ ())
Type? person location = no (λ ())
Type? person person = yes refl

Object? : ∀ {t : Type} -> DecidableEquality (Object t)
Object? (taxi x) (taxi x₁) with x ≟ x₁
... | no ¬p = no (λ { refl → ¬p refl})
... | yes refl = yes refl
Object?  (location x) (location x₁) with x ≟ x₁
... | no ¬p = no (λ { refl → ¬p refl})
... | yes refl = yes refl
Object?  (person x) (person x₁) with x ≟ x₁
... | no ¬p = no (λ { refl → ¬p refl})
... | yes refl = yes refl

Predicate? : DecidableEquality Predicate
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

isDECT : IsDecEquivalence {A = Type} _≡_
isDECT = isDecEquivalence Type?

isDEC : (t : Type) -> IsDecEquivalence {A = Object t} _≡_
isDEC t = isDecEquivalence Object?

isDecidable : IsDecEquivalence {A = Predicate} _≡_
isDecidable = isDecEquivalence Predicate?


-----------------------------------------------------------------------------------
-- Domain

-- Generate list of all possible taxis
allTaxis : List (Object taxi)
allTaxis = Data.List.map taxi (allFin numberOfTaxis)

taxiDomain : Domain
taxiDomain = record
  { Type = Type
  ; Predicate = Predicate
  ; Action = Action
  ; Γ = Γ
  ; _≟ₚ_ = Predicate? }

open Domain taxiDomain public
  hiding (Action; Predicate; Type; Γ)

\end{code}
