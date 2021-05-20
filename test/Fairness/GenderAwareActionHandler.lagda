\begin{code}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.List hiding (any ; _++_)
open import Relation.Nullary
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Nat.Show
open import Relation.Nullary.Decidable
open import Data.Unit
open import Data.String hiding (show; _<_ ; _<?_; _≟_; length)
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat.DivMod
import Relation.Unary as U
open import Relation.Nullary.Negation using (contradiction)
open import Function using (flip)

open import TaxiDomain
open import Fairness.Gender

open import Plans.Plan taxiDomain
open import Plans.Semantics taxiDomain hiding (¬_; flip)
open import Plans.ActionHandler taxiDomain

open ActionDescription

module Fairness.GenderAwareActionHandler
  (driverGender : Object taxi → Gender)
  (margin : ℕ)
  where

variable
  n m : ℕ

-------------------------------------------------------------------------------------------------------
-- Percentages

-- Return the number of taxis of a specific gender 
noGender : Gender → ℕ
noGender g = length (filter (λ t → decGender g (driverGender t)) allTaxis)

totalDrivers : ℕ
totalDrivers = _+_ (noGender male) (_+_ (noGender female) (noGender other))

-- Division with 0 / 0 = 0
infixl 7 _/₀_
_/₀_ : ℕ → ℕ → ℕ
n /₀ zero    = 0
n /₀ (suc m) = n / (suc m)

-- Percentage of each gender
percentage : Gender → ℕ
percentage g = (noGender g * 100) /₀ totalDrivers 

-------------------------------------------------------------------------------------------------------
-- Trip counts

TripCount : Set
TripCount = Gender → ℕ

--Total trips taken
totalTripsTaken : TripCount → ℕ
totalTripsTaken f = _+_ (_+_ (f male) (f female)) (f other)

updateTripCount : Action → TripCount → TripCount
updateTripCount (drive _ _ _)  f = f
updateTripCount (drivePassenger t1 _ _ _) f g with decGender (driverGender t1) g
... | no  _ = f g
... | yes _ = suc (f g)

-------------------------------------------------------------------------------------------------------
-- Conditions

-- Condition 1 : Driver does not get paid for trip

TripAgnostic : Action → Set
TripAgnostic (drivePassenger t p1 l1 l2) = ⊥
TripAgnostic (drive t l1 l2) = ⊤

TripAgnostic? : U.Decidable TripAgnostic
TripAgnostic? (drivePassenger x x₁ x₂ x₃) = no λ()
TripAgnostic? (drive x x₁ x₂) = yes tt

-- Condition 2 : Number of trips is too small to make a judgement about fairness

UnderMinimumTripThreshold : TripCount → Set
UnderMinimumTripThreshold tripCount = totalTripsTaken tripCount < totalDrivers * 10

UnderMinimumTripThreshold? : (tripCount : TripCount) → Dec (UnderMinimumTripThreshold tripCount)
UnderMinimumTripThreshold? tripCount = totalTripsTaken tripCount <? totalDrivers * 10

calculateGenderAssignment : Gender → TripCount → ℕ 
calculateGenderAssignment g tripCount = (tripCount g * 100) /₀ totalTripsTaken tripCount

calculateLowerbound : Gender → ℕ  
calculateLowerbound g = percentage g ∸ (percentage g /₀ margin)

-- Condition 3 : The assignment of trips is fair

IsFair : Gender → TripCount → Set
IsFair g f = calculateGenderAssignment g f  ≥ calculateLowerbound g

IsFair? : Decidable IsFair
IsFair? g f = calculateGenderAssignment g f ≥? calculateLowerbound g

IsFairForAll : TripCount → Set
IsFairForAll f = ∀ (g : Gender) → IsFair g f

IsFairForAll? : U.Decidable IsFairForAll
IsFairForAll? f with IsFair? male f | IsFair? female f | IsFair? other f
... | no ¬p | no ¬p₁ | no ¬p₂ = no (λ {x → ¬p (x male)})
... | no ¬p | no ¬p₁ | yes p = no (λ x → ¬p (x male))
... | no ¬p | yes p | no ¬p₁ = no (λ x → ¬p (x male))
... | no ¬p | yes p | yes p₁ = no (λ x → ¬p (x male))
... | yes p | no ¬p | no ¬p₁ = no (λ x → ¬p (x female))
... | yes p | no ¬p | yes p₁ = no (λ x → ¬p (x female))
... | yes p | yes p₁ | no ¬p = no (λ x → ¬p (x other))
... | yes p | yes p₁ | yes p₂ = yes (λ { male → p ; female → p₁ ; other → p₂})

-- Overall condition

data ActionPreservesFairness
  (α : Action) (tripCount : TripCount) : Set where
  underThreshold : UnderMinimumTripThreshold tripCount
    → ActionPreservesFairness α tripCount
  fairForAll : IsFairForAll tripCount
    → ActionPreservesFairness α tripCount
  agnostic : TripAgnostic α
    → ActionPreservesFairness α tripCount

ActionPreservesFairness? : ∀ action tripCount → Dec (ActionPreservesFairness action tripCount)
ActionPreservesFairness? action tripCount with
  TripAgnostic? action
  | UnderMinimumTripThreshold? tripCount
  | IsFairForAll? tripCount
... | yes ag | _      | _        = yes (agnostic ag)
... | _      | yes ut | _        = yes (underThreshold ut)
... | _      | _      | yes fair = yes (fairForAll fair)
... | no ¬ag | no ¬ut | no ¬fair = no λ
  { (agnostic ag)       → ¬ag ag
  ; (underThreshold ut) → ¬ut ut
  ; (fairForAll fair)   → ¬fair fair
  }

------------------------------------------------------------------------------------------------
-- Error handling

data GenderBiasError : Set where
  notProportional : (a : Action) (f : TripCount) → ¬ (ActionPreservesFairness a f) → GenderBiasError

proofToString : Gender → n ≱ m → String
proofToString {n} {m} gender _ =
  "The gender " ++ showGender gender ++ " is not proportional:"
  ++ " the assignment " ++ show n ++ " is not greater than the lower bound " ++ show m ++ ".\n"

errorMessage : GenderBiasError → Action × String
errorMessage (notProportional (drive _ _ _) f notFair) = contradiction (agnostic _) notFair
errorMessage (notProportional α f notFair) with IsFair? male f | IsFair? female f | IsFair? other f
... | no ¬p | no ¬p₁ | no ¬p₂ = α , proofToString male ¬p ++ proofToString female ¬p₁  ++ proofToString other ¬p₁
... | no ¬p | no ¬p₁ | yes p  = α , proofToString male ¬p ++ proofToString female ¬p₁
... | no ¬p | yes p  | no ¬p₁ = α , proofToString male ¬p ++ proofToString other ¬p₁
... | no ¬p | yes p  | yes p₁ = α , proofToString male ¬p
... | yes p | no ¬p  | no ¬p₁ = α , proofToString female ¬p ++ proofToString other ¬p₁
... | yes p | no ¬p  | yes p₁ = α , proofToString female ¬p
... | yes p | yes p₁ | no ¬p  = α , proofToString male ¬p
... | yes p | yes p₁ | yes p₂ = flip contradiction notFair (fairForAll (λ
  { male → p
  ; female → p₁
  ; other → p₂
  }))

---------------------------------------------------------------------------------------------------------------
-- Action Handler

GenderAwareActionHandler : Set
GenderAwareActionHandler =
  (α : Action)
  → {tripCount : Gender → ℕ} 
  → {fair : ActionPreservesFairness α tripCount}
  → World → World

enriched-σ : Context → GenderAwareActionHandler
enriched-σ Γ α = updateWorld (effects (Γ α ))

execute' : Plan →
           GenderAwareActionHandler →
           TripCount →
           World →
           World ⊎ GenderBiasError
execute' halt    σ tripCount w = inj₁ w  
execute' (a ∷ f) σ tripCount w with updateTripCount a tripCount
... | updatedTrips with ActionPreservesFairness? a updatedTrips
...   | yes fair = execute' f σ updatedTrips (σ a {fair = fair} w)
...   | no ¬fair = inj₂ (notProportional a updatedTrips ¬fair)
\end{code}
