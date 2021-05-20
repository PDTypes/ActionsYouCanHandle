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
open import Data.String hiding (show; _<_ ; _<?_; _≟_ )
open import Relation.Nullary
open import Data.Maybe
open import Data.Nat.DivMod

open import TaxiDomain
open import Fairness.Gender

open import Plans.Plan taxiDomain
open import Plans.Semantics taxiDomain hiding (¬_)
open import Plans.ActionHandler taxiDomain

open ActionDescription

module Fairness.GenderAwareActionHandler
  (getGender : Object taxi → Gender)
  (margin : ℕ)
  where

variable
  n m : ℕ

open IsDecEquivalence isDecidable renaming (_≟_ to _≟ᵣ_)

-- Instead of float we will us nat to two decimal places by multiplying by 100

totalDrivers : ℕ
totalDrivers = _+_ (noGender male) (_+_ (noGender female) (noGender other))

-- Division with 0 / 0 = 0

infixl 7 _/₀_
_/₀_ : ℕ → ℕ → ℕ
n /₀ zero    = 0
n /₀ (suc m) = n / (suc m)

--percentage of each gender
percentage : Gender → ℕ
percentage g = (noGender g * 100) /₀ totalDrivers 

-- Cannot have over a 20% difference in taxi allocations from the proportional representation
-- could move this so it is passed into the module
tripsTakenOrig : Gender → ℕ
tripsTakenOrig x = 5

--Total trips taken
totalTripsTaken : (Gender → ℕ) → ℕ
totalTripsTaken f = _+_ (_+_ (f male) (f female)) (f other)

incTripsG : Gender → (Gender → ℕ) → (Gender → ℕ)
incTripsG g f g1 with decGender g g1
... | no  _ = f g1
... | yes _ = suc (f g)

-- True if the action does not affect the number of trips taken
TripAgnostic : Action → Set
TripAgnostic (drivePassenger t p1 l1 l2) = ⊥
TripAgnostic (drive t l1 l2) = ⊤


-------------------------------------------------------------------------------------------------------
-- Conditions

UnderMinimumTripThreshold : (f : (Gender → ℕ)) → Set
UnderMinimumTripThreshold tripsTaken = totalTripsTaken tripsTaken < (totalDrivers * 10)

underMinimumTripThreshold? : (f : (Gender → ℕ)) → Dec (UnderMinimumTripThreshold f)
underMinimumTripThreshold? f = totalTripsTaken f <? (totalDrivers * 10)

calculateGenderAssignment : Gender → (Gender → ℕ) → ℕ 
calculateGenderAssignment g f = (f g * 100) /₀ (totalTripsTaken f)

calculateLowerbound : Gender → ℕ  
calculateLowerbound g = percentage g ∸ (percentage g /₀ margin)

IsFair : (g : Gender) → (f : (Gender → ℕ)) → Set
IsFair g f = calculateGenderAssignment g f  ≥ calculateLowerbound g

isFair? : Decidable IsFair
isFair? g f = calculateGenderAssignment g f ≥? calculateLowerbound g

IsFairForAll : (f : (Gender → ℕ)) → Set
IsFairForAll f = ∀ (g : Gender) → IsFair g f

isFairForAll? : (f : (Gender → ℕ)) → Dec (IsFairForAll f)
isFairForAll? f with isFair? male f | isFair? female f | isFair? other f
... | no ¬p | no ¬p₁ | no ¬p₂ = no (λ {x → ¬p (x male)})
... | no ¬p | no ¬p₁ | yes p = no (λ x → ¬p (x male))
... | no ¬p | yes p | no ¬p₁ = no (λ x → ¬p (x male))
... | no ¬p | yes p | yes p₁ = no (λ x → ¬p (x male))
... | yes p | no ¬p | no ¬p₁ = no (λ x → ¬p (x female))
... | yes p | no ¬p | yes p₁ = no (λ x → ¬p (x female))
... | yes p | yes p₁ | no ¬p = no (λ x → ¬p (x other))
... | yes p | yes p₁ | yes p₂ = yes (λ { male → p ; female → p₁ ; other → p₂})

------------------------------------------------------------------------------------------------
-- Error Handling

proofToString : n ≱ m → String
proofToString {n} {m} x = "the assignment " ++ show n ++ " is not greater than the lower bound " ++ show m

data Error : Set where
  notProportional : Action → (f : Gender → ℕ) → ¬ (IsFairForAll f) → Error

errorMessage : Error → String × Action
errorMessage (notProportional α f x₁) with isFair? male f | isFair? female f | isFair? other f
... | no ¬p | no ¬p₁ | no ¬p₂ = "The gender male is not proportional: " ++ proofToString ¬p ++  ". The gender female is not proportional: " ++ proofToString ¬p₁  ++ ". The gender other is not proportional: " ++ proofToString ¬p₁ , α
... | no ¬p | no ¬p₁ | yes p = "The gender male is not proportional: " ++ proofToString ¬p ++  ". The gender female is not proportional: " ++ proofToString ¬p₁  , α
... | no ¬p | yes p | no ¬p₁ = "The gender male is not proportional: " ++ proofToString ¬p ++  ". The gender other is not proportional: " ++ proofToString ¬p₁  , α
... | no ¬p | yes p | yes p₁ = "The gender male is not proportional: " ++ proofToString ¬p  , α
... | yes p | no ¬p | no ¬p₁ = "The gender female is not proportional: " ++ proofToString ¬p ++ ". The gender other is not proportional: " ++ proofToString ¬p₁  , α
... | yes p | no ¬p | yes p₁ = "The gender female is not proportional: " ++ proofToString ¬p  , α
... | yes p | yes p₁ | no ¬p = "The gender other is not proportional: " ++ proofToString ¬p , α
... | yes p | yes p₁ | yes p₂ = ⊥-elim (x₁ (λ { male → p ; female → p₁ ; other → p₂}))

---------------------------------------------------------------------------------------------------------------
-- Action Handler


data ActionPreservesFairness
  (α : Action)(g : Gender)(tripsTaken : Gender → ℕ) : Set where
  underThreshold : UnderMinimumTripThreshold tripsTaken
    → ActionPreservesFairness α g tripsTaken
  fairForAll : IsFairForAll (incTripsG g tripsTaken)
    → ActionPreservesFairness α g tripsTaken
  agnostic : TripAgnostic α
    → ActionPreservesFairness α g tripsTaken

--need to fix this to include minimum trips 
GenderAwareActionHandler : Set
GenderAwareActionHandler =
  (α : Action)
  → {g : Gender}
  → {tripsTaken : (Gender → ℕ)} 
  → {ActionPreservesFairness α g tripsTaken}
  → World → World

enriched-σ : Context → GenderAwareActionHandler
enriched-σ Γ α = updateWorld (effects (Γ α ))

execute' : Plan → GenderAwareActionHandler
            → (tripsTaken : (Gender → ℕ))
            → World
            → World ⊎ Error
execute' (drivePassenger txi p1 l1 l2 ∷ f) σ tripsTaken w with underMinimumTripThreshold? tripsTaken
... | yes p = execute' f σ (incTripsG (getGender txi) tripsTaken) 
                                                             (σ (drivePassenger txi p1 l1 l2)
                                                                 {getGender txi}
                                                                 {tripsTaken}
                                                                 {underThreshold p}
                                                                 w)
... | no ¬p with isFairForAll? (incTripsG (getGender txi) tripsTaken) 
... | no ¬p₁ = inj₂ (notProportional (drivePassenger txi p1 l1 l2) ((incTripsG (getGender txi) tripsTaken)) ¬p₁) --inj₂ (notProportional _ ¬p)
... | yes p =  execute' f σ (incTripsG (getGender txi) tripsTaken) 
                                                             (σ (drivePassenger txi p1 l1 l2)
                                                                 {getGender txi}
                                                                 {tripsTaken}
                                                                 {fairForAll p}
                                                                 w)
execute' (drive txi l1 l2 ∷ f) σ tripsTaken w = execute' f σ tripsTaken 
                                                             (σ (drive txi l1 l2)
                                                                 {getGender txi}
                                                                 {tripsTaken} 
                                                                {agnostic tt}
                                                                 w)
execute' halt σ tripsTaken w = inj₁ w  

\end{code}
