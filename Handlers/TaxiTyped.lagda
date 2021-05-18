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
open import Agda.Builtin.Nat hiding (_<_)
open import Data.Nat 
open import Relation.Nullary.Decidable
open import Examples.Gender
open import Examples.TaxiDomain
open import Agda.Builtin.Unit
open import Data.String hiding (_<_ ; _<?_; _≟_ )

module Handlers.TaxiTyped  (getGender : C taxi → Gender)
                           (noOfGender : Gender → Nat)
                           (margin : Nat) where


variable
  n m : Nat

-- This imports our typed planning Grammar

open import GrammarTypes Action R Type C hiding (¬_)

----------------------------------------------------------------------------------------

open import Relation.Nullary
open import Data.Maybe



effects = ActionDescription.effects

-- This is the type of an ActionHandler. An ActionHandler takes in an Action and a World and returns a new World.
-- This Action handler also has a type that ensures that every Action is associated with a taxi and that the taxi
-- will not exceed its max number of trips. Here we assume that the numberOfTrips function is an auto-updating oracle.
ActionHandler : Set
ActionHandler = Action -> World -> World

open IsDecEquivalence  isDecidable renaming (_≟_ to _≟ᵣ_)


-- Remove a predicate R from a world.
remove : R → World → World
remove x [] = []
remove x (y ∷ w) with x ≟ᵣ y
remove x (y ∷ w) | yes p = remove x w
remove x (y ∷ w) | no ¬p = y ∷ remove x w

-- World constructor from state
σα : State → World → World
σα [] w = w
σα ((+ , x) ∷ N) w = x ∷ σα N w
σα ((- , x) ∷ N) w = remove x (σα N w)

-- Instead of float we will us nat to two decimal places by multiplying by 100
open import Data.Nat.DivMod

totalDrivers : Nat
totalDrivers = _+_ (noOfGender male) (_+_ (noOfGender female) (noOfGender other))

-- Dividing by zero equals zero

zeroDiv : Nat -> Nat -> Nat
zeroDiv n m with m ≟ 0
... | yes p = 0 
zeroDiv n zero | no ¬p = ⊥-elim (¬p _≡_.refl)
zeroDiv n (suc m) | no ¬p = n / (suc m)

--percentage of each gender
percentage : Gender -> Nat
percentage g = zeroDiv (noOfGender g * 100) totalDrivers 

-- Cannot have over a 20% difference in taxi allocations from the proportional representation
-- could move this so it is passed into the module
tripsTakenOrig : Gender -> Nat
tripsTakenOrig x = 5

--Total trips taken
totalTripsTaken : (Gender -> Nat) -> Nat
totalTripsTaken f = _+_ (_+_ (f male) (f female)) (f other)

incTripsG : Gender -> (Gender -> Nat) -> (Gender -> Nat)
incTripsG g f g1 with decGender g g1
... | no ¬p = f g1
... | yes _≡_.refl = suc (f g)

-- True if the action does not affect the number of trips taken
TripAgnostic : Action -> Set
TripAgnostic (drivePassenger t p1 l1 l2) = ⊥
TripAgnostic (drive t l1 l2) = ⊤


-------------------------------------------------------------------------------------------------------
-- Conditions

UnderMinimumTripThreshold : (f : (Gender -> Nat)) -> Set
UnderMinimumTripThreshold f = totalTripsTaken f < (totalDrivers * 10)

underMinimumTripThreshold? : (f : (Gender -> Nat)) -> Dec (UnderMinimumTripThreshold f)
underMinimumTripThreshold? f = totalTripsTaken f <? (totalDrivers * 10)

calculateGenderAssignment : Gender -> (Gender -> Nat) -> Nat 
calculateGenderAssignment g f =
  zeroDiv (f g * 100) (totalTripsTaken f)

calculateLowerbound : Gender -> Nat  
calculateLowerbound g =
  _-_ (percentage g) (zeroDiv (percentage g) margin)

IsFair : (g : Gender) -> (f : (Gender -> Nat)) -> Set
IsFair g f =
  calculateGenderAssignment g f  ≥ calculateLowerbound g

isFair? : (g : Gender) -> (f : (Gender -> Nat)) -> Dec (IsFair g f)
isFair? g f = calculateGenderAssignment g f ≥? calculateLowerbound g

IsFairForAll : (f : (Gender -> Nat)) -> Set
IsFairForAll f = ∀ (g : Gender) -> IsFair g f

isFairForAll? : (f : (Gender -> Nat)) -> Dec (IsFairForAll f)
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

open import Data.Nat.Show

proofToString : ¬ (n Data.Nat.≥ m) -> String
proofToString {n} {m} x = "the assignment " ++ Data.Nat.Show.show n ++ " is not greater than the lower bound " ++ Data.Nat.Show.show m

data Error : Set where
  notProportional : Action -> (f : Gender -> Nat) -> ¬ (IsFairForAll f) -> Error

errorMessage : Error -> String × Action
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
  (α : Action)(g : Gender)(tripsTaken : Gender -> Nat) : Set where
  underThreshold : UnderMinimumTripThreshold tripsTaken
    -> ActionPreservesFairness α g tripsTaken
  fairForAll : IsFairForAll (incTripsG g tripsTaken)
    -> ActionPreservesFairness α g tripsTaken
  agnostic : TripAgnostic α
    -> ActionPreservesFairness α g tripsTaken

--need to fix this to include minimum trips 
GenderAwareActionHandler : Set
GenderAwareActionHandler =
  (α : Action)
  -> {g : Gender}
  -> {tripsTaken : (Gender -> Nat)} 
  -> {ActionPreservesFairness α g tripsTaken}
  -> World -> World

execute' : Plan -> GenderAwareActionHandler
            -> (tripsTaken : (Gender -> Nat))
            -> World
            -> World ⊎ Error
execute' ((drivePassenger txi p1 l1 l2) ∷ f) σ tripsTaken w with underMinimumTripThreshold? tripsTaken
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
execute' ((drive txi l1 l2) ∷ f) σ tripsTaken w = execute' f σ tripsTaken 
                                                             (σ (drive txi l1 l2)
                                                                 {getGender txi}
                                                                 {tripsTaken} 
                                                                {agnostic tt}
                                                                 w)
execute' halt σ tripsTaken w = inj₁ w  

canonical-σ : Context → GenderAwareActionHandler
canonical-σ Γ α = σα (effects (Γ α))

\end{code}
