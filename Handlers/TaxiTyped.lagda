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
open import Gender
open import Examples.TaxiDomainWithProofs

-- Is it possible to access the superset of (C taxi) considering it is finite.
-- Otherwise I think I have to use lists which are slightly less nice.

--_/_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
--m / (suc n) = div-helper 0 n m n

{- 
NonZero : ℕ → Set
NonZero zero    = ⊥
NonZero (suc x) = ⊤

-- Constructors

≢-nonZero : ∀ {n} → n ≢ 0 → NonZero n
≢-nonZero {zero}  0≢0 = 0≢0 refl
≢-nonZero {suc n} n≢0 = tt

>-nonZero : ∀ {n} → n > 0 → NonZero n
>-nonZero (s≤s 0<n) = tt -}
--(≢0 : False (lowerbound ≟ 0)

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

-- Canonical Handler
canonical-σ : Context → ActionHandler
canonical-σ Γ α = σα (effects (Γ α))

--Evalutation Function
execute : Plan → ActionHandler → World → World
execute (α ∷ f) σ w = execute f σ (σ α w)
execute halt σ w = w

--List size is total number of taxi's e.g (length xs)

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

-- assignments = (tripsTaken gender * 100) / totalTripsTaken --gives percentage of trips taken for a gender
-- lowerbound = (percentage of gender) - (percentage of gender / 4) --give a lower bound for assignments 
-- We simply need to check (assignments > lowerbound) for all genders)


-- totalTripsTaken has to be > 0 for division


-- If there is 10 people then we want to have 100 trips taken before enforcing this otherwise the variance will
-- be too low.

--What happens if a gender has 0 people in the list?



{- 
isFair3 : (g : Gender) -> (f : (Gender -> Nat)) -> (prf : False (totalTripsTaken f Data.Nat.≟ 0)) -> (_/_ (f g * 100) (totalTripsTaken f) {prf}) > (_-_ (percentage g) (_/_ (percentage g) lowerbound {≢0}))
isFair3 x f prf = {!!}



fairForAll2 : (Gender -> Nat) -> Nat 
fairForAll2 f with totalTripsTaken f >? (totalDrivers * 10) -- needs to be greater than so we know that trips taken is greater than 0
... | no ¬p = {!!}
... | yes p = {!!}
  where
    prf = help (totalTripsTaken f) (totalDrivers * 10) p -}




open import Agda.Builtin.Unit
 
gZero : (n m : Nat) -> n > m ->  False (n Data.Nat.≟ 0)
gZero .(suc _) m (s≤s x) = tt



 
open import Agda.Builtin.Unit


-- True if the action does not affect the number of trips taken
TripAgnostic : Action -> Set
TripAgnostic (drivePassenger t p1 l1 l2) = ⊥
TripAgnostic (drive t l1 l2) = ⊤

open import Data.String hiding (_<_ ; _<?_)


--data Error : Set where
--  notProportional : (f : Gender -> Nat) -> ¬(isFairForAll f) -> Error

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

{-
⟦_⟧₃ : Plan -> ActionHandlerTaxi
            -> (tripsTaken : (Gender -> Nat))
            -> World
            -> World ⊎ Error
⟦ ((drivePassenger txi p1 l1 l2) ∷ f) ⟧₃ σ tripsTaken w with isFairForAll? (incTripsG (getGender txi) tripsTaken) 
... | no ¬p = inj₂ (notProportional (drivePassenger txi p1 l1 l2) ((incTripsG (getGender txi) tripsTaken)) ¬p) --inj₂ (notProportional _ ¬p)
... | yes p =  ⟦ f ⟧₃ σ (incTripsG (getGender txi) tripsTaken) 
                                                             (σ (drivePassenger txi p1 l1 l2)
                                                                 {getGender txi}
                                                                 {tripsTaken}
                                                                 {inj₂ p}
                                                                 w)
⟦ ((drive txi l1 l2) ∷ f) ⟧₃ σ tripsTaken w = ⟦ f ⟧₃ σ tripsTaken 
                                                             (σ (drive txi l1 l2)
                                                                 {getGender txi}
                                                                 {tripsTaken} 
                                                                {inj₂ tt}
                                                                 w)
⟦ halt ⟧₃ σ tripsTaken w = inj₁ w  
-}

canonical-σ₃ : Context → GenderAwareActionHandler
canonical-σ₃ Γ α = σα (effects (Γ α))

----------------------------------------------------------------------------------------------------------------

data Fuel : Nat → Set where
  fuel : (n : Nat) → Fuel n

EnergyValue : Fuel n → Nat
EnergyValue {n} x = n

FuelAwareActionHandler : Set
FuelAwareActionHandler = ∀ {n} → Action
                      → World × Fuel (suc n)
                      → World × Fuel n


data OutOfFuelError : Set where
  error : Action -> World -> OutOfFuelError

-- implementing an actual handler of this type future work
executeWithFuel : Plan → FuelAwareActionHandler
             → World × Fuel n
             → World ⊎ OutOfFuelError
executeWithFuel (α ∷ f) σ (w , (fuel zero)) = inj₂ (error α w)
executeWithFuel (α ∷ f) σ (w , (fuel (suc n))) =
            executeWithFuel f σ (σ α (w , (fuel (suc n))))
executeWithFuel halt σ (w , e) = inj₁ w

getWorld : World × Fuel n -> World
getWorld (w , e) = w


-- World constructor from state
σα' : State →  World × Fuel (suc n)
            → World × Fuel n
σα' [] (w , e) = w , fuel _
σα' ((+ , s) ∷ S) w = (s ∷ getWorld (σα' S w)) , fuel _
σα' ((- , s) ∷ S) w = remove s (getWorld (σα' S w)) , fuel _

enriched-σ : Context → FuelAwareActionHandler
enriched-σ Γ α = σα' (effects (Γ α ))


{-
⟦_⟧₆ : Plan ->  actionHandler -> World × Energy n -> Maybe (World × Nat)
⟦ α ∷ f ⟧₆ σ (w , (fuel zero)) = nothing
⟦ α ∷ f ⟧₆ σ (w , (fuel (suc n))) = ⟦ f ⟧₆ σ (σ α (w , (fuel (suc n))))
⟦ halt ⟧₆ σ (w , e) = just (w , EnergyValue e)
-}



------------------------------------------------------------------------------------------------------------------
\end{code}

ActionHandler4 : Set
ActionHandler4 = (α : Action)
                -> {g : Gender}
                -> {tripsTaken : (Gender -> Nat)}
                -> {isFairForAll (incTripsG g tripsTaken) ⊎ TripAgnostic α}
                -> World -> World

-- We can probably remove this notion of the list of taxis
-- Is there any way we can figure this informaation out from the getGender function

⟦_⟧₄ : Plan -> ActionHandler4
            -> (tripsTaken : (Gender -> Nat))
            -> World
            -> Maybe World
⟦ ((drivePassenger txi p1 l1 l2) ∷ f) ⟧₄ σ tripsTaken w with decFair (incTripsG (getGender txi) tripsTaken) 
... | no ¬p = nothing
... | yes p =  ⟦ f ⟧₄ σ (incTripsG (getGender txi) tripsTaken) 
                                                             (σ (drivePassenger txi p1 l1 l2)
                                                                 {getGender txi}
                                                                 {tripsTaken}
                                                                 {inj₁ p}
                                                                 w)
⟦ ((drive txi l1 l2) ∷ f) ⟧₄ σ tripsTaken w = ⟦ f ⟧₄ σ tripsTaken 
                                                             (σ (drive txi l1 l2)
                                                                 {getGender txi}
                                                                 {tripsTaken}
                                                                 {inj₂ tt}
                                                                 w)
⟦ halt ⟧₄ σ tripsTaken w = just w

-- Canonical Handler
canonical-σ₄ : Γ → ActionHandler4
canonical-σ₄ Γ α = σα (effects (Γ α))

⟦_⟧₅ : Plan -> ActionHandler4
            -> (tripsTaken : (Gender -> Nat))
            -> World
            -> World  ⊎ Error
⟦ ((drivePassenger txi p1 l1 l2) ∷ f) ⟧₅ σ tripsTaken w with decFair (incTripsG (getGender txi) tripsTaken) 
... | no ¬p = inj₂ (notProportional ((incTripsG (getGender txi) tripsTaken)) ¬p) --inj₂ (notProportional _ ¬p)
... | yes p =  ⟦ f ⟧₅ σ (incTripsG (getGender txi) tripsTaken) 
                                                             (σ (drivePassenger txi p1 l1 l2)
                                                                 {getGender txi}
                                                                 {tripsTaken}
                                                                 {inj₁ p}
                                                                 w)
⟦ ((drive txi l1 l2) ∷ f) ⟧₅ σ tripsTaken w = ⟦ f ⟧₅ σ tripsTaken 
                                                             (σ (drive txi l1 l2)
                                                                 {getGender txi}
                                                                 {tripsTaken} 
                                                                {inj₂ tt}
                                                                 w)
⟦ halt ⟧₅ σ tripsTaken w = inj₁ w
