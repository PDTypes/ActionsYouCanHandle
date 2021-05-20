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
open import Relation.Nullary
open import Data.Maybe

open import TaxiDomain

open import Plans.GrammarTypes taxiDomain hiding (¬_)

module Fuel.FuelAwareActionHandler where

variable
  n m : Nat

----------------------------------------------------------------------------------------
open import Plans.Domain.Core Type Action Predicate

effects = ActionDescription.effects

ActionHandler : Set
ActionHandler = Action -> World -> World

open IsDecEquivalence  isDecidable renaming (_≟_ to _≟ᵣ_)

-- Remove a predicate R from a world.
remove : Predicate → World → World
remove x [] = []
remove x (y ∷ w) with x ≟ᵣ y
remove x (y ∷ w) | yes p = remove x w
remove x (y ∷ w) | no ¬p = y ∷ remove x w

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
updateWorld : State → World → World
updateWorld [] w = w
updateWorld ((+ , x) ∷ N) w = x ∷ updateWorld N w
updateWorld ((- , x) ∷ N) w = remove x (updateWorld N w)

updateWorld' : State →  World × Fuel (suc n)
            → World × Fuel n
updateWorld' [] (w , e) = w , fuel _
updateWorld' ((+ , s) ∷ S) (w , fuel (suc n))
  = s ∷ (updateWorld S w) , fuel n 
updateWorld' ((- , s) ∷ S) (w , fuel (suc n))
  = remove s (updateWorld S w) , fuel n

enriched-σ : Context → FuelAwareActionHandler
enriched-σ Γ α = updateWorld' (effects (Γ α ))

\end{code}
