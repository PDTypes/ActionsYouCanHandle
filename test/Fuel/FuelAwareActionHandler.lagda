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
open import Relation.Nullary.Decidable
open import Relation.Nullary
open import Data.Maybe

open import TaxiDomain

open import Plans.Plan taxiDomain
open import Plans.Semantics taxiDomain
open import Plans.ActionHandler taxiDomain
open ActionDescription

module Fuel.FuelAwareActionHandler where

variable
  n m : ℕ

----------------------------------------------------------------------------------------
-- Fuel example

data Fuel : ℕ → Set where
  fuel : (n : ℕ) → Fuel n

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
updateWorld' : State → World × Fuel (suc n) → World × Fuel n
updateWorld' s (w , fuel (suc e)) = updateWorld s w , fuel e

enriched-σ : Context → FuelAwareActionHandler
enriched-σ Γ α = updateWorld' (effects (Γ α ))

\end{code}
