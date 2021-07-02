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
  error : Action → World → OutOfFuelError

-- implementing an actual handler of this type future work
executeWithFuel : Plan →
                  FuelAwareActionHandler →
                  World × Fuel n →
                  World ⊎ OutOfFuelError
executeWithFuel halt    σ (w , e)              = inj₁ w
executeWithFuel (α ∷ f) σ (w , fuel 0)         = inj₂ (error α w)
executeWithFuel (α ∷ f) σ s@(w , fuel (suc _)) = executeWithFuel f σ (σ α s)

getWorld : World × Fuel n → World
getWorld (w , e) = w

-- World constructor from state
updateWorld' : Effect → World × Fuel (suc n) → World × Fuel n
updateWorld' s (w , fuel (suc e)) = updateWorld s w , fuel e

enriched-σ : Context → FuelAwareActionHandler
enriched-σ Γ α = updateWorld' (effects (Γ α ))

-- Proposition 1: The canonical handler is well-formed
wf-canonical-σ : ∀ Γ → WfHandler Γ (canonical-σ Γ)
wf-canonical-σ Γ₁ x = refl

