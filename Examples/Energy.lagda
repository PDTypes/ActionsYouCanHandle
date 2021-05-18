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
open import Relation.Nullary
open import Data.Maybe


module Examples.Energy where
variable
  n m : Nat

open import GrammarTypes Action Predicate Type Object hiding (¬_)

----------------------------------------------------------------------------------------


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
σα' : State →  World × Fuel (suc n)
            → World × Fuel n
σα' [] (w , e) = w , fuel _
σα' ((+ , s) ∷ S) w = (s ∷ getWorld (σα' S w)) , fuel _
σα' ((- , s) ∷ S) w = remove s (getWorld (σα' S w)) , fuel _

enriched-σ : Context → FuelAwareActionHandler
enriched-σ Γ α = σα' (effects (Γ α ))

\end{code}
