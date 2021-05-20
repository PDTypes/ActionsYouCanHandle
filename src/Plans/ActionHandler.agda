open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List hiding (any)
open import Relation.Nullary

open import Plans.Domain

module Plans.ActionHandler (domain : Domain) where

open Domain domain
open import Plans.Semantics domain 
open import Plans.MembershipAndStateTyped domain
open import Plans.Subtyping PredMap isSame 

-- Action Handler
ActionHandler : Set
ActionHandler = Action → World → World

-- Well formed handler

{-
  If we have an action α in gamma
  And has preconditions proj₁ (Γ α) and postconditions proj₂ (Γ α)
  proj₁ (Γ α) is a subtype of M
  and M is true in the world w
  then the application of the action handler σ of action α
  results in M being overriden by proj₂ (Γ α) in w
-}
open ActionDescription

WfHandler : Context → ActionHandler → Set
WfHandler Γ σ =
  ∀{α P} →  P <: preconditions (Γ α) → ∀ {w} → w ∈⟨ P ⟩ → σ α w ∈⟨ P ⊔N effects (Γ α) ⟩

-- Remove a predicate R from a world.
remove : Predicate → World → World
remove x [] = []
remove x (y ∷ w) with x ≟ₚ y
remove x (y ∷ w) | yes p = remove x w
remove x (y ∷ w) | no ¬p = y ∷ remove x w

-- Update a world with the changes in a state
updateWorld : State → World → World
updateWorld [] w = w
updateWorld ((+ , x) ∷ N) w = x ∷ updateWorld N w
updateWorld ((- , x) ∷ N) w = remove x (updateWorld N w)

canonical-σ : Context → ActionHandler
canonical-σ Γ α = updateWorld (effects (Γ α))

