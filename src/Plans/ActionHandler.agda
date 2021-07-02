open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List hiding (any)
open import Relation.Nullary

open import Plans.Domain

module Plans.ActionHandler (domain : Domain) where

open import Plans.Semantics domain 
open Domain domain
open ActionDescription

-- Action Handler
ActionHandler : Set
ActionHandler = Action → World → World

-- Remove a predicate R from a world.
remove : Predicate → World → World
remove x [] = []
remove x (y ∷ w) with x ≟ₚ y
... | yes _ = remove x w
... | no  _ = y ∷ remove x w

-- Update a world with the changes in a state
updateWorld : Effects → World → World
updateWorld []            w = w
updateWorld ((+ , x) ∷ N) w = x ∷ updateWorld N w
updateWorld ((- , x) ∷ N) w = remove x (updateWorld N w)

canonical-σ : Context → ActionHandler
canonical-σ Γ α = updateWorld (effects (Γ α))

-- Well formed handler

{-
  If we have an action α in gamma
  And has preconditions proj₁ (Γ α) and postconditions proj₂ (Γ α)
  proj₁ (Γ α) is a subtype of M
  and M is true in the world w
  then the application of the action handler σ of action α
  results in M being overriden by proj₂ (Γ α) in w
-}
WfHandler : Context → ActionHandler → Set
WfHandler Γ σ =
  ∀{α w} → w ∈⟨ preconditions (Γ α) ⟩
         → σ α w ≡ updateWorld (effects (Γ α)) w 
