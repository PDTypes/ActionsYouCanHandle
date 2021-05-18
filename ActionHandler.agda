open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.List hiding (any)
open import Relation.Nullary

module ActionHandler (Action : Set) (Predicate : Set) (Type : Set) (Object : Type -> Set) (isDE : IsDecEquivalence {A = Predicate} (_≡_) )
      where

<<<<<<< HEAD
open import GrammarTypes Action Predicate Type Object 
open import MembershipAndStateTyped Action Predicate Type Object isDE 
open import Subtyping PredMap isSame hiding (State)
=======
open import GrammarTypes Action R Type C 
open import MembershipAndStateTyped Action R Type C isDE 
open import Subtyping PredMap isSame using (_<:_)
>>>>>>> efa175fd680b15a32a2f4e99c2f7d8d7a1dd4ce6
                                              
-- Action Handler
ActionHandler : Set
ActionHandler = Action → World → World

-- Evalutation function
execute : Plan → ActionHandler → World → World
execute (α ∷ f) σ w = execute f σ (σ α w)
execute halt σ w = w

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
  ∀{α P} →  P <: preconditions (Γ α) → ∀{w} → w ∈⟨ P ⟩ → σ α w ∈⟨ P ⊔N effects (Γ α) ⟩

