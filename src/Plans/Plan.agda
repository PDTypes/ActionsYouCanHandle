open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product
open import Data.Maybe
open import Relation.Nullary

open import Plans.Domain

--------------------------------------------------------
--  Definition of plans
--
-- The following module declarations allows to develop
-- the file parametrised on an abstract domain.

module Plans.Plan (domain : Domain) where

open Domain domain
open import Plans.Semantics domain
open import Plans.MembershipAndStateTyped domain
open import Plans.Subtyping PredMap isSame
open import Plans.ActionHandler domain
open ActionDescription using (preconditions; effects)

---------------------------------------------------------------
-- Plans

data Plan : Set where
  _∷_ : Action → Plan → Plan
  halt : Plan

---------------------------------------------------------------
-- Well-typing relation over plans
    
data _⊢_∶_↝_ : Context → Plan → State → State → Set where
  halt : ∀{Γ currentState  goalState} → currentState <: goalState
             → Γ ⊢ halt ∶ currentState ↝ goalState
  seq : ∀{α currentState goalState Γ f}
      →  currentState <: preconditions (Γ α)
      -- -> validS (M₁ ⊔N effects (Γ α))
      → Γ ⊢ f ∶ currentState ⊔N effects (Γ α) ↝ goalState
      → Γ ⊢ (α ∷ f) ∶ currentState ↝ goalState
      
---------------------------------------------------------------
-- Checks if a plan is well-typed

solver : (Γ : Context) (f : Plan) (P Q : State) → Maybe (Γ ⊢ f ∶ P ↝ Q)
solver Γ (x ∷ f) P Q with P <:? (preconditions (Γ x)) 
... | no ¬p = nothing
... | yes p with solver Γ f (P ⊔N (effects (Γ x))) Q
... | nothing = nothing
... | just x₁ = just (seq p x₁)
solver Γ halt P Q with P <:? Q
... | no ¬p = nothing
... | yes p = just (halt p)

---------------------------------------------------------------
-- Evaluate a plan

execute : Plan → ActionHandler → World → World
execute (α ∷ f) σ w = execute f σ (σ α w)
execute halt σ w = w
