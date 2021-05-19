-- Alasdair Hill
-- This file defines Planning languages as types, plans as prrof terms approach to PDDL

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level
open import Agda.Builtin.Nat hiding (_*_ ; _+_ ; _-_; zero)
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product
open import Data.Maybe
open import Relation.Nullary

open import Plans.Domain

--------------------------------------------------------
--  Definition of formulae, possible world semantics, actions, plans
--
-- The following module declarations allows to develop the file parametrised on an abstract domain.

module Plans.PCPlansTyped (domain : Domain) where

open Domain domain
open import Plans.GrammarTypes domain
open import Plans.MembershipAndStateTyped domain
open import Plans.Subtyping PredMap isSame

---------------------------------------------------------------
-- Figure 10: well-typing relation
--

open ActionDescription using (preconditions; effects)
    
data _⊢_∶_↝_ : Context → Plan → State → State → Set where
  halt : ∀{Γ currentState  goalState} → currentState <: goalState
             → Γ ⊢ halt ∶ currentState ↝ goalState
  seq : ∀{α currentState goalState Γ f}
      →  currentState <: preconditions (Γ α)
      -- -> validS (M₁ ⊔N effects (Γ α))
      → Γ ⊢ f ∶ currentState ⊔N effects (Γ α) ↝ goalState
      → Γ ⊢ (α ∷ f) ∶ currentState ↝ goalState
      
---------------------------------------------------------------

--We could create an error data type for errors
solver : (Γ : Context) -> (f : Plan) -> (P Q : State) ->  Maybe (Γ ⊢ f ∶ P ↝ Q)
solver Γ (x ∷ f) P Q with P <:? (preconditions (Γ x)) 
... | no ¬p = nothing
... | yes p with solver Γ f (P ⊔N (effects (Γ x))) Q
... | nothing = nothing
... | just x₁ = just (seq p x₁)
solver Γ halt P Q with P <:? Q
... | no ¬p = nothing
... | yes p = just (halt p)
