-- Alasdair Hill
-- This file defines Planning languages as types, plans as prrof terms approach to PDDL

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

--------------------------------------------------------
--  Definition of formulae, possible world semantics, actions, plans

--
-- The following module declarartion allows to develop the file parametrised on an abstract set R of predicates
-- an an abstract set A of declared actions. The former must have decidable equivalence.

module PCPlansTyped (Action : Set) (Predicate : Set) (Type : Set) (Object : Type -> Set) (isDE : IsDecEquivalence {A = Predicate} (_≡_) ) where

-- R is a predicate

open import Agda.Builtin.Nat hiding (_*_ ; _+_ ; _-_; zero)
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product

open import GrammarTypes Action Predicate Type Object
open import MembershipAndStateTyped Action Predicate Type Object isDE 
open import Subtyping PredMap isSame hiding (State)

---------------------------------------------------------------
-- Figure 10: well-typing relation
--

{-
record ActionDescription : Set where
  field
    preconditions : NPred
    effects : NPred -}

preconditions = ActionDescription.preconditions
effects = ActionDescription.effects
    
data _⊢_∶_↝_ : Context → Plan → State → State → Set where
  halt : ∀{Γ currentState  goalState} → currentState <: goalState
             → Γ ⊢ halt ∶ currentState ↝ goalState
  seq : ∀{α currentState goalState Γ f}
      →  currentState <: preconditions (Γ α)
      -- -> validS (M₁ ⊔N effects (Γ α))
      → Γ ⊢ f ∶ currentState ⊔N effects (Γ α) ↝ goalState
      → Γ ⊢ (α ∷ f) ∶ currentState ↝ goalState
      
---------------------------------------------------------------

open import Data.Maybe
open import Relation.Nullary

--We could create an error data type for errors
solver : (Γ₁ : Context) -> (f : Plan) -> (P : State) -> (Q : State) ->  Maybe (Γ₁ ⊢ f ∶ P ↝ Q)
solver Γ₁ (x ∷ f) P Q with decSub (preconditions (Γ₁ x)) P
... | no ¬p = nothing
... | yes p with solver Γ₁ f (P ⊔N (effects (Γ₁ x))) Q
... | nothing = nothing
... | just x₁ = just (seq p x₁)
solver Γ₁ halt P Q with decSub Q P
... | no ¬p = nothing
... | yes p = just (halt p)

{- open import Data.String hiding (_≟_)

solver2 : (Γ₁ : Γ) -> (f : Plan) -> (P : NPred) -> (Q : NPred) -> (Γ₁ ⊢ f ∶ P ↝ Q) ⊎ (Action ⊎ String)
solver2 Γ₁ (doAct x f) P Q with decSub (proj₁ (Γ₁ x)) P
... | no ¬p = inj₂ (inj₁ x)
... | yes p with solver2 Γ₁ f (P ⊔N (proj₂ (Γ₁ x))) Q
... | inj₁ x₁ = inj₁ (seq p x₁)
... | inj₂ (inj₁ x₁) = inj₂ (inj₁ x₁)
... | inj₂ (inj₂ y) = inj₂ (inj₂ y) --this case should be impossible
solver2 Γ₁ halt P Q with decSub Q P
... | no ¬p = inj₂ (inj₂ "Subtype Halt Issue") --giving an action here does not make sense and is impossible. Need to create some sort of error datatype.
... | yes p = inj₁ (halt p)

-}
