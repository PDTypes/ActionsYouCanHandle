open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product as Product
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
open import Plans.ActionHandler domain
open ActionDescription using (preconditions; effects)

---------------------------------------------------------------
-- Plans

data Plan : Set where
  _∷_ : Action → Plan → Plan
  halt : Plan

---------------------------------------------------------------
-- Well-typing relation over plans
--todo add valid state to initial state 
    
data _⊢_∶_↝_ : Context → Plan → World → Goal → Set where
  halt : ∀{Γ currentWorld  goalState} → currentWorld ∈⟨ goalState ⟩
             → Γ ⊢ halt ∶ currentWorld ↝ goalState
  seq : ∀{α currentWorld goalState Γ f}
      →  currentWorld  ∈⟨ preconditions (Γ α) ⟩
      → Γ ⊢ f ∶ updateWorld (effects (Γ α)) currentWorld ↝ goalState
      → Γ ⊢ (α ∷ f) ∶ currentWorld ↝ goalState
      
---------------------------------------------------------------
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Data.List.Membership.DecSetoid using (_∈?_)
--open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any


help : (a : Predicate) -> (w : World) -> Dec (a ∈ w)
help = _∈?_ (record { Carrier = Predicate ; _≈_ = _≡_ ; isDecEquivalence = record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans } ; _≟_ = _≟ₚ_ } })

relation? : (w : World) -> (S : State) -> Dec (w ∈⟨ S ⟩)
relation? w [] = yes ((λ x ()) , (λ x ()))
relation? w ((+ , a) ∷ S) with help a w
... | no ¬p = no (λ z → ¬p (proj₁ z a (here _≡_.refl)))
... | yes p with relation? w S
... | no ¬p = no (λ { (fst , snd) → ¬p ((λ x x₁ → fst x (there x₁)) , (λ x x₁ → snd x (there x₁)))})
... | yes (pa , pb) = yes ((λ { a₁ (here _≡_.refl) → p ; a₁ (there x) → pa a₁ x}) , λ { a₁ (there x) (here _≡_.refl) → pb a₁ x  (here _≡_.refl) ; a₁ (there x) (there x₁) → pb a₁ x (there x₁)})
relation? w ((- , a) ∷ S) with help a w
... | yes p = no λ { (fst , snd) → snd a (here _≡_.refl) p}
... | no ¬p with relation? w S
... | no ¬p₁ = no (λ { (fst , snd) → ¬p₁ ((λ x x₁ → fst x (there x₁)) , (λ x x₁ → snd x (there x₁)))})
... | yes (pa , pb) = yes ((λ { a₁ (there x) → pa a₁ x}) , λ { a₁ (here _≡_.refl) (here _≡_.refl) → ¬p (here _≡_.refl) ; a₁ (there x) (here _≡_.refl) → pb a₁ x (here _≡_.refl) ; a₁ (here _≡_.refl) (there x₁) → ¬p (there x₁) ; a₁ (there x) (there x₁) → pb a₁ x  (there x₁)})


solver : (Γ : Context) -> (f : Plan) -> (w : World) -> (g : State) ->  Maybe (Γ ⊢ f ∶ w ↝ g)
solver Γ (x ∷ f) w g with relation? w (preconditions (Γ x))
... | no ¬p = nothing
... | yes p with solver Γ f (updateWorld (effects (Γ x)) w) g
...   | nothing = nothing
...   | just x₁ = just (seq p x₁)
solver Γ halt w g with relation? w g
... | no ¬p = nothing
... | yes p = just (halt p)

---------------------------------------------------------------
-- Evaluate a plan

execute : Plan → ActionHandler → World → World
execute (α ∷ f) σ w = execute f σ (σ α w)
execute halt    σ w = w
