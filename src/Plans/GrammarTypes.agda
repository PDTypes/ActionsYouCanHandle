open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product

open import Plans.Domain

module Plans.GrammarTypes  (domain : Domain) where

open Domain domain

data Form : Set where
  _∧_ : Form → Form → Form
  ¬_ : Predicate  → Form
  atom : Predicate → Form
infixl 4 _∧_
infixl 5 ¬_

--------------------------------------------------------
-- Figure 4. Possible worlds 
--

World : Set
World = List Predicate


--------------------------------------------------------
-- Figure 6. Declarative (possible world) semantics
-- 

-- Entailment Relation
infix 3 _⊨[_]_
data _⊨[_]_ : World → Polarity → Form → Set where
  flip : ∀{w t A} → w ⊨[ neg t ] (atom A) → w ⊨[ t ] ¬ A
  both : ∀{w t P Q} → w ⊨[ t ] P → w ⊨[ t ] Q → w ⊨[ t ] P ∧ Q
  somewhere : ∀{w a} → a ∈ w → w ⊨[ + ] atom a
  nowhere : ∀{w a} → a ∉ w → w ⊨[ - ] atom a

-- Operational Semantics: normalisation function
infixr 3 _↓[_]_
_↓[_]_ : Form → Polarity → State → State
P ∧ Q ↓[ t ] N = Q ↓[ t ] P ↓[ t ] N
¬ x ↓[ t ] N = (neg t , x) ∷ N
atom x ↓[ t ] N = (t , x) ∷ N

---------------------------------------------------------------
-- Figure 7: Plans
--

data Plan : Set where
  _∷_ : Action → Plan → Plan
  halt : Plan

--------------------------------------------------------

-- Relation between NPred and World
_∈⟨_⟩ : World → State → Set
w ∈⟨ N ⟩ = (∀ a → (+ , a) ∈ N → a ∈ w) × (∀ a → (- , a) ∈ N → a ∉ w)

-- Convert a State to a World
stateToWorld : State  -> World
stateToWorld [] = []
stateToWorld ((+ , a) ∷ S) = a ∷ stateToWorld S
stateToWorld ((- , a) ∷ S) = stateToWorld S
