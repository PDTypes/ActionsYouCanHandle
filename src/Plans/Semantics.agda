open import Data.List
open import Data.List.Membership.Propositional
open import Data.Product

open import Plans.Domain

module Plans.Semantics (domain : Domain) where

open Domain domain

--------------------------------------------------------
-- Possible worlds 

World : Set
World = List Predicate

-- Relation between World and State
_∈⟨_⟩ : World → State → Set
w ∈⟨ S ⟩ = (∀ a → (+ , a) ∈ S → a ∈ w) ×
           (∀ a → (- , a) ∈ S → a ∉ w)

--------------------------------------------------------
-- Figure 6. Declarative and operational semantics

data Form : Set where
  _∧_ : Form → Form → Form
  ¬_ : Predicate  → Form
  atom : Predicate → Form
infixl 4 _∧_
infixl 5 ¬_

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

