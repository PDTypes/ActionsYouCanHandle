\begin{code}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.List hiding (any)
open import Relation.Nullary hiding (¬_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Agda.Builtin.Nat hiding (_+_ ; _-_)
open import Data.List
open import Function.Base
open import Relation.Nullary.Decidable
open import Data.Unit
open Data.Product
open import Agda.Builtin.FromNat
open import Data.Maybe

open import TaxiDomain

open import Plans.GrammarTypes taxiDomain hiding (¬_)
open import Plans.PCPlansTyped taxiDomain
open import Plans.ActionHandler taxiDomain

module TaxiExample where

-- Action Context which defines the preconditions and effects of Actions.




initialState : State
initialState =
  (+ , taxiIn (taxi 0) (location 0)) ∷
  (+ , taxiIn (taxi 1) (location 1)) ∷
  (+ , taxiIn (taxi 2) (location 2)) ∷
  (+ , personIn (person 0) (location 0)) ∷
  (+ , personIn (person 1) (location 1)) ∷
  (+ , personIn (person 2) (location 2)) ∷
  []

goalState : State
goalState =
  (+ , taxiIn (taxi 0) (location 1)) ∷
  (+ , personIn (person 0) (location 2)) ∷
  (+ , personIn (person 2) (location 0)) ∷
  []

planₜ : Plan
planₜ = (drive (taxi 0) (location 0) (location 1)) ∷
        (drivePassenger (taxi 2) (person 2) (location 2) (location 0)) ∷
        (drivePassenger (taxi 2) (person 0) (location 0) (location 2)) ∷
        halt


Derivation : Γ ⊢ planₜ ∶ initialState ↝ goalState
Derivation = from-just (solver Γ planₜ initialState goalState)

finalState : World
finalState = execute planₜ (canonical-σ Γ) (σα initialState [])

{-
Output:
  taxiIn taxi3 location3 ∷
  personIn person1 location3 ∷
  personIn person3 location1 ∷
  taxiIn taxi1 location2 ∷
  taxiIn taxi2 location2 ∷
  personIn person2 location2 ∷ []
-}

