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
open import Data.Maybe
open import Agda.Builtin.FromNat

open import TaxiDomain
open import Fuel.FuelAwareActionHandler

open import Plans.GrammarTypes taxiDomain hiding (¬_)
open import Plans.PCPlansTyped taxiDomain

module Fuel.ExampleProblem  where

-- Action Context which defines the preconditions and effects of Actions.

open import Plans.Domain.Core Type Action Predicate

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


--Here we give a fuel level 1 higher than needed as the σα' function takes 1 energy to initialise
finalState : World ⊎ OutOfFuelError
finalState = (executeWithFuel planₜ (enriched-σ Γ)
  (updateWorld' initialState ([] , fuel 4)))

{-
finalStateError : OutOfFuelError
finalStateError = from-inj₂ (executeWithFuel planₜ (enriched-σ Γ) (σα' initialState ([] , fuel 3)))
-}
