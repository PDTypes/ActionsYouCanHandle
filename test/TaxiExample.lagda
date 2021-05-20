\begin{code}
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Unit
open import Data.Maybe
open import Agda.Builtin.FromNat

open import TaxiDomain
open import Plans.GrammarTypes taxiDomain
open import Plans.Plan taxiDomain
open import Plans.ActionHandler taxiDomain

module TaxiExample where

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

