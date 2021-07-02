open import Data.Product
open import Data.Sum
open import Data.Fin
open import Data.List
open import Data.Nat
open import Data.Unit
open Data.Product
open import Data.Maybe
open import Agda.Builtin.FromNat using (Number)
open import Function.Base
open import Relation.Nullary.Decidable
import Data.Nat.Literals as NatLiterals
import Data.Fin.Literals as FinLiterals

open import TaxiDomain
open import Fuel.FuelAwareActionHandler

open import Plans.Semantics taxiDomain
open import Plans.Plan taxiDomain

module Fuel.ExampleProblem  where

instance
  NumNat : Number ℕ
  NumNat = NatLiterals.number
  
instance
  NumFin : ∀ {n} → Number (Fin n)
  NumFin {n} = FinLiterals.number n



open import Plans.MembershipAndStateTyped taxiDomain

initialWorld : World
initialWorld =
  taxiIn (taxi 0) (location 0) ∷
  taxiIn (taxi 1) (location 1) ∷
  taxiIn (taxi 2) (location 2) ∷
  personIn (person 0) (location 0) ∷
  personIn (person 1) (location 1) ∷
  personIn (person 2) (location 2) ∷
  []

goalState : Goal
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

Derivation : Γ ⊢ planₜ ∶ initialWorld ↝ goalState
Derivation = from-just (solver Γ planₜ initialWorld goalState)

finalState : World
finalState = from-inj₁ (executeWithFuel planₜ (enriched-σ Γ) (initialWorld , (fuel 3)))

finalStateError : OutOfFuelError
finalStateError = from-inj₂ (executeWithFuel planₜ (enriched-σ Γ) (initialWorld , fuel 2))
