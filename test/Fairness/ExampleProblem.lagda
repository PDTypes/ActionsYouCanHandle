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
open import Data.List
open import Data.Fin
open import Function.Base
open import Relation.Nullary.Decidable
open import Data.Unit
open Data.Product
open import Agda.Builtin.FromNat using (Number)
open import Data.Maybe
open import Data.Nat
open import Data.Fin.Patterns
import Data.Nat.Literals as NatLiterals
import Data.Fin.Literals as FinLiterals

open import TaxiDomain
open import Fairness.Gender

open import Plans.ActionHandler taxiDomain
open import Plans.Semantics taxiDomain
open import Plans.Plan taxiDomain

module Fairness.ExampleProblem  where

instance
  NumNat : Number ℕ
  NumNat = NatLiterals.number
  
instance
  NumFin : ∀ {n} → Number (Fin n)
  NumFin {n} = FinLiterals.number n
  

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



-- The below function asks us to construct in our type system that applying plan₁ to P entails Q given the context Γ₁
-- This has been proven true in our type system using our automated solver function.
Derivation : Γ ⊢ planₜ ∶ initialState ↝ goalState
Derivation = from-just (solver Γ planₜ initialState goalState)

-- percentage of variance allowed for lowerbound
-- 100/4= 25%

-- Assign all taxis to a gender
driverGender : Object taxi → Gender
driverGender (taxi 0F) = male
driverGender (taxi 1F) = female
driverGender (taxi 2F) = male

open import Fairness.GenderAwareActionHandler driverGender 4 

tripsTaken : Gender → ℕ
tripsTaken x = 0

finalState : World
finalState = from-inj₁ (execute' planₜ (enriched-σ Γ) tripsTaken (updateWorld initialState []))

-------------------------------------------------------------------------------

--30
-- 66% assigned
-- 50%
tripsTaken2 : Gender → ℕ
tripsTaken2 male = 30
tripsTaken2 female = 11
tripsTaken2 other = 0

finalState2 : World
finalState2 = from-inj₁ (execute' planₜ (enriched-σ Γ) tripsTaken2 (updateWorld initialState []))

--------------------------------------------------------------------------------------------

tripsTaken3 : Gender → ℕ
tripsTaken3 male = 30
tripsTaken3 female = 9
tripsTaken3 other = 0

finalStateError : Error
finalStateError = from-inj₂ (execute' planₜ (enriched-σ Γ) tripsTaken3 (updateWorld initialState []))

open import Data.String

displayErrorMessage : (String × Action)
displayErrorMessage = errorMessage finalStateError

\end{code}
