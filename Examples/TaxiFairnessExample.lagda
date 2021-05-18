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
open import Examples.Gender
open import Relation.Nullary.Decidable
open import Data.Unit
open Data.Product
open import Examples.TaxiDomain
open import GrammarTypes Action Predicate Type Object hiding (¬_)
open import PCPlansTyped Action Predicate Type Object isDecidable
open import Agda.Builtin.FromNat
open import Data.Maybe

module Examples.TaxiFairnessExample  where

-- Action Context which defines the preconditions and effects of Actions.

Γ : Context
Γ (drivePassenger t1 p1 l1 l2) =
  record {
    preconditions = (+ , taxiIn t1 l1) ∷
                    (+ , personIn p1 l1) ∷ [] ;
                    
    effects = (- , taxiIn t1 l1) ∷
              (- , personIn p1 l1) ∷
              (+ , taxiIn t1 l2) ∷
              (+ , personIn p1 l2) ∷ [] }
Γ (drive t1 l1 l2) =
  record {
    preconditions = (+ , taxiIn t1 l1) ∷ [] ;
    effects = (- , taxiIn t1 l1) ∷
              (+ , taxiIn t1 l2) ∷ [] }





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

open import ActionHandler Action Predicate Type Object isDecidable

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



-- Relation between NPred and World
--_∈⟨_⟩ : World → NPred → Set
--w ∈⟨ N ⟩ = (∀ a → (+ , a) ∈ N → a ∈ w) × (∀ a → (- , a) ∈ N → a ∉ w)



{-
helper : (a : R) -> (N : State) -> (+ , a) ∈ N -> a ∈ (σα N [])
helper = {!!}


postulate
  implicit-consistency-assumption : (t : Polarity) (x : R) → ∀ N → (t , x) ∈ N → (neg t , x) ∉ N

σα-insert : ∀{N x} → (+ , x) ∈ N → ∀ w → x ∈ σα N w
σα-insert = {!!}

σα-delete : ∀{x N} → (- , x) ∈ N → ∀ w → x ∉ σα N w
σα-delete = {!!}

stateToWorldConversionSound : (N : State) -> (σα N []) ∈⟨ N ⟩
stateToWorldConversionSound [] = (λ { a ()}) , λ { a () x₁}
stateToWorldConversionSound ((+ , a) ∷ N) = (λ { a₁ (here refl) → here refl ; a₁ (there x) → there (σα-insert x [])})
                                          , λ a₁ x x₁ → σα-delete x [] x₁
stateToWorldConversionSound ((- , a) ∷ N) = (λ { a₁ (there x) → σα-insert (there x) []})
                                              , λ {a₁ x x₁ → σα-delete x [] x₁}

-}


































--testMe : (P : Form) -> w ⊨[ + ] P
--testMe = ?





{-
-- The below function asks us to construct in our type system that applying plan₁ to P entails Q given the context Γ₁
-- This has been proven true in our type system using our automated solver function.
proofOfPlan : Γ₁ ⊢ plan₁ ∶ P ↝ Q
proofOfPlan = from-just (solver Γ₁ plan₁ P Q)

-- percentage of variance allowed for lowerbound
-- 100/4= 25%
open import Tutorial.TaxiTyped getGender noOfGender 4 tt

-- Convert a State to a World


----------------------------------------------------------------------------------------
-- Exaluating plan₁ on the initial state P given the simple ActionHandler.
world-eval : World
world-eval = (⟦ plan₁ ⟧ (canonical-σ Γ₁) (stateToWorld P))

{- Output of world-eval
isIn taxi3 location3 ∷
isIn person1 location3 ∷
isIn person3 location1 ∷
isIn taxi1 location2 ∷
isIn taxi2 location2 ∷ isIn person2 location2 ∷ []
-}

---------------------------------------------------------------------------------------

tripsTaken : Gender -> Nat
tripsTaken x = 0

world-eval-test : World
world-eval-test = from-just (⟦ plan₁ ⟧₄ (canonical-σ₄ Γ₁) tripsTaken (stateToWorld P))

--30
-- 66% assigned
-- 50%
tripsTaken2 : Gender -> Nat
tripsTaken2 male = 30
tripsTaken2 female = 11
tripsTaken2 other = 0



-- male
-- 40 > 30
-- 20 * 100 / 40 = 50
-- 2 * 100 / 3 = 66 --.66  66/4 = 16 therefore lowerbound = 50 so ok

-- setting tripstaken male to 18 will fail the condition for men in this case

world-eval-test2 : World
world-eval-test2 = from-just (⟦ plan₁ ⟧₄ (canonical-σ₄ Γ₁) tripsTaken2 (stateToWorld P))

--female
-- 25 is the lowrbound for female in this example so setting it to 10 and men to 30 and other to 0 will break the code 


tripsTaken3 : Gender -> Nat
tripsTaken3 male = 30
tripsTaken3 female = 9
tripsTaken3 other = 0

world-eval-test3 : Error 
world-eval-test3 = from-inj₂ (⟦ plan₁ ⟧₅ (canonical-σ₄ Γ₁) tripsTaken3 (stateToWorld P))

{- 
Tutorial.TaxiTyped.Error.notProportional
(λ g1 →
   Tutorial.TaxiTyped.incTripsG getGender noOfGender 4 tt male
   tripsTaken3 g1
   | decGender male g1)
(λ x → x) -}


--world-eval-test4 : Error2 
--world-eval-test4 = from-inj₂ (⟦ plan₁ ⟧₂ (canonical-σ₂ Γ₁) tripsTaken3 (stateToWorld P))

{- 
Tutorial.TaxiTyped.Error2.notProportional
(λ g1 →
   Tutorial.TaxiTyped.incTripsG getGender noOfGender 4 tt male
   tripsTaken3 g1
   | decGender male g1)
(λ { () }) -}

open import Data.String
{-
world-eval-test5 : String × Action
world-eval-test5 = errorMessage2 (from-inj₂ (⟦ plan₁ ⟧₂ (canonical-σ₂ Γ₁) tripsTaken3 (stateToWorld P))) -}

world-eval-test6 : String × Action
world-eval-test6 = errorMessage3 (from-inj₂ (⟦ plan₁ ⟧₃ (canonical-σ₃ Γ₁) tripsTaken3 (stateToWorld P)))

world-eval-test4 : Error3
world-eval-test4 = from-inj₂ (⟦ plan₁ ⟧₃ (canonical-σ₃ Γ₁) tripsTaken3 (stateToWorld P))






{-
-- Evaluating plan₁ on the initial state P given ActionHandler₂ where we update the function ourselver.
world-eval-function : World
world-eval-function = from-just (⟦ plan₁ ⟧₂ (canonical-σ₂ Γ₁) numberOfTrips (stateToWorld P))

-- Both of evaluations return the same world 
testEqual : world-eval ≡ world-eval-function
testEqual = refl

----------------------------------------------------------------------------------------

--Also works with handler where driving is agnostic to trips.
world-eval-function-ag : World
world-eval-function-ag = from-just (⟦ plan₁ ⟧₃ (canonical-σ₃ Γ₁) numberOfTrips (stateToWorld P))

-- Both of evaluations return the same world 
testEqual2 : world-eval ≡ world-eval-function-ag
testEqual2 = refl

----------------------------------------------------------------------------------------
-- Here is an example where the function should fail

numberOfTripsFail : C taxi -> Nat
numberOfTripsFail taxi1 = 2
numberOfTripsFail taxi2 = 2
numberOfTripsFail taxi3 = 2

open import Data.Bool

world-eval-function-fail : Maybe World  
world-eval-function-fail = (⟦ plan₁ ⟧₂ (canonical-σ₂ Γ₁) numberOfTripsFail (stateToWorld P))

world-eval-function-fail-proof : (⟦ plan₁ ⟧₂ (canonical-σ₂ Γ₁) numberOfTripsFail (stateToWorld P)) ≡ nothing
world-eval-function-fail-proof = refl 

-}

-}

\end{code}
