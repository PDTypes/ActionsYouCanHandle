open import Data.Product
open import Data.List

module Plans.Domain.Core (Type : Set) (Action : Set) (Predicate : Set) where

data Polarity : Set where
  + - : Polarity

neg : Polarity → Polarity
neg + = -
neg - = +

-- A pair containing a predicate and polarity
PredMap : Set
PredMap = Polarity × Predicate

-- A list containing pairs of polarities and predicates
State : Set
State = List PredMap

Preconditions : Set
Preconditions = State

Effects : Set
Effects = State

Goal : Set
Goal = State 

record ActionDescription : Set where
  field
    preconditions : Preconditions
    effects       : Effects

Context : Set
Context = Action → ActionDescription
