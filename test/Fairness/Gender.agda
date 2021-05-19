open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat
open import Data.List
open import Data.Fin.Patterns

open import TaxiDomain

module Fairness.Gender where

data Gender : Set where
  male female other : Gender

decGender : (x y : Gender) -> Dec (x ≡ y)
decGender male male = yes refl
decGender male female = no (λ ())
decGender male other = no (λ ())
decGender female male = no (λ ())
decGender female female = yes refl
decGender female other = no (λ ())
decGender other male = no (λ ())
decGender other female = no (λ ())
decGender other other = yes refl

-- Assign all taxis to a gender
getGender : Object taxi -> Gender
getGender (taxi 0F) = male
getGender (taxi 1F) = female
getGender (taxi 2F) = male


-- return the number of taxis of a specific gender 
noGender : Gender -> ℕ
noGender g = length (filter (λ t → decGender g (getGender t)) allTaxis)
