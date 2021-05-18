open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Gender where

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
