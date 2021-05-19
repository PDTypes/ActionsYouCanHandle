open import Relation.Binary

module Plans.Domain where

record Domain : Set₁ where
  field
    Type : Set
    Action : Set
    Predicate : Set
    
    _≟ₚ_ : DecidableEquality Predicate

