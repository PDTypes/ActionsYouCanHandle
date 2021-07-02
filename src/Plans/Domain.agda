open import Relation.Binary

import Plans.Domain.Core as DomainCore

module Plans.Domain where

record Domain : Set₁ where
  field
    Type      : Set
    Predicate : Set
    Action    : Set

  open DomainCore Type Action Predicate public

  field
    Γ    : Context
    _≟ₚ_ : DecidableEquality Predicate
