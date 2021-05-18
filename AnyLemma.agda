open import Data.List
open import Level

module _ {a} {p} {A : Set a} {P : A → Set p} where

  open import Data.List.Relation.Unary.Any public
  open import Data.List.Relation.Unary.Any.Properties
  open import Data.Sum

  ++⁻[] : ∀ {P} {N : List A} -> Any {a} {p} P (N ++ []) -> Any {a} P N
  ++⁻[] {P} {N} x with (++⁻ N x) 
  ++⁻[] {_} {_} x | inj₁ x₁ = x₁
  ++⁻[] {_} {_} x | inj₂ ()

  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary

  any-cong : ∀ {P} {M N : List A} → Any {a} {p} P M → M ≡ N  → Any {a} P N
  any-cong (here px) refl = here px
  any-cong (there x) refl = there x 

  
