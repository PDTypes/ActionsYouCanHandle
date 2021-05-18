open import Data.List hiding (any)
open import Data.Product
import Data.List.Relation.Binary.Subset.Propositional as Subset
import Data.List.Relation.Binary.Subset.Propositional.Properties as Subset
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any
open import Relation.Nullary
open import Relation.Binary

module Subtyping (A : Set) (decA : DecidableEquality A) where

open import Data.List.Membership.DecPropositional decA

private
  State = List A

-- Subtyping
infix 3 _<:_
_<:_ : State → State → Set
_<:_ = Subset._⊇_

-- Extension of subtyping
<:atom : (P Q : State) -> (s : A) -> P <: Q -> s ∷ P <: Q
<:atom P Q s P<Q = Subset.++⁺ (λ ()) P<Q

-- Reflexivity of subtyping
reflSub : (S : State) -> S <: S
reflSub S = Subset.⊆-refl

-- Transitivity of subtyping
transSub : (L : State) -> (M : State) -> (N : State) -> M <: L -> N <: M -> N <: L
transSub L M N = Subset.⊆-trans

-- Weakening of subtyping
weakSub : (s : A) -> (P : State) -> (Q : State) ->  Q <: (s ∷ P)  -> Q <: P
weakSub s P Q Q<sP x∈P = Q<sP (there x∈P)

isSameInState : (s : A) -> (S : State) -> Dec (s ∈ S)
isSameInState s S = any? (λ x → decA s x) S

_<:?_ : Decidable _<:_
_<:?_ xs [] = yes λ()
_<:?_ xs (y ∷ ys) with y ∈? xs | xs <:? ys
... | yes y∈xs | yes xs<ys = yes (λ { (here refl) → y∈xs ; (there v) → xs<ys v })
... | no  y∉xs | _         = no (λ xs<y∷ys → y∉xs (xs<y∷ys (here refl)))
... | _        | no xs≮ys  = no (λ xs<y∷ys → xs≮ys (weakSub _ _ _ xs<y∷ys))
