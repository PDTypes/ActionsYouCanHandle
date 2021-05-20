\begin{code}
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.List.Membership.Propositional
open import Level
open import Data.Product
open import Relation.Nullary
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.List hiding (any)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there)
open Data.Product renaming (_,_ to _↝_)
open import Relation.Nullary

open import Plans.Domain

module Plans.MembershipAndStateTyped (domain : Domain) where

open Domain domain
open import Plans.Semantics domain


-- New Definitions Of Membership -----------------------------------------------------------------

--Defining above using Any instead
_atom≡_ : (a : Predicate) (p : PredMap) → Set
a atom≡ s = a ≡ proj₂ s

_∈S_ : (a : Predicate) (s : State) → Set
a ∈S s = Any (a atom≡_) s
  
-- Is an atom not in a State
_∉S_ : (a : Predicate) (s : State) → Set
a ∉S s = Relation.Nullary.¬ (a ∈S s)

isInState  : (a : Predicate) → (s : State) → Dec (a ∈S s)
isInState a s = any? (λ x → a ≟ₚ proj₂ x) s

------------------------------------------------------------------------------------------------

-- A State is valid if there is no duplicate predicates in the State.
validState : State → Set
validState [] = ⊤
validState ((t , At') ∷ s) with isInState At' s
validState ((t , At') ∷ s) | yes p = ⊥
validState ((t , At') ∷ s) | no ¬p = validState s

--Decidability of State validity
decValidState : (s : State) → Dec (validState s)
decValidState [] = yes tt
decValidState ((t , At') ∷ s) with isInState At' s
decValidState ((t , At') ∷ s) | yes p =  no λ ()
decValidState ((t , At') ∷ s) | no ¬p = decValidState s

-- Decidablity of polarities
decZ : DecidableEquality Polarity
decZ + + = yes refl
decZ + - = no (λ ())
decZ - + = no (λ ())
decZ - - = yes refl

-- Decidablity of PredMaps
isSame : DecidableEquality PredMap
isSame (z , a) (z' , a') with decZ z z' | a ≟ₚ a'
isSame (z ↝ a) (.z ↝ .a) | yes refl | yes refl = yes refl
isSame (z ↝ a) (.z ↝ a') | yes refl | no ¬p = no λ { refl → ¬p refl}
isSame (z ↝ a) (z' ↝ a') | no ¬p | yes p = no λ { refl → ¬p refl}
isSame (z ↝ a) (z' ↝ a') | no ¬p | no ¬p₁ = no λ { refl → ¬p refl}


del : Predicate → State → State
del x [] = []
del x ((t' , x') ∷ M) with x ≟ₚ x'
del x ((t' , x') ∷ M) | yes p =  del x M
del x ((t' , x') ∷ M) | no ¬p = (t' , x') ∷ del x M

del-spec : ∀ t x N → (t , x) ∉ del x N
del-spec t x [] ()
del-spec t x ((t' , y) ∷ N) tx∈N' with x ≟ₚ y
del-spec t x ((t' , y) ∷ N) tx∈N' | yes p = del-spec t x N tx∈N'
del-spec .t' .y ((t' , y) ∷ N) (here refl) | no ¬p = ¬p _≡_.refl
del-spec t x ((t' , y) ∷ N) (there tx∈N') | no ¬p =  del-spec t x N tx∈N'


del-∈ : ∀{M y x} → x ∈ del y M → x ∈ M
del-∈ {[]}             ()
del-∈ {(t , z) ∷ M}{y} x∈ with y ≟ₚ z
del-∈ {(t , z) ∷ M} {y} x∈ | yes p = there (del-∈ x∈)
del-∈ {(t , z) ∷ M} {y} (here refl) | no ¬p = here _≡_.refl
del-∈ {(t , z) ∷ M} {y} (there x∈) | no ¬p = there (del-∈ x∈)


-- Override operator
_⊔N_ : State → State → State
P ⊔N [] = P
P ⊔N ((z , q) ∷ Q) = (z , q) ∷ del q P ⊔N Q
\end{code}
