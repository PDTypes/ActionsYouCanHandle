open import Relation.Binary
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (¬_)
open import Data.Product renaming (_,_ to _↝_)
open import Data.Product
open import Data.List hiding (any)
open import Data.Empty
open import Data.List.Relation.Unary.Any

open import Plans.Domain

module Plans.Proofs.Soundness_Of_Evaluation (domain : Domain) where

open Domain domain
open import Plans.Semantics domain
open import Plans.Plan domain 
open import Plans.MembershipAndStateTyped domain
open import Plans.ActionHandler domain
open import Plans.Proofs.Possible_World_Soundness domain
open ActionDescription

_↓₊ : Form → State
P ↓₊ = P ↓[ + ] []
 
sound : ∀{σ w Γ f N}
      → WfHandler Γ σ
      → Γ ⊢ f ∶ w ↝ N
      → execute f σ w ∈⟨ N ⟩
sound x (halt w∈⟨N⟩) = w∈⟨N⟩
sound wfh (seq {α} {w} w∈⟨P⟩ tr) rewrite wfh w∈⟨P⟩
  = sound wfh tr

sound' : ∀{σ w Γ f Q}
              → WfHandler Γ σ
              → Γ ⊢ f ∶ w ↝ (Q ↓₊)
              → execute f σ w ⊨[ + ] Q
sound' wfh ti = ↓-sound (sound wfh ti)

-------------------------------------------------------------

-- Proposition 1: The canonical handler is well-formed
wf-canonical-σ : ∀ Γ → WfHandler Γ (canonical-σ Γ)
wf-canonical-σ Γ₁ x = refl

------------------------------------------------------------

