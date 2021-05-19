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
open import Plans.GrammarTypes domain
open import Plans.PCPlansTyped domain 
open import Plans.MembershipAndStateTyped domain
open import Plans.Subtyping PredMap isSame 
open import Plans.ActionHandler domain
open import Plans.Proofs.Possible_World_Soundness domain

<:-resp-∈ : ∀{N M} → M <: N → ∀{w} → w ∈⟨ M ⟩ → w ∈⟨ N ⟩
<:-resp-∈ {[]} {M} []<:N w∈⟨M⟩ = (λ _ ()) , λ _ ()
<:-resp-∈ {x ∷ N} {M} M<:x∷N {w} w∈⟨M⟩ = lt , rt where
  ih : w ∈⟨ N ⟩
  ih = <:-resp-∈ (weakSub _ _ _ M<:x∷N) w∈⟨M⟩
  
  lt : ∀ a' → (+ , a') ∈ x ∷ N → a' ∈ w
  lt a' (here refl) =  proj₁ w∈⟨M⟩ a' (M<:x∷N (here refl))
  lt a' (there +a'∈N) = proj₁ ih a' +a'∈N

  rt : ∀ a' → (- , a') ∈ x ∷ N → a' ∉ w
  rt a' (here refl) a'∈w = proj₂ w∈⟨M⟩ a' (M<:x∷N (here refl)) a'∈w
  rt a' (there -a'∈N) a'∈w = proj₂ ih a' -a'∈N a'∈w 

---------------------------------------------------------------
-- Theorem 2: Soundness of evaluation of normalised formula
--

open ActionDescription

sound : ∀{w σ M Γ f N}
      → WfHandler Γ σ
      → Γ ⊢ f ∶ M ↝ N
      → w ∈⟨ M ⟩
      → execute f σ w ∈⟨ N ⟩
sound wfσ (halt N<:M) w∈⟨M⟩ = <:-resp-∈ N<:M w∈⟨M⟩
sound {w}{σ}{M}{Γ} wfσ (seq {α}{M₁} M₁'<:M Γ⊢f∶M⊔M₂↝N) w∈⟨M⟩ =
  sound wfσ Γ⊢f∶M⊔M₂↝N σαw∈⟨M⊔NM₂⟩
  where σαw∈⟨M⊔NM₂⟩ : σ α w ∈⟨ M ⊔N effects (Γ α) ⟩
        σαw∈⟨M⊔NM₂⟩ = wfσ M₁'<:M w∈⟨M⟩

---------------------------------------------------------------
-- Theorem 3: Soundness of evaluation
--

sound' : ∀{Γ f P Q σ}
       → WfHandler Γ σ
       → Γ ⊢ f ∶ (P ↓₊) ↝ (Q ↓₊)
       → ∀{w} → w ⊨[ + ] P
       → execute f σ w ⊨[ + ] Q
sound' {Γ}{f}{P}{Q}{σ} wfσ Γ⊢f∶P↓₊↝Q↓₊ {w} w⊨₊P = ↓-sound h
  where h : execute f σ w ∈⟨ Q ↓₊ ⟩
        h = sound wfσ Γ⊢f∶P↓₊↝Q↓₊ (↓-complete w⊨₊P) 
