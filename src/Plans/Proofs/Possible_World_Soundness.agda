open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (¬_)
open import Data.Product as Prod
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List hiding (any)
open import Data.List.Properties
open import Data.Empty

open import Plans.Domain

module Plans.Proofs.Possible_World_Soundness (domain : Domain) where

open Domain domain
open import Plans.Semantics domain

--------------------------------------------------------
-- Code for the Soundness and Completeness proofs
--
-- We first prove some auxiliary lemmas:

weakeningH : ∀ t₁ t₂ P Q N a → (t₁ , a) ∈ (P ↓[ t₂ ] N) → (t₁ , a) ∈ (Q ↓[ t₂ ] P ↓[ t₂ ] N)
weakeningH t₁ t₂ P (Q ∧ Q₁) N a x = weakeningH t₁ t₂ Q Q₁ (P ↓[ t₂ ] N) a (weakeningH t₁ t₂ P Q N a x)
weakeningH t₁ t₂ P (¬ x₁) N a x = there x
weakeningH t₁ t₂ P (atom x₁) N a x = there x

--
-- ∈⟨⟩-weakeningH
--
∈⟨⟩-weakeningH : ∀ w t P Q N → w ∈⟨ Q ↓[ t ] P ↓[ t ] N ⟩ → (w ∈⟨ P ↓[ t ] N ⟩)
∈⟨⟩-weakeningH w t P Q N (pos , neg)
  = (λ a1 x → pos a1 (weakeningH + t P Q N a1 x))
  , (λ a1 x x2 → neg a1 (weakeningH - t P Q N a1 x) x2)

lemma-transport-r : ∀ t P M N →
  ((P ↓[ t ] M) ++ N) ≡ (P ↓[ t ] (M ++ N))
lemma-transport-r t (P ∧ Q) M N = trans
  (lemma-transport-r t Q (P ↓[ t ] M) N)
  (cong (λ x → Q ↓[ t ] x) (lemma-transport-r t P M N))
lemma-transport-r t (¬ A) M N = refl
lemma-transport-r t (atom x) M N = refl


--newer stdlib

lemma-transport-l : ∀ t P M N →
  (M ++ (P ↓[ t ] N)) ≡ ((M ++ (P ↓[ t ] [])) ++ N)
lemma-transport-l t (P ∧ P₁) M N
  = sym (trans (++-assoc M (P₁ ↓[ t ] P ↓[ t ] []) N)
               (cong (λ x → M ++ x)
                     (trans (lemma-transport-r t P₁ (P ↓[ t ] []) N)
                            (cong (λ x → P₁ ↓[ t ] x) (lemma-transport-r t P [] N)))))
lemma-transport-l t (¬ x) M N = sym (++-assoc M (((neg t) , x) ∷ []) N)
lemma-transport-l t (atom x) M N = sym (++-assoc M ((t , x) ∷ []) N)

∈-transport-l : ∀ a {t1} t P M N → (t1 , a) ∈ ( M ++ (P ↓[ t ] N))
  → (t1 , a) ∈ ((M ++ (P ↓[ t ] [])) ++ N)
∈-transport-l a₁ {t₁} t P M N x
  = subst ((t₁ , a₁) ∈_) (lemma-transport-l t P M N) x



∈-transport-r : ∀ a {t1} t P M N → (t1 , a) ∈ ((M ++ (P ↓[ t ] [])) ++ N)
  → (t1 , a) ∈ ( M ++ (P ↓[ t ] N))
∈-transport-r a₁ t P M N x
  = subst (_ ∈_) ((sym (lemma-transport-l t P M N))) x

--
-- exchange for the underlying representation (was cAny)
--
∈-exchange : ∀ a {t} t1 t2 P Q N1 N2 → (t , a) ∈ ( N1 ++ (P ↓[ t1 ] Q ↓[ t2 ] N2))
  → (t , a) ∈ (N1 ++ (Q ↓[ t2 ] P ↓[ t1 ] N2))
∈-exchange a₁ t1 t2 P (Q ∧ R) N1 N2 x
  = ∈-transport-r a₁ t2 R N1 (Q ↓[ t2 ] P ↓[ t1 ] N2)
      (∈-exchange a₁ t1 t2 P Q (N1 ++ (R ↓[ t2 ] [])) N2
            (∈-transport-l a₁ t2 R N1 (P ↓[ t1 ] Q ↓[ t2 ] N2)
                             (∈-exchange a₁ t1 t2 P R N1 (Q ↓[ t2 ] N2) x)))
∈-exchange a₁ t1 t2 (P ∧ Q) (¬ A) N1 N2 x
  = ∈-exchange a₁ t1 t2 Q (¬ A) N1 (P ↓[ t1 ] N2)
    (∈-transport-r a₁ t1 Q N1 ((¬ A) ↓[ t2 ] P ↓[ t1 ] N2)
      (∈-exchange a₁ t1 t2 P (¬ A) (N1 ++ (Q ↓[ t1 ] [])) N2
        (∈-transport-l a₁ t1 Q N1 (P ↓[ t1 ] (¬ A) ↓[ t2 ] N2) x)))
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) [] N2 (here px) = there (here px)
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) (x₂ ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) (x₂ ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) N1 N2 x)
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) [] N2 (here px) = there (here px)
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) (x₂ ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) (x₂ ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (atom x₁) (¬ A) N1 N2 x)
∈-exchange a₁ t1 t2 (P ∧ Q) (atom x₁) N1 N2 x
  = ∈-exchange a₁ t1 t2 Q (atom x₁) N1 (P ↓[ t1 ] N2)
    (∈-transport-r a₁ t1 Q N1 ((atom x₁) ↓[ t2 ] P ↓[ t1 ] N2)
      (∈-exchange a₁ t1 t2 P (atom x₁) (N1 ++ (Q ↓[ t1 ] [])) N2
        (∈-transport-l a₁ t1 Q N1 (P ↓[ t1 ] (atom x₁) ↓[ t2 ] N2) x)))
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) [] N2 (here px) = there (here px)
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) (x₂ ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) (x₂ ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (¬ A) (atom x₁) N1 N2 x)
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) [] N2 (here refl) = there (here refl)
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) ((t3 , x₃) ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) ((t3 , x₃) ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) N1 N2 x)

--
-- ∈⟨⟩-exchange lemma
--
-- a wrapper around ∈-exchange
--
∈⟨⟩-exchange : ∀ w t1 t2 P Q N1 N2 → w ∈⟨ N1 ++ (P ↓[ t1 ] Q ↓[ t2 ] N2) ⟩
  → w ∈⟨ N1 ++ (Q ↓[ t2 ] P ↓[ t1 ] N2) ⟩
∈⟨⟩-exchange w t1 t2 P (Q ∧ R) N1 N2 (fst , snd)
  = (λ { a₁ x₁ → fst a₁ (∈-exchange a₁ t2 t1 R P N1 (Q ↓[ t2 ] N2)
       (∈-transport-r a₁ t2 R N1 (P ↓[ t1 ] Q ↓[ t2 ] N2)
         (∈-exchange a₁ t2 t1  Q P  (N1 ++ (R ↓[ t2 ] [])) N2
           (∈-transport-l a₁ t2 R N1 (Q ↓[ t2 ] P ↓[ t1 ] N2) x₁))))})
  , (λ { a₁ x x₁ → snd a₁
       ( ∈-exchange a₁ t2 t1 R P N1 (Q ↓[ t2 ] N2)
         (∈-transport-r a₁ t2 R N1 (P ↓[ t1 ] Q ↓[ t2 ] N2)
           (∈-exchange a₁ t2 t1 Q P  (N1 ++ (R ↓[ t2 ] [])) N2
             (∈-transport-l a₁ t2 R N1 (Q ↓[ t2 ] P ↓[ t1 ] N2) x)))  )
      x₁})
∈⟨⟩-exchange w t1 t2 P (¬ A) N1 N2 (fst , snd)
  = (λ {a₁ x₁ → fst a₁ (∈-exchange a₁ (neg t2) t1 (atom A) P N1 N2 x₁)})
  , (λ {a₁ x x₁ → snd a₁ (∈-exchange a₁ (neg t2) t1 (atom A) P N1 N2 x) x₁})
∈⟨⟩-exchange w t1 t2 P (atom x₁) N1 N2 (fst , snd)
  = (λ {a₁ x → fst a₁ (∈-exchange a₁ t2 t1 (atom x₁) P N1 N2 x)})
  , (λ {a₁ x x₂ → snd a₁ (∈-exchange a₁ t2 t1 (atom x₁) P N1 N2 x) x₂})

--
-- soundness of operational semantics 
--
↓-sound : ∀{w t P} → w ∈⟨ P ↓[ t ] [] ⟩ → w ⊨[ t ] P
↓-sound {w} {t} {P ∧ Q} x
  = both (↓-sound (∈⟨⟩-weakeningH w t P Q [] x))
         (↓-sound (∈⟨⟩-weakeningH w t Q P [] (∈⟨⟩-exchange w t t Q P [] [] x )))
↓-sound {w} {+} {¬ A} (proj1 , proj2) = flip (nowhere (proj2 A (here refl)))
↓-sound {w} { - } {¬ A} (proj1 , proj2) = flip (somewhere (proj1 A (here (refl))))
↓-sound {w} {+} {atom p} (proj1 , proj2) = somewhere (proj1 p (here refl))
↓-sound {w} { - } {atom p} (proj1 , proj2) = nowhere (proj2 p (here refl))

↓-complete : ∀{w t P} → w ⊨[ t ] P → w ∈⟨ P ↓[ t ] [] ⟩
↓-complete {w} {t} p = go p ((λ _ ()) , (λ _ ())) 
  where
  go : ∀{t P z} → w ⊨[ t ] P → w ∈⟨ z ⟩ → w ∈⟨ P ↓[ t ] z ⟩
  go {t}   {x ∧ y}  {z} (both eq eq₁) v = go eq₁ (go eq v)
  go {t}   {¬ x}    {z} (flip eq)     v = go eq v
  go { + } {atom a} {z} (somewhere x) v = s , u
    where s : ∀ d → (+ , d) ∈ (+ , a) ∷ z → d ∈ w
          s d (here  refl) = x
          s d (there ins)  = proj₁ v d ins

          u : ∀ d → (- , d) ∈ (+ , a) ∷ z → d ∉ w
          u d (there ins) = proj₂ v d ins
  go { - } {atom a} {z} (nowhere x) v = s , u
    where s : ∀ d → (+ , d) ∈ (- , a) ∷ z → d ∈ w
          s d (there ins)  = proj₁ v d ins

          u : ∀ d → (- , d) ∈ (- , a) ∷ z → d ∉ w
          u d (here  refl) = x
          u d (there ins)  = proj₂ v d ins
  
