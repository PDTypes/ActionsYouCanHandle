open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (¬_)
open import Data.Product
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.List hiding (any)

module Proofs.Possible_World_Soundness (Action : Set) (R : Set) (Type : Set) (C : Type -> Set) where

open import GrammarTypes Action R Type C 

--------------------------------------------------------
-- Code for the Soundness and Completeness proofs
--
-- We first prove some auxiliary lemmas:

weakeningH : ∀ t₁ t₂ P Q N a -> (t₁ , a) ∈ (P ↓[ t₂ ] N) -> (t₁ , a) ∈ (Q ↓[ t₂ ] P ↓[ t₂ ] N)
weakeningH t₁ t₂ P (Q ∧ Q₁) N a x = weakeningH t₁ t₂ Q Q₁ (P ↓[ t₂ ] N) a (weakeningH t₁ t₂ P Q N a x)
weakeningH t₁ t₂ P (¬ x₁) N a x = there x
weakeningH t₁ t₂ P (atom x₁) N a x = there x

--
-- ∈⟨⟩-weakeningH
--
∈⟨⟩-weakeningH : ∀ w t P Q N -> w ∈⟨ Q ↓[ t ] P ↓[ t ] N ⟩ -> (w ∈⟨ P ↓[ t ] N ⟩)
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


-- older stdlib
{-
open import Algebra
++-assoc :  (x x₁ x₂ : List ( Polarity × R)) →  (x ++ x₁) ++ x₂ ≡ x ++ x₁ ++ x₂
++-assoc = Monoid.assoc (monoid (Polarity × R))-}

--newer stdlib
open import Data.List.Properties


lemma-transport-l : ∀ t P M N →
  (M ++ (P ↓[ t ] N)) ≡ ((M ++ (P ↓[ t ] [])) ++ N)
lemma-transport-l t (P ∧ P₁) M N
  = sym (trans (++-assoc M (P₁ ↓[ t ] P ↓[ t ] []) N)
               (cong (λ x → M ++ x)
                     (trans (lemma-transport-r t P₁ (P ↓[ t ] []) N)
                            (cong (λ x → P₁ ↓[ t ] x) (lemma-transport-r t P [] N)))))
lemma-transport-l t (¬ x) M N = sym (++-assoc M (((neg t) , x) ∷ []) N)
lemma-transport-l t (atom x) M N = sym (++-assoc M ((t , x) ∷ []) N)

open import Level

∈-transport-l : ∀ a {t1} t P M N -> (t1 , a) ∈ ( M ++ (P ↓[ t ] N))
  -> (t1 , a) ∈ ((M ++ (P ↓[ t ] [])) ++ N)
∈-transport-l a₁ {t₁} t P M N x
  = subst ((t₁ , a₁) ∈_) (lemma-transport-l t P M N) x



∈-transport-r : ∀ a {t1} t P M N -> (t1 , a) ∈ ((M ++ (P ↓[ t ] [])) ++ N)
  -> (t1 , a) ∈ ( M ++ (P ↓[ t ] N))
∈-transport-r a₁ t P M N x
  = subst (_ ∈_) ((sym (lemma-transport-l t P M N))) x

--
-- exchange for the underlying representation (was cAny)
--
∈-exchange : ∀ a {t} t1 t2 P Q N1 N2 -> (t , a) ∈ ( N1 ++ (P ↓[ t1 ] Q ↓[ t2 ] N2))
  -> (t , a) ∈ (N1 ++ (Q ↓[ t2 ] P ↓[ t1 ] N2))
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
∈⟨⟩-exchange : ∀ w t1 t2 P Q N1 N2 -> w ∈⟨ N1 ++ (P ↓[ t1 ] Q ↓[ t2 ] N2) ⟩
  -> w ∈⟨ N1 ++ (Q ↓[ t2 ] P ↓[ t1 ] N2) ⟩
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


open import Data.Sum

strengthening : ∀ t₁ t₂ P Q N a -> (t₁ , a) ∈ (Q ↓[ t₂ ] P ↓[ t₂ ] N)
  -> ((t₁ , a) ∈ (Q ↓[ t₂ ] N)) ⊎  ((t₁ , a) ∈ (P ↓[ t₂ ] N))
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x
  with strengthening t₁ t₂ Q₁ Q₂ (P₁ ↓[  t₂ ] P ↓[ t₂ ] N) a x
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁
  with strengthening t₁ t₂ Q₂ P₁ (P ↓[ t₂ ] N) a (∈-exchange a t₂ t₂ Q₂ P₁ [] (P ↓[ t₂ ] N) x₁)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₁ x₂ = inj₂ x₂
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₂ y
  with strengthening t₁ t₂ P Q₂ N a y
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₂ y | inj₁ x₂
  = inj₁ (∈-exchange a t₂ t₂ Q₁ Q₂ [] N (weakeningH t₁ t₂ Q₂ Q₁ N a x₂))
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₂ y | inj₂ y₁
  = inj₂ (weakeningH t₁ t₂ P P₁ N a y₁)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y
  with strengthening t₁ t₂ Q₁ P₁ (P ↓[ t₂ ] N) a (∈-exchange a t₂ t₂ Q₁ P₁ [] (P ↓[ t₂ ] N) y)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₁ x₂ = inj₂ x₂
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₂ y₂
  with strengthening t₁ t₂ P Q₁ N a y₂
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₂ y₂ | inj₁ x₁ = inj₁ (weakeningH t₁ t₂ Q₁ Q₂ N a x₁)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₂ y₂ | inj₂ y₁ = inj₂ (weakeningH t₁ t₂ P P₁ N a y₁)
strengthening t₁ t₂ (¬ x₁) (Q₁ ∧ Q₂) N a x with ∈-exchange a t₂ t₂ (Q₁ ∧ Q₂) (¬ x₁) [] N x
strengthening t₁ t₂ (¬ x₁) (Q₁ ∧ Q₂) N a x | here px = inj₂ (here px)
strengthening t₁ t₂ (¬ x₁) (Q₁ ∧ Q₂) N a x | there res = inj₁ res
strengthening t₁ t₂ (atom x₁) (Q₁ ∧ Q₂) N a x with ∈-exchange a t₂ t₂ (Q₁ ∧ Q₂) (atom x₁) [] N x
strengthening t₁ t₂ (atom x₁) (Q₁ ∧ Q₂) N a x | here px = inj₂ (here px)
strengthening t₁ t₂ (atom x₁) (Q₁ ∧ Q₂) N a x | there res = inj₁ res
strengthening t₁ t₂ P (¬ x₁) N a (here px) = inj₁ (here px)
strengthening t₁ t₂ (P ∧ P₁) (¬ x₁) N a (there x) = inj₂ x
strengthening t₁ t₂ (¬ x₂) (¬ x₁) N a (there (here px)) = inj₂ (here px)
strengthening t₁ t₂ (¬ x₂) (¬ x₁) N a (there (there x)) = inj₁ (there x)
strengthening t₁ t₂ (atom x₂) (¬ x₁) N a (there (here px)) = inj₂ (here px)
strengthening t₁ t₂ (atom x₂) (¬ x₁) N a (there (there x)) = inj₁ (there x)
strengthening t₁ t₂ P (atom x₁) N a (here px) = inj₁ (here px)
strengthening t₁ t₂ P (atom x₁) N a (there x) = inj₂ x

helperPos :  ∀ w t P Q N a → (w ∈⟨ P ↓[ t ] N ⟩) -> (w ∈⟨ Q ↓[ t ] N ⟩)
           -> (+ , a) ∈ (Q ↓[ t ] P ↓[ t ] N)
           -> a ∈ w
helperPos w t P Q N a x x1 x2 with (strengthening + t P Q N) a x2
helperPos w t P Q N a x x1 x2 | inj₁ y = proj₁ x1 a y
helperPos w t P Q N a x x1  x2 | inj₂ y = proj₁ x a y

open import Data.Empty

helperNeg : ∀ w t P Q N a → (w ∈⟨ P ↓[ t ] N ⟩) -> (w ∈⟨ Q ↓[ t ] N ⟩)
            -> (- , a) ∈ (Q ↓[ t ] P ↓[ t ] N)
            -> a ∉ w
helperNeg w t P Q N a x x1 x2 x3 with (strengthening - t P Q N) a x2
helperNeg w t P Q N a x x1 x2 x3 | inj₁ y = proj₂ x1 a y x3
helperNeg w t P Q N a x x1 x2 x3 | inj₂ y = proj₂ x a y x3


∈⟨⟩-strengthening : ∀ w t P Q N -> (w ∈⟨ P ↓[ t ] N ⟩) -> (w ∈⟨ Q ↓[ t ] N ⟩)
  -> w ∈⟨ Q ↓[ t ] P ↓[ t ] N ⟩
∈⟨⟩-strengthening w t P Q N p n
  = (λ { a x → helperPos w t P Q N a p n x })
    , (λ {a x x2 → helperNeg w t P Q N a p n x x2})


--
-- Completeness of operational semantics 
--
↓-complete : ∀{w t P} → w ⊨[ t ] P → w ∈⟨ P ↓[ t ] [] ⟩
↓-complete {w} {t} {P ∧ Q} (both x y)
  = ∈⟨⟩-strengthening w t P Q [] (↓-complete x) (↓-complete y)
↓-complete {w} {+} {¬ x₁} (flip (nowhere x))
  = (λ { a (here ())
       ; a (there ())})
  , (λ { a (here refl) x₃ → x x₃
       ; a (there ()) x₃})
↓-complete {w} { - } {¬ x₁} (flip (somewhere x))
  = (λ { a (here refl) → x
       ; a (there ())})
  , (λ { a (here ()) x₃
       ; a (there ()) x₃})
↓-complete {w} { .+ } {atom x₁} (somewhere x)
  = (λ { a (here refl) → x
       ; a (there ()) })
  , (λ { a (here ()) x₃
       ; a (there ()) x₃ })
↓-complete {w} { .- } {atom x₁} (nowhere x)
  = (λ { a (here ())
       ; a (there ())})
  , (λ { a (here refl) x₃ → x x₃
       ; a (there ()) x₃})

--------------------------------------------------------------------------------------------------------------------------------------
-- New proofs

helper : (a : R) -> (N : State) -> (+ , a) ∈ N -> a ∈ (stateToWorld N)
helper a ((+ , .a) ∷ N) (here refl) = here refl
helper a ((+ , a1) ∷ N) (there x) = there (helper a N x)
helper a ((- , a1) ∷ N) (there x) = helper a N x

helper2 : (a : R) -> (N : State) -> a ∈ (stateToWorld N) -> (+ , a) ∈ N
helper2 a ((+ , .a) ∷ N) (here refl) = here refl
helper2 a ((+ , snd) ∷ N) (there x) = there (helper2 a N x)
helper2 a ((- , snd) ∷ N) x = there (helper2 a N x)

postulate
  implicit-consistency-assumption : (t : Polarity) (x : R) → ∀ N → (t , x) ∈ N → (neg t , x) ∉ N

stateToWorldConversionSound : (N : State) -> (stateToWorld N) ∈⟨ N ⟩
stateToWorldConversionSound [] = (λ x ()) , (λ x x₁ ())
stateToWorldConversionSound ((+ , p) ∷ N) = (λ { a (here refl) → here refl ; a (there x) → there (helper a N x)})
          , λ { a x (here refl) → implicit-consistency-assumption + p ((+ , p) ∷ N) (here refl) x
          ; a x (there x₁) → implicit-consistency-assumption + a ((+ , p) ∷ N) (there (helper2 a N x₁)) x}
stateToWorldConversionSound ((- , p) ∷ N) = (λ { a (there x) → helper a N x})
          , λ { a (here refl) x₁ → implicit-consistency-assumption - p (((- , p) ∷ N)) (here refl) (helper2 p ((- , p) ∷ N) x₁)
          ; a (there x) x₁ → implicit-consistency-assumption - a N x (helper2 a N x₁)}

_↓₊ : Form → State
P ↓₊ = P ↓[ + ] []

open import Data.List.Relation.Unary.Any
open import Agda.Builtin.Equality

convertedStateEntailsPositiveForm : (P : Form) -> (stateToWorld (P ↓₊)) ⊨[ + ] P
convertedStateEntailsPositiveForm N = ↓-sound (stateToWorldConversionSound (N ↓[ + ] []))
