{-# OPTIONS --cubical --allow-unsolved-metas --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SequentialColimit

open import cw-complex
open import choice

module cw-approx where

open Sequence

-- todo: clean up imports

realiseSeq : CW → Sequence ℓ-zero
Sequence.obj (realiseSeq (C , p)) = C
Sequence.map (realiseSeq C) = CW↪ C _

-- realisation of CW complex from skeleton
realise : CW → Type
realise C = SeqColim (realiseSeq C)

-- elimination from colimit into prop (move to lib)
Lim→Prop : ∀ {ℓ ℓ'} {C : Sequence ℓ} {B : SeqColim C → Type ℓ'}
  → ((x : _) → isProp (B x))
  → (s : (n : ℕ) (x : obj C n) → B (incl x))
  → (x : _) → B x
Lim→Prop {C = C} pr ind (incl x) = ind _ x
Lim→Prop {C = C} {B = B} pr ind (push x i) =
  isProp→PathP {B = λ i → B (push x i)}
    (λ i → pr _)
    (ind _ x) (ind (suc _) (C .Sequence.map x)) i

-- elimination from Cₙ into prop
CWskel→Prop : (C : CW) {A : (n : ℕ) → fst C n → Type}
  → ((n : ℕ) (x : _) → isProp (A n x))
  → ((a : _) → A zero a)
  → ((n : ℕ) (a : _) → (A n a → A (suc n) (CW↪ C n a)))
  → (n : _) (c : fst C n) → A n c
CWskel→Prop C {A = A} pr b eqs zero c = b c
CWskel→Prop C {A = A} pr b eqs (suc n) c =
  subst (A (suc n))
        (retEq (snd C .snd .snd .snd n) c)
        (help (CWskel→Prop C pr b eqs n) _)
  where
  help : (inder : (c₁ : fst C n) → A n c₁)
       → (a : Pushout _ fst)
       → A (suc n) (invEq (snd C .snd .snd .snd n) a)
  help inder =
    elimProp _ (λ _ → pr _ _) (λ b → eqs n _ (inder b))
     λ c → subst (A (suc n))
                  (cong (invEq (snd C .snd .snd .snd n)) (push (c , ptSn n)))
                  (eqs n _ (inder _))

-- eliminating from CW complex into prop
CW→Prop : (C : CW) {A : realise C → Type}
  → ((x : _) → isProp (A x))
  → ((a : _) → A (incl {n = zero} a))
  → (a : _) → A a
CW→Prop C {A = A} pr ind  =
  Lim→Prop pr (CWskel→Prop C (λ _ _ → pr _)
    ind
    λ n a → subst A (push a))

isSet-CW₀ : (C : CW) → isSet (fst C 0)
isSet-CW₀ C =
  isOfHLevelRetractFromIso 2 (equivToIso (snd C .snd .snd .fst))
    isSetFin

-- Cellular approximation
module _ (C D : CW) (f : realise C → realise D) where
  find-connected-component : (d : realise D) → ∃[ d0 ∈ fst D 0 ] incl d0 ≡ d
  find-connected-component = CW→Prop D (λ _ → squash₁) λ a → ∣ a , refl ∣₁

  find-connected-component-C₀ : (c : fst C 0) → ∃[ d0 ∈ fst D 0 ] incl d0 ≡ f (incl c)
  find-connected-component-C₀ c = find-connected-component (f (incl c))

  satAC∃Fin-C0 : ∀ {ℓ ℓ'} → satAC∃ ℓ ℓ' (fst C 0)
  satAC∃Fin-C0 {ℓ} {ℓ'} = subst (satAC∃ ℓ ℓ') ( sym (ua (snd C .snd .snd .fst))) (satAC∃Fin _)

  -- existence of f₀ : C₀ → D₀
  approx₀ : ∃[ f₀ ∈ (fst C 0 → fst D 0) ] ((c : _) → incl (f₀ c) ≡ f (incl c) )
  approx₀ =
    invEq (_ , satAC∃Fin-C0 (λ _ → fst D 0) (λ c d0 → incl d0 ≡ f (incl c)))
      find-connected-component-C₀

  -- todo: higher dims...
