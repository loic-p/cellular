{-# OPTIONS --safe --lossy-unification --cubical #-}

{-
This file contains a definition of a notion of (strict)
subcomplexes of a CW complex. Here, a subomplex of a complex
C = colim ( C₀ → C₁ → ...)
is simply the complex
C⁽ⁿ⁾ := colim (C₀ → ... → Cₙ = Cₙ = ...)

This file contains.
1. Definition of above
2. A `strictification' of finite CW complexes in terms of above
3. An elmination principle for finite CW complexes
4. A proof that C and C⁽ⁿ⁾ has the same homolog in appropriate dimensions.
-}

module Hurewicz.SubcomplexNew where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat.Order.Inductive

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.ChainComplex
open import Cubical.CW.Approximation

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.ChainComplex

private
  variable
    ℓ ℓ' ℓ'' : Level

-- finite subcomplex C⁽ⁿ⁾ of a cw complex C.
module SubComplexGen (C : CWskel ℓ) (n : ℕ) where
  subComplexFam : (m : ℕ) → Trichotomyᵗ m n → Type ℓ
  subComplexFam m (lt x) = fst C m
  subComplexFam m (eq x) = fst C m
  subComplexFam m (gt x) = fst C n

  subComplexCard : (m : ℕ) → Trichotomyᵗ m n → ℕ
  subComplexCard m (lt x) = snd C .fst m
  subComplexCard m (eq x) = 0
  subComplexCard m (gt x) = 0

  -- Attaching maps
  subComplexα : (m : ℕ) (p : Trichotomyᵗ m n)
    → Fin (subComplexCard m p) × S⁻ m → subComplexFam m p
  subComplexα m (lt x) = snd C .snd .fst m

  subComplex₀-empty : (p : Trichotomyᵗ zero n) → ¬ subComplexFam zero p
  subComplex₀-empty (lt x₁) x = CW₀-empty C x
  subComplex₀-empty (eq x₁) x = CW₀-empty C x

  -- Resulting complex has CW structure
  subComplexFam≃Pushout : (m : ℕ) (p : Trichotomyᵗ m n) (q : Trichotomyᵗ (suc m) n) 
    → subComplexFam (suc m) q ≃ Pushout (subComplexα m p) fst
  subComplexFam≃Pushout m (lt x) (lt x₁) = snd C .snd .snd .snd m
  subComplexFam≃Pushout m (lt x) (eq x₁) = snd C .snd .snd .snd m
  subComplexFam≃Pushout m (lt x) (gt x₁) = ⊥.rec (¬squeeze (x , x₁))
  subComplexFam≃Pushout m (eq x) (lt x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x (<ᵗ-trans <ᵗsucm x₁)))
  subComplexFam≃Pushout m (eq x) (eq x₁) = ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (x₁ ∙ sym x) <ᵗsucm))
  subComplexFam≃Pushout m (eq x) (gt x₁) =
    compEquiv (pathToEquiv (λ i → fst C (x (~ i))))
              (isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0))
  subComplexFam≃Pushout m (gt x) (lt x₁) =
    ⊥.rec (¬squeeze (x₁ , <ᵗ-trans x (<ᵗ-trans <ᵗsucm <ᵗsucm)))
  subComplexFam≃Pushout m (gt x) (eq x₁) =
    ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₁ (<ᵗ-trans x <ᵗsucm)))
  subComplexFam≃Pushout m (gt x) (gt x₁) =
    isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0)

  subComplexFinEquiv' : (m : ℕ) (ineq : n <ᵗ suc m) (p : _)
    → isEquiv {B = Pushout (subComplexα m p) fst} inl
  subComplexFinEquiv' m ineq (lt x) = ⊥.rec (¬squeeze (x , ineq))
  subComplexFinEquiv' m ineq (eq x) = isoToIsEquiv (PushoutEmptyFam (¬Fin0 ∘ fst) ¬Fin0)
  subComplexFinEquiv' m ineq (gt x) = isoToIsEquiv (PushoutEmptyFam (¬Fin0 ∘ fst) ¬Fin0)

  complex≃subcomplex' : (m : ℕ) (ineq : m <ᵗ suc n) (p : _)
    → fst C m  ≃ subComplexFam m p
  complex≃subcomplex' m ineq (lt x) = idEquiv _
  complex≃subcomplex' m ineq (eq x) = idEquiv _
  complex≃subcomplex' m ineq (gt x) = ⊥.rec (¬squeeze (x , ineq))


module _ (C : CWskel ℓ) where
  module _ (n : ℕ) where
    module G = SubComplexGen C n
    subComplexFam : ℕ → Type ℓ
    subComplexFam m = G.subComplexFam m (m ≟ᵗ n)

    subComplexCard : (m : ℕ) → ℕ
    subComplexCard m = G.subComplexCard m (m ≟ᵗ n)

    -- Attaching maps
    subComplexα : (m : ℕ)
      → Fin (subComplexCard m) × S⁻ m → subComplexFam m
    subComplexα m = G.subComplexα m (m ≟ᵗ n)

    subComplex₀-empty : ¬ subComplexFam zero
    subComplex₀-empty = G.subComplex₀-empty (0 ≟ᵗ n)

    -- Resulting complex has CW structure
    subComplexFam≃Pushout : (m : ℕ)
      → subComplexFam (suc m) ≃ Pushout (subComplexα m) fst
    subComplexFam≃Pushout m =
      G.subComplexFam≃Pushout m (m ≟ᵗ n) (suc m ≟ᵗ n)

  -- packaging it all together
  subComplexYieldsCWskel : (n : ℕ) → yieldsCWskel (subComplexFam n)
  fst (subComplexYieldsCWskel n) m = subComplexCard n m
  fst (snd (subComplexYieldsCWskel n)) m = subComplexα n m
  fst (snd (snd (subComplexYieldsCWskel n))) = subComplex₀-empty n
  snd (snd (snd (subComplexYieldsCWskel n))) m = subComplexFam≃Pushout n m

  -- main definition
  subComplex : (n : ℕ) → CWskel ℓ
  fst (subComplex n) m = subComplexFam n m
  snd (subComplex n) = subComplexYieldsCWskel n

  subComplexFin : (m : ℕ) (n : Fin (suc m))
    → isEquiv (CW↪ (subComplex (fst n)) m)
  subComplexFin m n =
    compEquiv
      (_ , SubComplexGen.subComplexFinEquiv' C (fst n) m (snd n) (m ≟ᵗ fst n))
      (invEquiv (subComplexFam≃Pushout (fst n) m)) .snd

  subComplexYieldsFinCWskel : (n : ℕ) → yieldsFinCWskel n (subComplexFam n)
  fst (subComplexYieldsFinCWskel n) = subComplexYieldsCWskel n
  snd (subComplexYieldsFinCWskel n) k = subComplexFin (k + n) (n , <ᵗ-+)

  finSubComplex : (n : ℕ) → finCWskel ℓ n
  fst (finSubComplex n) m = subComplexFam n m
  snd (finSubComplex n) = subComplexYieldsFinCWskel n

  -- complex≃subcomplex : (n : ℕ) (m : Fin (suc n))
  --   → fst C (fst m) ≃ subComplex n .fst (fst m)
  -- complex≃subcomplex n (m , p) with (m ≟ᵗ n)
  -- ... | lt x = idEquiv _
  -- ... | eq x = idEquiv _
  -- ... | gt x = ⊥.rec (¬squeeze (x , p))

-- C⁽ⁿ⁾ₙ ≃ Cₙ
realiseSubComplex : (n : ℕ) (C : CWskel ℓ)
  → Iso (fst C n) (realise (subComplex C n))
realiseSubComplex n C =
  compIso (equivToIso (SubComplexGen.complex≃subcomplex' C n n <ᵗsucm (n ≟ᵗ n)))
          (realiseFin n (finSubComplex C n))

-- Strictifying finCWskel
niceFinCWskel : ∀ {ℓ} (n : ℕ) → finCWskel ℓ n → finCWskel ℓ n
fst (niceFinCWskel n (A , AC , fin)) = finSubComplex (A , AC) n .fst
snd (niceFinCWskel n (A , AC , fin)) = finSubComplex (A , AC) n .snd

makeNiceFinCWskel : ∀ {ℓ} {A : Type ℓ} → isFinCW A → isFinCW A
makeNiceFinCWskel {A = A} (dim , cwsk , e) = better
  where
  improved = finSubComplex (cwsk .fst , cwsk .snd .fst) dim

  better : isFinCW A
  fst better = dim
  fst (snd better) = improved
  snd (snd better) =
    compEquiv
      (compEquiv e (invEquiv (isoToEquiv (realiseFin dim cwsk))))
      (isoToEquiv (realiseSubComplex dim (cwsk .fst , cwsk .snd .fst)))


makeNiceFinCW : ∀ {ℓ} → finCW ℓ → finCW ℓ
fst (makeNiceFinCW C) = fst C
snd (makeNiceFinCW C) =
  PT.map makeNiceFinCWskel (snd C)

makeNiceFinCW≡ : ∀ {ℓ} (C : finCW ℓ) → makeNiceFinCW C ≡ C
makeNiceFinCW≡ C = Σ≡Prop (λ _ → squash₁) refl

-- Elimination principles
makeNiceFinCWElim : ∀ {ℓ ℓ'} {A : finCW ℓ → Type ℓ'}
  → ((C : finCW ℓ) → A (makeNiceFinCW C))
  → (C : _) → A C
makeNiceFinCWElim {A = A} ind C = subst A (makeNiceFinCW≡ C) (ind C)

makeNiceFinCWElim' : ∀ {ℓ ℓ'} {C : Type ℓ} {A : ∥ isFinCW C ∥₁ → Type ℓ'}
  → ((x : _) → isProp (A x))
  → ((cw : isFinCW C) → A (makeNiceFinCW (C , ∣ cw ∣₁) .snd))
  → (cw : _) → A cw
makeNiceFinCWElim' {A = A} pr ind =
  PT.elim pr λ cw → subst A (squash₁ _ _) (ind cw)

-- Goal: Show that a cell complex C and its subcomplex C⁽ⁿ⁾ share
-- homology in low enough dimensions
module _ (C : CWskel ℓ) where
  ChainSubComplex : (n : ℕ) → snd C .fst n ≡ snd (subComplex C (suc n)) .fst n
  ChainSubComplex n with (n ≟ᵗ suc n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) (sym x) <ᵗsucm))
  ... | gt x = ⊥.rec (¬-suc-n<ᵗn x)

  ≤ChainSubComplex : (n : ℕ) (m : Fin n)
    → snd C .fst (fst m) ≡ snd (subComplex C n) .fst (fst m)
  ≤ChainSubComplex n (m , p) with (m ≟ᵗ n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x p))
  ... | gt x = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))

subChainIso : (C : CWskel ℓ) (n : ℕ) (m : Fin n)
  → AbGroupIso (CWskel-fields.ℤ[A_] C (fst m))
                (CWskel-fields.ℤ[A_] (subComplex C n) (fst m))
subChainIso C n (m , p) with (m ≟ᵗ n)
... | lt x = idGroupIso
... | eq x = ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (sym x) p))
... | gt x = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))

-- main result
subComplexHomology : (C : CWskel ℓ) (n m : ℕ) (p : suc (suc m) <ᵗ n)
  → GroupIso (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ (subComplex C n) m)
subComplexHomology C n m p =
  homologyIso m _ _
    (subChainIso C n (suc (suc m) , p))
    (subChainIso C n (suc m , <ᵗ-trans <ᵗsucm p))
    (subChainIso C n (m , <ᵗ-trans <ᵗsucm (<ᵗ-trans <ᵗsucm p)))
    lem₁
    lem₂
  where
  lem₁ : {q : _} {r : _}
    → Iso.fun (subChainIso C n (m , q) .fst) ∘ ∂ C m .fst
    ≡ ∂ (subComplex C n) m .fst
     ∘ Iso.fun (subChainIso C n (suc m , r) .fst)
  lem₁ {q} {r} with (m ≟ᵗ n) | (suc m ≟ᵗ n) | (suc (suc m) ≟ᵗ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ r))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ r))
  ... | eq x | s | t = ⊥.rec (¬-suc-n<ᵗn (subst (suc m <ᵗ_) (sym x) r))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans r x))

  lem₂ : {q : suc m <ᵗ n} {r : (suc (suc m)) <ᵗ n}
    → Iso.fun (subChainIso C n (suc m , q) .fst)
     ∘ ∂ C (suc m) .fst
     ≡ ∂ (subComplex C n) (suc m) .fst
     ∘ Iso.fun (subChainIso C n (suc (suc m) , r) .fst)
  lem₂ {q} with (suc m ≟ᵗ n) | (suc (suc m) ≟ᵗ n) | (suc (suc (suc m)) ≟ᵗ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ p))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ p))
  ... | eq x | s | t = ⊥.rec (¬m<ᵗm (subst (suc m <ᵗ_) (sym x) q))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans p x))
