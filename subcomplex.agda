{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import prelude
open import spherebouquet
open import cw-complex
open import cw-chain-complex
open import ChainComplex

module subcomplex where

-- finite subcomplex
module _ (C : CW) where
  subComplexFam : (n : ℕ) (m : ℕ) → Type
  subComplexFam n m with (m ≟ n)
  ... | lt x = fst C m
  ... | eq x = fst C m
  ... | gt x = fst C n

  subComplexCard : (n : ℕ) → ℕ → ℕ
  subComplexCard n m with (m ≟ n)
  ... | lt x = snd C .fst m
  ... | eq x = 0
  ... | gt x = 0

  subComplexα : (n m : ℕ) → Fin (subComplexCard n m) × S⁻ m → subComplexFam n m
  subComplexα n m with (m ≟ n)
  ... | lt x = snd C .snd .fst m
  ... | eq x = λ x → ⊥.rec (¬Fin0 (fst x))
  ... | gt x = λ x → ⊥.rec (¬Fin0 (fst x))

  subComplex₀-empty : (n : ℕ) → ¬ subComplexFam n zero
  subComplex₀-empty n with (zero ≟ n)
  ... | lt x = CW₀-empty C
  ... | eq x = CW₀-empty C
  ... | gt x = λ _ → ¬-<-zero x

  subComplexFam≃Pushout : (n m : ℕ)
    → subComplexFam n (suc m) ≃ Pushout (subComplexα n m) fst
  subComplexFam≃Pushout n m with (m ≟ n) | ((suc m) ≟ n)
  ... | lt x | lt x₁ = snd C .snd .snd .snd m
  ... | lt x | eq x₁ = snd C .snd .snd .snd m
  ... | lt x | gt x₁ = ⊥.rec (¬-<-suc x x₁)
  ... | eq x | lt x₁ = ⊥.rec (¬m<m (subst (_< n) x (<-trans (0 , refl) x₁)))
  ... | eq x | eq x₁ = ⊥.rec (snot (x₁ ∙ sym x))
  ... | eq x | gt x₁ =
    compEquiv (pathToEquiv (λ i → fst C (x (~ i))))
              (isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0))
  ... | gt x | lt x₁ =
    ⊥.rec (¬-suc-n<n (<-trans (suc-≤-suc x) x₁))
  ... | gt x | eq x₁ =
    ⊥.rec (<-asym (<-trans (0 , refl) (subst (_< suc n) (sym x₁) (0 , refl))) x)
  ... | gt x | gt x₁ = isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0)

  subComplexYieldsCW : (n : ℕ) → yieldsCW (subComplexFam n)
  fst (subComplexYieldsCW n) = subComplexCard n
  fst (snd (subComplexYieldsCW n)) = subComplexα n
  fst (snd (snd (subComplexYieldsCW n))) = subComplex₀-empty n
  snd (snd (snd (subComplexYieldsCW n))) m = subComplexFam≃Pushout n m

  subComplex : (n : ℕ) → CW
  fst (subComplex n) = subComplexFam n
  snd (subComplex n) = subComplexYieldsCW n

  subComplexFin : (n m : ℕ) (p : n ≤ m)
    → isEquiv (CW↪ (subComplexFam n , subComplexYieldsCW n) m)
  subComplexFin n m r with (m ≟ n) | (suc m ≟ n)
  ... | lt x | p = ⊥.rec (¬m<m (≤-trans x r))
  ... | eq x | lt x₁ = ⊥.rec (¬m<m (subst (_< n) x (<-trans (0 , refl) x₁)))
  ... | eq x | eq x₁ = ⊥.rec (snot (x₁ ∙ sym x))
  ... | eq x | gt x₁ =
    subst isEquiv (funExt λ x → cong (help .fst)
          (retEq (isoToEquiv (PushoutEmptyFam {A = Fin 0 × fst C m}
                  (λ x₃ → ¬Fin0 (fst x₃)) ¬Fin0 {f = snd} {g = fst})) x))
                  (help .snd)
      where
      help : fst C m ≃ fst C n
      help = invEquiv (pathToEquiv (λ i → fst C (x (~ i))))
  ... | gt x | lt x₁ =
    ⊥.rec (¬-suc-n<n (<-trans (suc-≤-suc x) x₁))
  ... | gt x | eq x₁ =
    ⊥.rec (<-asym (<-trans (0 , refl) (subst (_< suc n) (sym x₁) (0 , refl))) x)
  ... | gt x | gt x₁ =
    subst isEquiv (funExt (retEq (isoToEquiv (PushoutEmptyFam {A = Fin 0 × fst C n}
                          (λ x₃ → ¬Fin0 (fst x₃)) ¬Fin0 {f = snd} {g = fst}))))
                  (idEquiv _ .snd)

  subComplexYieldsFinCW : (n : ℕ) → yieldsFinCW n (subComplexFam n)
  fst (subComplexYieldsFinCW n) = subComplexYieldsCW n
  snd (subComplexYieldsFinCW n) k = subComplexFin n (k +ℕ n) (k , refl)

  finSubComplex : (n : ℕ) → finCW n
  fst (finSubComplex n) = subComplexFam n
  snd (finSubComplex n) = subComplexYieldsFinCW n

  complex≃subcomplex : (n m : ℕ) → m ≤ n → fst C m ≃ subComplex n .fst m
  complex≃subcomplex n m p with (m ≟ n)
  ... | lt x = idEquiv _
  ... | eq x = idEquiv _
  ... | gt x = ⊥.rec (¬m<m (≤-trans x p))

realiseSubComplex : (n : ℕ) (C : CW) → Iso (fst C n) (realise (subComplex C n))
realiseSubComplex n C =
  compIso (equivToIso (complex≃subcomplex C n n (0 , refl)))
          (realiseFin n (finSubComplex C n))

module _ (C : CW) where
  ChainSubComplex : (n : ℕ) → snd C .fst n ≡ snd (subComplex C (suc n)) .fst n
  ChainSubComplex n with (n ≟ suc n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (snot (sym x))
  ... | gt x = ⊥.rec (¬-suc-n<n x)

  ≤ChainSubComplex : (n m : ℕ) → m < n → snd C .fst m ≡ snd (subComplex C n) .fst m
  ≤ChainSubComplex n m p with (m ≟ n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<m (subst (_< n) x p))
  ... | gt x = ⊥.rec (¬m<m (<-trans x p))

-- needed?

-- subComplLem : (C : CW) (n : ℕ) (m : ℕ) (p : suc m < n)
--   → PathP (λ i → (SphereBouquet (suc m) (Fin (≤ChainSubComplex C n (suc m) p i))
--                →∙ SphereBouquet (suc m) (Fin (≤ChainSubComplex C n m (suc (fst p)
--                                      , sym (+-suc (fst p) (suc m)) ∙ snd p) i))))
--            (preboundary.pre∂ C m)
--            (preboundary.pre∂ (subComplex C n) m)
-- subComplLem c n m p with (m ≟ n) | (suc m ≟ n) | (suc (suc m) ≟ n)
-- ... | lt x | lt x₁ | lt x₂ = refl
-- ... | lt x | lt x₁ | eq x₂ = refl
-- ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze< (x₁ , x₂))
-- ... | lt x | eq x₁ | r = ⊥.rec (¬m<m (subst (_< n) x₁ p))
-- ... | lt x | gt x₁ | r = ⊥.rec (¬m<m (<-trans x₁ p))
-- ... | eq x | b | r = ⊥.rec (¬-suc-n<n (subst (suc m <_) (sym x) p))
-- ... | gt x | b | r = ⊥.rec (¬-suc-n<n (<-trans p x))

subChainIso : (C : CW) (n m : ℕ) (p : m < n)
  → AbGroupIso (ℤ[A C ] m) (ℤ[A subComplex C n ] m)
subChainIso C n m p with (m ≟ n)
... | lt x = idGroupIso
... | eq x = ⊥.rec (¬m<m (subst (m <_) (sym x) p))
... | gt x = ⊥.rec (¬m<m (<-trans x p))

subComplexHomology : (C : CW) (n m : ℕ) (p : suc (suc m) < n)
  → GroupIso (Hᶜʷ C m) (Hᶜʷ (subComplex C n) m)
subComplexHomology C n m p =
  homologyIso m _ _
    (subChainIso C n (suc (suc m)) p)
    (subChainIso C n (suc m) (<-trans (0 , refl) p))
    (subChainIso C n m (<-trans (0 , refl) (<-trans (0 , refl) p)))
    lem₁
    lem₂
  where
  lem₁ : {q : _} {r : _}
    → Iso.fun (subChainIso C n m q .fst) ∘ ∂ C m .fst
    ≡ ∂ (subComplex C n) m .fst
     ∘ Iso.fun (subChainIso C n (suc m) r .fst)
  lem₁ {q} {r} with (m ≟ n) | (suc m ≟ n) | (suc (suc m) ≟ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze< (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<m (subst (_< n) x₁ r))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<m (<-trans x₁ r))
  ... | eq x | s | t = ⊥.rec (¬-suc-n<n (subst (suc m <_) (sym x) r))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<n (<-trans r x))

  lem₂ : {q : suc m < n} {r : (suc (suc m)) < n}
    → Iso.fun (subChainIso C n (suc m) q .fst)
     ∘ ∂ C (suc m) .fst
     ≡ ∂ (subComplex C n) (suc m) .fst
     ∘ Iso.fun (subChainIso C n (suc (suc m)) r .fst)
  lem₂ {q} with (suc m ≟ n) | (suc (suc m) ≟ n) | (suc (suc (suc m)) ≟ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze< (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<m (subst (_< n) x₁ p))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<m (<-trans x₁ p))
  ... | eq x | s | t = ⊥.rec (¬m<m (subst (suc m <_) (sym x) q))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<n (<-trans p x))
