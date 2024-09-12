{-# OPTIONS --cubical #-}
module EilenbergSteenrod.CWPushout where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.CW.Base
open import Cubical.CW.Map

open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT

finSplit3 : ∀ n m l → Fin (n +ℕ m +ℕ l) → ((Fin n) ⊎ (Fin m)) ⊎ (Fin l)
finSplit3 = {!!}

module CWstrictification (ℓ : Level) (X : CWskel ℓ) where
  open CWskel-fields X

  strictA : ℕ → Type ℓ
  A≃strictA : (n : ℕ) → strictA n ≃ X .fst n

  strictA zero = X .fst zero
  strictA (suc n) = Pushout ((invEq (A≃strictA n)) ∘ (α n)) fst

  A≃strictA zero = idEquiv (X .fst zero)
  A≃strictA (suc n) = {!!}

  strictMap : (n : ℕ) → (Fin (card n) × (S⁻ n)) → strictA n
  strictMap n = (invEq (A≃strictA n)) ∘ (α n)

  strict : CWskel ℓ
  strict = strictA , (card , strictMap , X .snd .snd .snd .fst , λ n → idEquiv (Pushout ((invEq (A≃strictA n)) ∘ (α n)) fst))

strictifySkel : {ℓ : Level} → CWskel ℓ → CWskel ℓ
strictifySkel X = CWstrictification.strict _ X

module _ (ℓ : Level) (B₀ C₀ D₀ : CWskel ℓ)
  (f : cellMap (strictifySkel B₀) (strictifySkel C₀))
  (g : cellMap (strictifySkel B₀) (strictifySkel D₀)) where

  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)

  B = strictifySkel B₀
  C = strictifySkel C₀
  D = strictifySkel D₀

  2+ : ℕ → ℕ
  2+ n = suc (suc n)

  pushoutA : ℕ → Type ℓ
  pushoutA zero = B .fst zero
  pushoutA (suc n) = Pushout (CW↪ C n ∘ ∣ f ∣ n) (CW↪ D n ∘ ∣ g ∣ n)

  pushoutCells : ℕ → ℕ
  pushoutCells zero = (card C zero) +ℕ (card D zero)
  pushoutCells (suc n) = (card C (suc n)) +ℕ (card B n) +ℕ (card D (suc n))

  pushoutMap₀ : (Fin (pushoutCells zero)) × (S⁻ 0) → pushoutA 0
  pushoutMap₀ ()

  pushoutMap₁ : (((A C 1) ⊎ (A B 0)) ⊎ (A D 1)) × (S⁻ 1) → pushoutA 1
  pushoutMap₁ (inl (inl c) , x) = inl (α C 1 (c , x))
  pushoutMap₁ (inl (inr b) , false) = inl (∣ f ∣ 1 (inr b))
  pushoutMap₁ (inl (inr b) , true) = inr (∣ g ∣ 1 (inr b))
  pushoutMap₁ (inr d , x) = inr (α D 1 (d , x))

  pushoutMapₛ : (n : ℕ) → (((A C (2+ n)) ⊎ (A B (suc n))) ⊎ (A D (2+ n))) × (Susp (S⁻ (suc n))) → pushoutA (2+ n)
  pushoutMapₛ n (inl (inl c) , x) = inl (α C (2+ n) (c , Iso.inv (IsoSucSphereSusp n) x))
  pushoutMapₛ n (inl (inr b) , north) = inl (∣ f ∣ (2+ n) (invEq (e B (suc n)) (inr b)))
  pushoutMapₛ n (inl (inr b) , south) = inr (∣ g ∣ (2+ n) (invEq (e B (suc n)) (inr b)))
  pushoutMapₛ n (inl (inr b) , merid x i) =
    ((λ i → inl (∣ f ∣ (2+ n) (push (b , x) (~ i))))
    ∙∙ ((λ i → inl (f .comm (suc n) (α B (suc n) (b , x)) (~ i)))
    ∙∙ (push (α B (suc n) (b , x)))                                   -- push is the main guy, the rest is just decoration
    ∙∙ (λ i → inr (g .comm (suc n) (α B (suc n) (b , x)) i)))
    ∙∙ (λ i → inr (∣ g ∣ (2+ n) (push (b , x) i)))) i
  pushoutMapₛ n (inr d , x) = inr (α D (2+ n) (d , Iso.inv (IsoSucSphereSusp n) x))

  pushoutMap : (n : ℕ) → (Fin (pushoutCells n)) × (S⁻ n) → pushoutA n
  pushoutMap zero = pushoutMap₀
  pushoutMap (suc zero) (a , x) = pushoutMap₁ (finSplit3 (card C 1) (card B 0) (card D 1) a , x)
  pushoutMap (suc (suc n)) (a , x) = pushoutMapₛ n (finSplit3 (card C (2+ n)) (card B (suc n)) (card D (2+ n)) a
                                                   , Iso.fun (IsoSucSphereSusp n) x)
