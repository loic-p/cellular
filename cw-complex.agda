{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp

open import prelude
open import spherebouquet

module cw-complex where

--- CW complexes ---

-- Definition of (the skeleton) of an arbitrary CW complex
yieldsCW : (ℕ → Type) → Type
yieldsCW X =
  Σ[ f ∈ (ℕ → ℕ) ]
        (Σ[ α ∈ ((n : ℕ) → (Fin (f (suc n)) × (S₊ n)) → X n) ]
         ((X zero ≃ Fin (f 0))
        × ((n : ℕ) → X (suc n) ≃ Pushout (α n) fst)))

CW : Type₁
CW = Σ[ X ∈ (ℕ → Type) ] (yieldsCW X)

-- Technically, a CW complex should be the sequential colimit over the following maps
CW↪ : (T : CW) → (n : ℕ) → fst T n → fst T (suc n)
CW↪ (X , α , e₀ , e₊) n x = invEq (e₊ .snd n) (inl x)

-- But if it stabilises, no need for colimits.
yieldsFinCW : (n : ℕ) (X : ℕ → Type) → Type
yieldsFinCW n X =
  Σ[ CW ∈ yieldsCW X ] ((k : ℕ) → isEquiv (CW↪ (X , CW) (k +ℕ n)))

-- ... which should give us finite CW complexes.
finCW : (n : ℕ) → Type₁
finCW n = Σ[ C ∈ (ℕ → Type) ] (yieldsFinCW n C)

--the cofiber of the inclusion of X n into X (suc n)
cofiber : (n : ℕ) (C : CW) → Pointed₀
cofiber n C = Pushout (terminal (fst C n)) (CW↪ C n) , inl tt

--...is basically a sphere bouquet
cofiber≃bouquet : (n : ℕ) (C : CW)
  → cofiber n C ≃∙ (SphereBouquet (suc n) (Fin (snd C .fst (suc n))))
cofiber≃bouquet n C = Bouquet≃∙-gen n (fst (C .snd) (suc n)) (α n) e
  where
  α = C .snd .snd .fst
  e = C .snd .snd .snd .snd n

--sending X (suc n) into the cofiber
to_cofiber : (n : ℕ) (C : CW) → (fst C (suc n)) → fst (cofiber n C)
to_cofiber n C x = inr x

--the connecting map of the long exact sequence
δ : (n : ℕ) (C : CW) → fst (cofiber n C) → Susp (fst C n)
δ n C (inl x) = north
δ n C (inr x) = south
δ n C (push a i) = merid a i

--pointed version
δ∙ : (n : ℕ) (C : CW) → cofiber n C →∙ Susp∙ (fst C n)
δ∙ n C = (δ n C) , refl
