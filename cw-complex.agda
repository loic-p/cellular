{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp

open import Cubical.Relation.Nullary

open import prelude
open import spherebouquet

module cw-complex where


--- CW complexes ---
-- Definition of (the skeleton) of an arbitrary CW complex

-- New def: X 0 is empty and C (suc n) is pushout
yieldsCW : (ℕ → Type) → Type
yieldsCW X =
  Σ[ f ∈ (ℕ → ℕ) ]
    Σ[ α ∈ ((n : ℕ) → (Fin (f n) × (S⁻ n)) → X n) ]
      ((¬ X zero) ×
      ((n : ℕ) → X (suc n) ≃ Pushout (α n) fst))

CW : Type₁
CW = Σ[ X ∈ (ℕ → Type) ] (yieldsCW X)

CW₀-empty : (C : CW) → ¬ fst C 0
CW₀-empty C = snd (snd (snd C)) .fst

CW₁-discrete : (C : CW) → fst C 1 ≃ Fin (snd C .fst 0)
CW₁-discrete C = compEquiv (snd C .snd .snd .snd 0) (isoToEquiv main)
  where
  main : Iso (Pushout (fst (snd C .snd) 0) fst) (Fin (snd C .fst 0))
  Iso.fun main (inl x) = ⊥.rec (CW₀-empty C x)
  Iso.fun main (inr x) = x
  Iso.inv main = inr
  Iso.rightInv main x = refl
  Iso.leftInv main (inl x) = ⊥.rec (CW₀-empty C x)
  Iso.leftInv main (inr x) = refl

-- Technically, a CW complex should be the sequential colimit over the following maps
CW↪ : (T : CW) → (n : ℕ) → fst T n → fst T (suc n)
CW↪ (X , f , α , e₀ , e₊) n x = invEq (e₊ n) (inl x)

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
  → cofiber n C ≃∙ SphereBouquet n (Fin (snd C .fst n))
cofiber≃bouquet n C = Bouquet≃∙-gen n (snd C .fst n) (α n) e
  where
  s = Bouquet≃∙-gen
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
