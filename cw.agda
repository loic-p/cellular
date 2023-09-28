{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.Relation.Nullary

mutual
  -- description of n-dimensional finite cell complex
  CW : ℕ → Type0
  CW zero = ℕ
  CW (suc n) = Σ (CW n) (λ C → Σ ℕ (λ m → (Fin m × (S₊ n) → real n C)))

  -- realization of a n-dimensional finite cell complex
  real : (n : ℕ) → CW n → Type0
  real zero m = Fin m
  real (suc n) (C , m , bndry) = Pushout bndry fst

-- number of cells of max dimension
cells : (n : ℕ) → CW n → ℕ
cells zero m = m
cells (suc n) (C , m , bndry) = m

-- number of cells of max dimension minus one
prev-cells : (n : ℕ) → CW (suc n) → ℕ
prev-cells zero (m , _ , _) = m
prev-cells (suc n) ((C , m , bndry) , _ , _) = m

∂-aux : (n : ℕ) → (C : CW (suc n)) → real (suc n) C → Fin (cells (suc n) C) → S₊ (suc n)
∂-aux n C (inl _) _ = ptSn (suc n)
∂-aux n C (inr a) b = ptSn (suc n)
∂-aux n C (push (a , s) i) b with (discreteℕ (fst a) (fst b))
∂-aux n C (push (a , s) i) b | yes e = {!!}
∂-aux n C (push (a , s) i) b | no _ = ptSn (suc n)

degree : (n : ℕ) → (S₊ n → S₊ n) → ℕ
degree = {!!}

-- ∂ : (n : ℕ) → (C : CW (suc n)) → Fin (cells (suc n) C) → Fin (prev-cells n C) → ℕ
-- ∂ n C a b = degree n (∂-aux n C
