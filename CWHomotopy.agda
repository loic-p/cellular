{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool hiding (_≟_ ; isProp≤)

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms

open import prelude
open import freeabgroup
open import spherebouquet
open import degree
open import cw-complex
open import cw-chain-complex
open import cw-map
open import ChainComplex

module CWHomotopy where

record cellHom {C D : CW} (f g : cellMap C D) : Type where
  open cellMap
  field
    hom : (n : ℕ) → (x : C .fst n) → CW↪ D n (f .map n x) ≡ CW↪ D n (g .map n x)
    coh : (n : ℕ) → (c : C .fst n) → Square (cong (CW↪ D (suc n)) (hom n c))
                                            (hom (suc n) (CW↪ C n c))
                                            (cong (CW↪ D (suc n)) (f .comm n c))
                                            (cong (CW↪ D (suc n)) (g .comm n c))

module _ (C D : CW) (f g : cellMap C D) (H : cellHom f g) where
  open cellMap
  open cellHom

  module _ (n : ℕ) where
    Hn+1/Hn : Susp (cofiber n C) → cofiber (suc n) D
    Hn+1/Hn north = inl tt
    Hn+1/Hn south = inl tt
    Hn+1/Hn (merid (inl tt) i) = inl tt
    Hn+1/Hn (merid (inr x) i) = ((push (f .map (suc n) x)) ∙∙ (cong inr (H .hom (suc n) x)) ∙∙ (sym (push (g .map (suc n) x)))) i
    Hn+1/Hn (merid (push x j) i) =
      hcomp (λ k → λ { (i = i0) → push (f .comm n x j) (~ k)
                     ; (i = i1) → push (g .comm n x j) (~ k)
                     ; (j = i0) → push (hom H n x i) (~ k) })
            (inr (H .coh n x j i))

  module _ (n : ℕ) where

    ∂H : Susp (cofiber n C) → Susp (cofiber n D)
    ∂H north = north
    ∂H south = north
    ∂H (merid (inl tt) i) = north
    ∂H (merid (inr x) i) = ((merid (inr (f .map (suc n) x))) ∙∙ refl ∙∙ (sym (merid (inr (g .map (suc n) x))))) i
    ∂H (merid (push x j) i) =
      hcomp (λ k → λ { (i = i0) → merid (inr (f .comm n x j)) (~ k)
                     ; (i = i1) → merid (inr (g .comm n x j)) (~ k)
                     ; (j = i0) → merid (inr (hom H n x i)) (~ k) })
            (south)

    Σ∂ : Susp (cofiber (suc n) C) → Susp (Susp (cofiber n C))
    Σ∂ north = north
    Σ∂ south = south
    Σ∂ (merid (inl tt) i) = merid north i
    Σ∂ (merid (inr x) i) = merid south i
    Σ∂ (merid (push x j) i) = merid (merid (inr x) j) i

    ΣH∂ : Susp (cofiber n C) → Susp (cofiber n D)
    ΣH∂ north = north
    ΣH∂ south = south
    ΣH∂ (merid (inl tt) i) = merid (inl tt) i
    ΣH∂ (merid (inr x) i) = merid (inl tt) i
    ΣH∂ (merid (push x j) i) = merid (((push (f .map n x)) ∙∙ (cong inr (H .hom n x)) ∙∙ (sym (push (g .map n x)))) j) i

    f-ΣH∂ : Susp (cofiber n C) → Susp (cofiber n D)
    f-ΣH∂ north = north
    f-ΣH∂ south = north
    f-ΣH∂ (merid (inl tt) i) = north
    f-ΣH∂ (merid (inr x) i) = ((merid (inr (f .map (suc n) x))) ∙∙ refl ∙∙ (sym (merid (inl tt)))) i
    f-ΣH∂ (merid (push x j) i) =
      hcomp (λ k → λ { (i = i0) → merid (inr (f .comm n x j)) (~ k)
                     ; (i = i1) → merid (push (g .map n x) (~ j)) (~ k)
                     ; (j = i0) → merid (inr (hom H n x i)) (~ k) })
            (south)

    -- then we wanna prove f - ΣH∂ = f-ΣH∂ with 3D cubes
    -- and finally f-ΣH∂ = ∂H + g
