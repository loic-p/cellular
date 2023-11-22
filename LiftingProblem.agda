{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude hiding (lift)

module LiftingProblem where

record LiftingProblem (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    E0 B0 E1 B1 : Type ℓ
    p0 : E0 → B0
    p1 : E1 → B1
    mapE : E0 → E1
    mapB : B0 → B1
    square : ∀ x → p1 (mapE x) ≡ mapB (p0 x)

mkLiftingProblem : {ℓ : Level} → {E0 B0 E1 B1 : Type ℓ}
  → (p0 : E0 → B0) → (p1 : E1 → B1) → (mapE : E0 → E1) → (mapB : B0 → B1)
  → (∀ x → p1 (mapE x) ≡ mapB (p0 x)) → LiftingProblem ℓ
mkLiftingProblem p0 p1 mapE mapB square =
  record { E0 = _ ; B0 = _ ; E1 = _ ; B1 = _
         ; p0 = p0 ; p1 = p1 ; mapE = mapE ; mapB = mapB ; square = square }

record LiftingSolution {ℓ : Level} (problem : LiftingProblem ℓ) : Type ℓ where
  open LiftingProblem problem
  field
    lift : B0 → E1
    upperTriangle : ∀ x → mapE x ≡ lift (p0 x)
    lowerTriangle : ∀ x → p1 (lift x) ≡ mapB x
    pasting : ∀ x → square x ≡ (cong p1 (upperTriangle x) ∙ lowerTriangle (p0 x))

module _ {ℓ : Level} {problem : LiftingProblem ℓ} where
  open LiftingProblem problem

  mkLiftingSolution : (lift : B0 → E1)
    → (upperTriangle : ∀ x → mapE x ≡ lift (p0 x))
    → (lowerTriangle : ∀ x → p1 (lift x) ≡ mapB x)
    → (pasting : ∀ x → square x ≡ (cong (p1) (upperTriangle x) ∙ lowerTriangle (p0 x)))
    → LiftingSolution problem
  mkLiftingSolution lift upperTriangle lowerTriangle pasting =
    record { lift = lift ; upperTriangle = upperTriangle
           ; lowerTriangle = lowerTriangle ; pasting = pasting }
