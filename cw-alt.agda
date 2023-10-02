{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetTruncation as ST

open import Cubical.Relation.Nullary
open import Cubical.Homotopy.Loopspace
open import Cubical.ZCohomology.Groups.Sn


open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.QuotientGroup renaming (_/_ to _//_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.AbGroup

open import prelude
open import freeabgroup

module cw-alt where

-- defn of the degree map
chooseS : (n : ℕ) (a b : ℕ) → S₊ n → S₊ n
chooseS n a b x with (discreteℕ a b)
... | yes p = x
... | no ¬p = ptSn n

degree : (n : ℕ) → (S₊ (suc n) → S₊ (suc n)) → ℤ
degree n f = Iso.fun ((Hⁿ-Sⁿ≅ℤ n) .fst) ∣ (λ x → ∣ f x ∣) ∣₂

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


-- This def makes ∂ easy to define.
∂-aux-gen : (n : ℕ) (C : CW)
  → Pushout (fst (C .snd .snd) n) fst
  → ℕ → S₊ (suc n)
∂-aux-gen n C (inl x) _ = ptSn (suc n)
∂-aux-gen n C (inr x) _ = ptSn (suc n)
∂-aux-gen n C (push (a , s) i) m = σ n (chooseS n (a .fst) m s) i

∂-aux : (n : ℕ) → (C : CW) → C .fst (suc n) → ℕ → S₊ (suc n)
∂-aux n C x m = ∂-aux-gen n C (fst (C .snd .snd .snd .snd n) x) m

-- Please check my indices...
pre∂ : (n : ℕ) (C : CW) → Fin (C .snd .fst (suc n)) → Fin (C .snd .fst n) → ℤ
pre∂ zero (C , f , α , e₀ , e₊) x y = pos (e₀ .fst (α zero (x , true)) .fst) - pos (e₀ .fst (α zero (x , false)) .fst)
pre∂ (suc n) C x y = degree n λ z → ∂-aux n C (α (x , z)) (y .fst)
  where
  Aₙ₊₂ : Type
  Aₙ₊₂ = Fin (fst (snd C) (suc (suc n)))

  α : Aₙ₊₂ × S₊ (suc n) → fst C (suc n)
  α = snd C .snd .fst (suc n)

module _ (C : CW) where
  ∂ : (n : ℕ) → ℤ[A snd C .fst (suc n) ] .fst → ℤ[A snd C .fst n ] .fst
  ∂ n f a = sumFin λ b → f b ·ℤ (pre∂ n C b a)

  ∂-hom : (n : ℕ) → AbGroupHom ℤ[A snd C .fst (suc n) ] ℤ[A snd C .fst n ]
  fst (∂-hom n) = ∂ n
  snd (∂-hom n) =
    makeIsGroupHom λ f g → funExt λ x →
      cong (sumFin {n = snd C .fst (suc n)})
        (funExt (λ y → ·DistL+ (f y) (g y) (pre∂ n C y x)))
    ∙ sumFin-hom (λ b → f b ·ℤ pre∂ n C b x) (λ b → g b ·ℤ pre∂ n C b x)

  ∂* : ∀ {ℓ} (n : ℕ) (G : AbGroup ℓ)
    → HomGroup (AbGroup→Group (ℤ[A snd C .fst n ])) G .fst
    → HomGroup (AbGroup→Group (ℤ[A snd C .fst (suc n) ])) G .fst
  ∂* n G f = compGroupHom (∂-hom n) f

  ∂*-hom : ∀ {ℓ} (n : ℕ) (G : AbGroup ℓ)
    → AbGroupHom (HomGroup (AbGroup→Group (ℤ[A snd C .fst n ])) G)
                  (HomGroup (AbGroup→Group (ℤ[A snd C .fst (suc n) ])) G)
  fst (∂*-hom n G) = ∂* n G
  snd (∂*-hom n G) =
    makeIsGroupHom λ f g → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    refl

  -- Need elimination principle for FreeAbGroup I think
  ∂² : (n : ℕ) (f : _) (a : _) → ∂ n (∂ (suc n) f) a ≡ 0
  ∂² n f a =
     cong (sumFin {n = snd C .fst (suc n)})
       (funExt (λ g → cong (_·ℤ pre∂ n C g a) (refl {x = sumFin (λ b → f b ·ℤ (pre∂ (suc n) C b g))}) ∙ refl))
    ∙ {!!}
    ∙ {!!}


H^_[_,_]gr : ∀ {ℓ} (n : ℕ) (C : CW) (G : AbGroup ℓ) → Group ℓ
H^ n [ C , G ]gr = {!kerSubgroup (∂*-hom C n G)!} // {!!}

H^_[_,_] : ∀ {ℓ} (n : ℕ) (C : CW) (G : AbGroup ℓ) → AbGroup ℓ
H^ n [ C , G ] = {!!}
