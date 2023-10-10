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
open import Cubical.Data.Unit
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
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
open import spherebouquet

module cw-alt2 where

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

--now we define the boundary map as essentially Susp(to_cofiber) ∘ δ
pre-∂-aux : (n : ℕ) (C : CW) → cofiber (suc n) C →∙ Susp∙ (fst (cofiber n C))
pre-∂-aux n C = (suspFun (to_cofiber n C) , refl) ∘∙ δ∙ (suc n) C

--we need to compose with the isomorphism with the sphere bouquet...
--...and the fact that the suspension of a bouquet is a bouquet
pre-∂ : (n : ℕ) (C : CW) → (SphereBouquet (suc (suc n)) (Fin (snd C .fst (suc (suc n))))
                         →∙ SphereBouquet (suc (suc n)) (Fin (snd C .fst (suc n))))
pre-∂ n C = {!!}

--and then we take the bouquetDegree of pre-∂
∂ : (n : ℕ) (C : CW) → AbGroupHom ℤ[ Fin (snd C .fst (suc (suc n))) ] ℤ[ Fin (snd C .fst (suc n)) ]
∂ n C = bouquetDegree (pre-∂ n C)

--now we want to prove that ∂∂ = 0
--to do that, we use the lemmas in spherebouquet to show that it suffices to show Susp(pre-∂) ∘ pre-∂ = 0
--and this comes from the fact that δ ∘ to_cofiber = 0 (super easy to prove)
--plus some manipulations of the the isomosphisms (ugh)
