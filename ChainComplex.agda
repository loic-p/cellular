{-# OPTIONS --cubical --safe --lossy-unification #-}
module ChainComplex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties -- TODO: why is this there and not exported by the Morphisms file?
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.Algebra.AbGroup

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import prelude

record ChainComplex (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    chain   : (n : ℕ) → AbGroup ℓ
    bdry    : (n : ℕ) → AbGroupHom (chain (suc n)) (chain n)
    bdry²=0 : (n : ℕ) → compGroupHom (bdry (suc n)) (bdry n) ≡ 0hom


record CoChainComplex (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    cochain   : (n : ℕ) → AbGroup ℓ
    cobdry    : (n : ℕ) → AbGroupHom (cochain n) (cochain (suc n))
    cobdry²=0 : (n : ℕ) → compGroupHom (cobdry n) (cobdry (suc n)) ≡ 0hom


private
  variable
    ℓ : Level

-- TODO: upstream these
module _ {G H : Group ℓ} (ϕ : GroupHom G H) where
  kerGroup : Group ℓ
  kerGroup = Subgroup→Group G (kerSubgroup ϕ)

  kerGroup≡ : {x y : ⟨ kerGroup ⟩} → x .fst ≡ y .fst → x ≡ y
  kerGroup≡ = Σ≡Prop (isPropIsInKer ϕ)


open ChainComplex
open IsGroupHom

homology : (n : ℕ) → ChainComplex ℓ → Group ℓ
homology n C = ker∂n / img∂+1⊂ker∂n
  where
  Cn+2 = AbGroup→Group (chain C (suc (suc n)))
  ∂n = bdry C n
  ∂n+1 = bdry C (suc n)
  ker∂n = kerGroup ∂n

  -- Restrict ∂n+1 to ker∂n
  ∂' : GroupHom Cn+2 ker∂n
  fst ∂' x           = ∂n+1 .fst x , funExt⁻ (cong fst (bdry²=0 C n)) x
  pres· (snd ∂') x y = kerGroup≡ ∂n (∂n+1 .snd .pres· x y)
  pres1 (snd ∂')     = kerGroup≡ ∂n (∂n+1 .snd .pres1)
  presinv (snd ∂') x = kerGroup≡ ∂n (∂n+1 .snd .presinv x)

  img∂+1⊂ker∂n : NormalSubgroup ker∂n
  fst img∂+1⊂ker∂n = imSubgroup ∂'
  snd img∂+1⊂ker∂n =
    isNormalIm ∂' (λ x y → kerGroup≡ ∂n (C1.+Comm (fst x) (fst y)))
      where
      module C1 = AbGroupStr (chain C (suc n) .snd)


-- TODO: define cohomology
