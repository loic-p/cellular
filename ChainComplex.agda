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

module _ {G H : Group ℓ} (ϕ : GroupHom G H) where

  -- TODO: upstream (not sure we want to define this this way though?)
  kerGroup : Group ℓ
  kerGroup = Subgroup→Group G (kerSubgroup ϕ)

open ChainComplex

homology : (n : ℕ) → ChainComplex ℓ → Group ℓ
homology n C = kerGroup (bdry C n) / foo
  where
  im∂+1 : Group _
  im∂+1 = imGroup (bdry C (suc n))

  ker∂ : Group _
  ker∂ = kerGroup (bdry C n)

  apa : isSubgroup (AbGroup→Group (chain C (suc n))) (kerSubset (bdry C n))
  apa = isSubgroupKer (bdry C n)

  bepa : isSubgroup (AbGroup→Group (chain C (suc n))) (imSubset (bdry C (suc n)))
  bepa = isSubgroupIm (bdry C (suc n))

  ∂' : GroupHom im∂+1 ker∂
  ∂' = {!!}

  im∂+1⊂ker∂ : isSubgroup ker∂ {!!}
  im∂+1⊂ker∂ = {!!}

  foo : NormalSubgroup (kerGroup (bdry C n))
  fst (fst foo) = {!!}
  snd (fst foo) = {!!}
  snd foo = {!!}

