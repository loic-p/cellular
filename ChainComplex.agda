{-# OPTIONS --cubical --safe --lossy-unification #-}
module ChainComplex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties -- TODO: why is this there and not exported by the Morphisms file?
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup

open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties as SQ
open import Cubical.HITs.PropositionalTruncation as PT

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

homologyIso : (n : ℕ) (C D : ChainComplex ℓ)
  → (chEq₂ : AbGroupIso (chain C (suc (suc n))) (chain D (suc (suc n))))
  → (chEq₁ : AbGroupIso (chain C (suc n)) (chain D (suc n)))
  → (chEq₀ : AbGroupIso (chain C n) (chain D n))
  → Iso.fun (chEq₀ .fst) ∘ bdry C n .fst
   ≡ bdry D n .fst ∘ Iso.fun (chEq₁ .fst)
  → Iso.fun (chEq₁ .fst) ∘ bdry C (suc n) .fst
   ≡ bdry D (suc n) .fst ∘ Iso.fun (chEq₂ .fst)
  → GroupIso (homology n C) (homology n D)
homologyIso n C D chEq₂ chEq₁ chEq₀ eq1 eq2 = main-iso
  where
  F : homology n C .fst → homology n D .fst
  F = SQ.elim (λ _ → squash/) f
    λ a b r → eq/ _ _
      (PT.map (λ { (s , t)
        → (Iso.fun (chEq₂ .fst) s)
          , Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
            (sym (funExt⁻ eq2 s)
           ∙ cong (Iso.fun (chEq₁ .fst)) (cong fst t)
           ∙ IsGroupHom.pres· (chEq₁ .snd) _ _
           ∙ cong₂ (snd (chain D (suc n)) .AbGroupStr._+_)
                   refl
                   (IsGroupHom.presinv (chEq₁ .snd) _))}) r)
    where
    f : _ → homology n D .fst
    f (a , b) = [ Iso.fun (fst chEq₁) a
                , sym (funExt⁻ eq1 a) ∙ cong (Iso.fun (chEq₀ .fst)) b
                ∙ IsGroupHom.pres1 (snd chEq₀) ]

  G : homology n D .fst → homology n C .fst
  G = SQ.elim (λ _ → squash/) g
    λ a b r → eq/ _ _
      (PT.map (λ {(s , t)
      → (Iso.inv (chEq₂ .fst) s)
       , Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain C n)) _ _)
           (sym (Iso.leftInv (chEq₁ .fst) _)
          ∙ cong (Iso.inv (chEq₁ .fst)) (funExt⁻ eq2 (Iso.inv (chEq₂ .fst) s))
          ∙ cong (Iso.inv (chEq₁ .fst) ∘ bdry D (suc n) .fst)
                 (Iso.rightInv (chEq₂ .fst) s)
          ∙ cong (Iso.inv (chEq₁ .fst)) (cong fst t)
          ∙ IsGroupHom.pres· (invGroupIso chEq₁ .snd) _ _
          ∙ cong₂ (snd (chain C (suc n)) .AbGroupStr._+_)
                   refl
                   ((IsGroupHom.presinv (invGroupIso chEq₁ .snd) _)))}) r)
    where
    g : _ → homology n C .fst
    g (a , b) = [ Iso.inv (fst chEq₁) a
                , sym (Iso.leftInv (chEq₀ .fst) _)
                ∙ cong (Iso.inv (chEq₀ .fst)) (funExt⁻ eq1 (Iso.inv (chEq₁ .fst) a))
                ∙ cong (Iso.inv (chEq₀ .fst) ∘ bdry D n .fst)
                       (Iso.rightInv (chEq₁ .fst) a)
                ∙ cong (Iso.inv (chEq₀ .fst)) b
                ∙ IsGroupHom.pres1 (invGroupIso chEq₀ .snd) ]

  F-hom : IsGroupHom (homology n C .snd) F (homology n D .snd)
  F-hom =
    makeIsGroupHom
      (SQ.elimProp2 (λ _ _ → GroupStr.is-set (homology n D .snd) _ _)
        λ {(a , s) (b , t)
        → cong [_] (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
                     (IsGroupHom.pres·  (snd chEq₁) _ _)) })

  main-iso : GroupIso (homology n C) (homology n D)
  Iso.fun (fst main-iso) = F
  Iso.inv (fst main-iso) = G
  Iso.rightInv (fst main-iso) =
    elimProp (λ _ → GroupStr.is-set (homology n D .snd) _ _)
      λ{(a , b)
      → cong [_] (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain D n)) _ _)
                  (Iso.rightInv (fst chEq₁) a))}
  Iso.leftInv (fst main-iso) =
    elimProp (λ _ → GroupStr.is-set (homology n C .snd) _ _)
      λ{(a , b)
      → cong [_] (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain C n)) _ _)
                  (Iso.leftInv (fst chEq₁) a))}
  snd main-iso = F-hom

-- -- TODO: define cohomology
