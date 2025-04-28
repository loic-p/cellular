{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.SFT where

open import Hurewicz.SubcomplexNew
open import Hurewicz.random

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.Connected
open import Cubical.CW.Homology.Base
open import Cubical.CW.Approximation
open import Cubical.CW.ChainComplex

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.FinSequence
open import Cubical.Data.Int
open import Cubical.Data.Unit

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/s_)
open import Cubical.HITs.Wedge

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties
open import Cubical.Homotopy.Connected

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Abelianization.Properties as Abi
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Relation.Nullary

open import Cubical.CW.Instances.Sn
open import Cubical.CW.Homology.Groups.Sn

open import Hurewicz.SphereBouquetCofib2
open import Hurewicz.SphereBouquetCofibHomotopy
open import Hurewicz.SphereBouquetCofibHomotopyP2
open import Cubical.HITs.Bouquet
open import Cubical.HITs.FreeGroup.Base

open import Hurewicz.SphereBouquetCofib2
open import Hurewicz.SphereBouquetCofibHomotopy
open import Hurewicz.SphereBouquetCofibHomotopyP2
open import Hurewicz.Map
open import Cubical.HITs.Bouquet
open import Cubical.HITs.FreeGroup.Base


open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as TR
open import Cubical.CW.Properties
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.Subgroup

private
  variable
    ℓ : Level

record FinitePresentation (A : AbGroup ℓ) : Type ℓ where
  field
    nGens : ℕ
    nRels : ℕ
    rels : AbGroupHom ℤ[Fin nRels ] ℤ[Fin nGens ]
    fpiso : GroupIso (AbGroup→Group A)
                       (AbGroup→Group ℤ[Fin nGens ]
                       / (imSubgroup rels , isNormalIm rels λ f g → funExt (λ _ → +Comm _ _)))

open FinitePresentation
isFPπSphereBouquetCofib :  {n m k : ℕ}
   (α : SphereBouquet∙ (suc (suc n)) (Fin m)
     →∙ SphereBouquet∙ (suc (suc n)) (Fin k))
  → FinitePresentation (Group→AbGroup (π'Gr (suc n) (cofib (fst α) , inl tt)) (π'-comm n))
nGens (isFPπSphereBouquetCofib {n = n} {m = m} {k = k} α) = k
nRels (isFPπSphereBouquetCofib {n = n} {m = m} {k = k} α) = m
rels (isFPπSphereBouquetCofib {n = n} {m = m} {k = k} α) = bouquetDegree (fst α)
fpiso (isFPπSphereBouquetCofib {n = n} {m = m} {k = k} α) = π'CofibBouquetMap≅ℤ[]/BouquetDegree α

module _ (X : Pointed ℓ-zero) (n : ℕ) (hX : isConnectedCW (1 +ℕ n) (typ X)) (cX : isConnected (3 +ℕ n) (typ X))
  (cX' : isConnected 2 (hX .fst .fst (suc (suc (suc (suc n))))))
  (x* : hX .fst .fst (4 +ℕ n))
  (x*pres : fst (hX .snd) (CW↪∞ ((hX .fst .fst) , (hX .fst .snd .fst)) (4 +ℕ n) x*)
          ≡ snd X)
  where
  private
    Xskel : CWskel _
    Xskel = ((hX .fst .fst) , (hX .fst .snd .fst)) 

    e = hX .snd

    Xfam = hX .fst .fst

  firstEquiv : GroupEquiv  (π'Gr (suc n) (Xfam (4 +ℕ n) , x*)) (π'Gr (suc n) X)
  firstEquiv =
     (connectedFun→π'Equiv (suc n)
             (fst e ∘ CW↪∞ Xskel (4 +ℕ n) , x*pres)
             (isConnectedComp (fst e) (CW↪∞ Xskel (4 +ℕ n)) _
               (isEquiv→isConnected _ (snd e) (4 +ℕ n))
               (isConnected-CW↪∞ (4 +ℕ n) Xskel)))

  isFPGuy1 : ∥ FinitePresentation (Group→AbGroup (π'Gr (suc n) (Xfam (4 +ℕ n) , x*)) (π'-comm n)) ∥₁
  isFPGuy1 = PT.rec squash₁
    (λ {(α , e) → PT.map
      (λ pp → subst FinitePresentation
                      (cong (λ X → Group→AbGroup (π'Gr (suc n) X) (π'-comm n))
                     (ΣPathP ((sym (cong fst e)) , pp)))
                     (isFPπSphereBouquetCofib α))
      (help α (cong fst e))})
      ((e3 (suc n) (fst X)
      hX
      (subCW (4 +ℕ n) ((fst X)
        , ((hX .fst .fst , hX .fst .snd .fst)
        , invEquiv (hX .snd))) .snd)))
      where
      help : (α : SphereBouquet∙ (suc (suc n))
               (Fin (fst (fst (snd (fst hX))) (suc (suc (suc n)))))
               →∙
               SphereBouquet∙ (suc (suc n))
               (Fin (fst (fst (snd (fst hX))) (suc (suc n)))))
               (e : fst hX .fst (suc (suc (suc (suc n)))) ≡ cofib (fst α))
            → ∥ PathP (λ i → e (~ i)) (inl tt) x* ∥₁
      help α e = TR.rec squash₁ ∣_∣₁
        (isConnectedPathP _ cX' _ _ .fst)

  isFPGuy : ∥ FinitePresentation (Group→AbGroup (π'Gr (suc n) X) (π'-comm n)) ∥₁
  isFPGuy = PT.map (λ fp → subst FinitePresentation (AbGroupPath _ _ .fst firstEquiv) fp) isFPGuy1

main : (X : Pointed ℓ-zero) (cwX : isCW (fst X)) (n : ℕ) (cX : isConnected (3 +ℕ n) (typ X))
  → ∥ FinitePresentation (Group→AbGroup (π'Gr (suc n) X) (π'-comm n)) ∥₁
main X cwX n cX =
  PT.rec squash₁ (λ a →
  PT.rec squash₁ (λ b →
  PT.rec squash₁ (λ c →
  PT.rec squash₁ (isFPGuy X n a cX b c)
    (TR.rec (isProp→isOfHLevelSuc (suc n) squash₁) ∣_∣₁ (isConnectedPath _ cX _ _ .fst)))
    (TR.rec (isOfHLevelSuc 1 squash₁) ∣_∣₁ (b .fst)))
    ∣ connectedFunPresConnected 2
       {f = fst (a .snd) ∘ CW↪∞ (a .fst .fst , a .fst .snd .fst) (4 +ℕ n)}
         (isConnectedSubtr' (suc n) 2 cX)
         (isConnectedComp (a .snd .fst) _ _ (isEquiv→isConnected _ (snd (snd a)) 2)
         λ b → isConnectedSubtr' (suc (suc n)) 2
                 ((isConnected-CW↪∞ (4 +ℕ n) (a .fst .fst , a .fst .snd .fst)) b)) ∣₁)
    (makeConnectedCW (1 +ℕ n) cwX cX)
