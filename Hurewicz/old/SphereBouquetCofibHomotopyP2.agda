{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.SphereBouquetCofibHomotopyP2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed

open import Cubical.Functions.Morphism



open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Sigma






open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST


open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Foundations.HLevels

open import Cubical.Algebra.AbGroup

open import Cubical.CW.Approximation

open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.CW.ChainComplex
open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties as SQ
open import Cubical.Data.Int renaming (_·_ to _·ℤ_)
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Abelianization.Properties as Abi

open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Unit
open import Cubical.HITs.Wedge


open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup as FAB

open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Pushout as PO




open import Cubical.HITs.Bouquet as Bouq
open import Cubical.HITs.Bouquet.Discrete



open import Cubical.HITs.FreeGroup as FG


open import Cubical.Homotopy.Group.PiSphereBouquet
open import Cubical.Homotopy.Group.PiCofibFinSphereBouquetMap

open import Cubical.Algebra.Group.IsomorphismTheorems

open import Hurewicz.SphereBouquetCofibHomotopy

open Iso renaming (inv to inv')


module _ {n m k : ℕ}
  (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k)) where

  preπ'FinSphereBouquetMapGenerator : (k : Fin k) → S₊∙ (suc n) →∙ cofib∙ (fst α)
  preπ'FinSphereBouquetMapGenerator k =
    (λ x → inr (inr (k , x))) ,
    (λ i → inr (push k (~ i))) ∙ (λ i → inr (snd α (~ i))) ∙ sym (push (inl tt))

  π'FinSphereBouquetMapGenerator : (k : Fin k) → π'Gr n (cofib∙ (fst α)) .fst
  π'FinSphereBouquetMapGenerator k =
     ∣ preπ'FinSphereBouquetMapGenerator k ∣₂

  πᵃᵇFinSphereBouquetMapGenerator : (k : Fin k)
    → Abelianization (π'Gr n (cofib∙ (fst α)))
  πᵃᵇFinSphereBouquetMapGenerator k = η (π'FinSphereBouquetMapGenerator k)

private
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreeMain : {n m k : ℕ}
    (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
    → Σ[ ϕ ∈ GroupIso
               (AbelianizationGroup (π'Gr n (cofib∙ (fst α))))
               (ℤ[Fin k ] /Im (bouquetDegree (fst α))) ]
         ((w : Fin k) → fun (fst ϕ) (πᵃᵇFinSphereBouquetMapGenerator α w)
                      ≡ [ ℤFinGenerator w ])
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreeMain {n = zero} {m} {k} α =
    lem (inv' (compIso (invIso CharacFinBouquetFunIso)
                           Iso-Bouquet→∙-SphereBouquet₁→∙) α) α
         (rightInv (compIso (invIso CharacFinBouquetFunIso)
                                 Iso-Bouquet→∙-SphereBouquet₁→∙) α)
    where
    Goal : (α : _) (s : (w : _) → _) → Type
    Goal α s =
      Σ[ ϕ ∈ GroupIso
               (AbelianizationGroup (π'Gr zero (cofib∙ (fst α))))
               (ℤ[Fin k ] /Im (bouquetDegree (fst α))) ]
         ((w : Fin k) → fun (fst ϕ) (s w) ≡ [ ℤFinGenerator w ])
    module _ (α' : Fin m → FreeGroup (Fin k)) where
      gens→finSphereBouquetMap∙ : SphereBouquet∙ 1 (Fin m)
                               →∙ SphereBouquet∙ 1 (Fin k)
      gens→finSphereBouquetMap∙ = fun Iso-Bouquet→∙-SphereBouquet₁→∙
                                   (inv' CharacFinBouquetFunIso α')

      gens→finSphereBouquetMap∙snd : snd gens→finSphereBouquetMap∙ ≡ refl
      gens→finSphereBouquetMap∙snd = cong₃ _∙∙_∙∙_ (λ _ → refl)
        (cong (cong (fst (fun (pre∘∙equiv (invEquiv∙ Bouquet≃∙SphereBouquet))
              (inv' CharacFinBouquetFunIso α'))))
              (cong₂ _∙_ (cong sym (cong₂ _∙_ refl (∙∙lCancel _) ∙ sym (rUnit refl)))
                (cong₃ _∙∙_∙∙_ (sym (rUnit _)
                  ∙ cong (cong (inv' (invIso (equivToIso (fst Bouquet≃∙SphereBouquet)))))
                         lem) refl (sym (rUnit _))
                ∙ sym (rUnit refl))
              ∙ sym (rUnit refl) ))
        (cong₃ _∙∙_∙∙_ refl refl
          (sym (lUnit _) ∙ ∙∙lCancel _))
          ∙ cong₃ _∙∙_∙∙_ refl refl (sym (rUnit refl))
          ∙ sym (rUnit refl)
         where
         lem : rightInv (invIso (equivToIso (fst Bouquet≃∙SphereBouquet)))
              ((fst (isoToEquiv (invIso (equivToIso (fst Bouquet≃∙SphereBouquet))))
                (pt (Bouquet∙ (Fin m))))) ≡ refl
         lem = ∙∙lCancel _

      module _ (lock : lockUnit {ℓ-zero}) where
        lockIso : Iso _ _
        lockIso =
          fst (invGroupIso ((π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1-Lock α')
                lock))

      η' : _ → Abelianization (π'Gr 0 (cofib∙ (fst gens→finSphereBouquetMap∙)))
      η' = η

      presGen : (lock : _) (w : Fin k) (t : _)
        (p : t ≡ πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w)
        → inv' (lockIso lock) t ≡ [ ℤFinGenerator w ]
      presGen l w t p =
        (cong (fun (fst (Freeᵃᵇ/ImFinBouquetMap≅ℤ[]/ImBouquetDegree-Lock α' l)))
            (lem3 l))
          ∙ lem l
        where
        lem : (l : _)
          → fun (fst (Freeᵃᵇ/ImFinBouquetMap≅ℤ[]/ImBouquetDegree-Lock α' l))
                [ η (η w) ] ≡ [ ℤFinGenerator w ]
        lem unlock = refl

        lem2 : inv' (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock
                      α' unlock .fst) [ η (η w) ]
            ≡ πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w
        lem2 = cong η' (cong ∣_∣₂
          (ΣPathP (funExt
          (λ { base i → inr (push w i)
            ; (loop i) j → inr (doubleCompPath-filler
                                 (push w)
                                 (λ j → inr (w , loop j))
                                 (sym (push w)) (~ j) i)})
            , ((sym (lUnit (sym (push (inl tt)))))
            ◁ compPath-filler' (λ i → inr (push w (~ i))) (sym (push (inl tt))))
            ▷ (cong₂ _∙_ refl (lUnit (sym (push (inl tt))))))
          ∙ λ i → preπ'FinSphereBouquetMapGenerator
                   (gens→finSphereBouquetMap α'
                   , gens→finSphereBouquetMap∙snd (~ i)) w))

        lem3 : (l : _)
          → fun (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock α' l
                  .fst) t ≡ [ η (η w) ]
        lem3 unlock =
            cong (fun (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock
                      α' unlock .fst)) p
          ∙ cong (fun (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock
                      α' unlock .fst)) (sym lem2)
           ∙ rightInv (Freeᵃᵇ/ImFinBouquetMap≅π'₁ᵃᵇCofibFinSphereBouquetMap-Lock
                      α' unlock .fst) [ η (η w) ]

        presGen' : (lock : _) (w : Fin k)
          → inv' (lockIso lock)
                  (πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w)
          ≡ [ ℤFinGenerator w ]
        presGen' l w = presGen l w _ refl

        presGen⁻ : (lock : _)(w : Fin k)
          → fun (lockIso lock) [ ℤFinGenerator w ]
           ≡ (πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w)
        presGen⁻ lock w =
           cong (fun (lockIso lock)) (sym (presGen lock w _ refl))
         ∙ rightInv (lockIso lock)
            (πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w)

      abstract
        lockIso' : (lock : lockUnit {ℓ-zero})
          → GroupIso (ℤ[Fin k ] /Im (bouquetDegree (gens→finSphereBouquetMap α')))
                      (AbelianizationGroup
                        (π'Gr zero (cofib∙ (gens→finSphereBouquetMap α'))))
        fst (lockIso' l) = lockIso l
        snd (lockIso' l) =
          isGroupHomInv (GroupIso→GroupEquiv
            (π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1-Lock α' l))

      G : lockUnit → (a : (w : _) → _) (t : (w : _)
        → a w ≡ (πᵃᵇFinSphereBouquetMapGenerator gens→finSphereBouquetMap∙ w))
        → Goal gens→finSphereBouquetMap∙ a
      fst (G l a t) = π'BoquetFunCofib≅Freeᵃᵇ/ImFinBouquetMap>1-Lock α' l
      snd (G l a t) w = cong (inv' (lockIso l)) (t w) ∙ presGen l w _ refl


    lem : (w : Fin m → FreeGroup (Fin k))
          (α : SphereBouquet∙ (suc zero) (Fin m)
            →∙ SphereBouquet∙ (suc zero) (Fin k))
          (s : fun Iso-Bouquet→∙-SphereBouquet₁→∙
                  (inv' CharacFinBouquetFunIso w) ≡ α)
         → Goal α (πᵃᵇFinSphereBouquetMapGenerator α)
    lem w = J> G w unlock _ (λ _ → refl)
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreeMain {n = suc n} {m} {k} α =
    →Goal unlock _ (λ _ → refl)
    where
    open πCofibFinSphereBouquetMap _ _ _ α

    lockIso : (lock : lockUnit {ℓ-zero})
      → GroupIso (π'Gr (suc n) (cofib∙ (fst α)))
                  (ℤ[Fin k ] /Im (bouquetDegree (fst α)))
    lockIso unlock = π'CofibFinSphereBouquetMap≅ℤ[]/BouquetDegree α

    lockInvIso : (lock : lockUnit {ℓ-zero}) → _
    lockInvIso lock = invGroupIso (lockIso lock)

    lockInvHom = GroupIso→GroupHom (lockInvIso unlock)

    lockInvIso≡ : (l : _) (f : _)
      → inv' (fst (lockInvIso l)) f
       ≡ fun (fst Iso3) (fun (fst Iso2) (fun (fst Iso1) f))
    lockInvIso≡ unlock f = refl

    lockInvIso≡' : (f : _) (r : _) (q : _)
      → fun (fst (surjImIso (π'∘∙Hom (suc n) inr') isSurjective-π'∘∙Hominr))
                   (∣ r ∣₂ , ∣ q ∣₁) ≡ ∣ f ∣₂
      → fun (fst Iso3) (fun (fst Iso2) (fun (fst Iso1) ∣ f ∣₂))
       ≡ [ fst (GroupIso→GroupHom (πₙ⋁Sⁿ≅ℤ[] n k)) (fst q) ]
    lockInvIso≡' f r q t =
        cong (fun (fst (πCofibFinSphereBouquetMap.Iso3 n k _ α)))
             (cong (fun (fst (πCofibFinSphereBouquetMap.Iso2 n k _ α)))
               (cong (fun (fst (isoThm1 _)))
                 (sym (cong (inv' (fst (surjImIso (π'∘∙Hom (suc n) inr')
                                         isSurjective-π'∘∙Hominr))) t)
               ∙ leftInv (fst (surjImIso (π'∘∙Hom (suc n) inr')
                                isSurjective-π'∘∙Hominr))
                                  (∣ r ∣₂ , ∣ q ∣₁))))

    lockInvHomGen : (l : _) (w : _)
      → inv' (fst (lockInvIso l)) (π'FinSphereBouquetMapGenerator α w)
       ≡ [ ℤFinGenerator  w ]
    lockInvHomGen l w =
        lockInvIso≡ l (∣ preπ'FinSphereBouquetMapGenerator α w ∣₂)
      ∙ lockInvIso≡' _ (preπ'FinSphereBouquetMapGenerator α w)
                   (∣ (λ x → inr (w , x)) , sym (push w) ∣₂ , refl)
                   refl
       ∙ cong [_] (πₙ⋁Sⁿ≅ℤ[]Generator _ _ _)

    lockInvHomGen' : (l : lockUnit {ℓ-zero}) (w : _) (s : _)
      (q : π'FinSphereBouquetMapGenerator α w ≡ s)
      → fun (fst (lockIso l)) s  ≡ [ ℤFinGenerator  w ]
    lockInvHomGen' l w = J> lockInvHomGen l w

    Goal : (s : (w : _) → _) → Type
    Goal s =
      Σ[ ϕ ∈ (GroupIso (AbelianizationGroup (π'Gr (suc n) (cofib∙ (fst α))))
                        (ℤ[Fin k ] /Im (bouquetDegree (fst α)))) ]
         ((w : Fin k) → fun (fst ϕ) (s w) ≡ [ ℤFinGenerator w ])

    →Goal : lockUnit {ℓ-zero} → (s : (w : _) → _)
            (p : (w : _) → s w ≡ πᵃᵇFinSphereBouquetMapGenerator α w) → Goal s
    fst (→Goal l s p) =
      compGroupIso (invGroupIso (AbelianizationIdempotent
                                  (Group→AbGroup _ (π'-comm _))))
                   (lockIso l)
    snd (→Goal l s p) w =
      cong (fun (fst (lockIso l)))
         (cong (inv' (fst (AbelianizationIdempotent
                           (Group→AbGroup _ (π'-comm _))))) (p w))
      ∙ lockInvHomGen' l w _ refl

module _ {n m k : ℕ}
  (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k)) where

  -- πₙᵃᵇ(cofib α) ≅ ℤ[]/Im α
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree :
    GroupIso (AbelianizationGroup (π'Gr n (cofib∙ (fst α))))
             (ℤ[Fin k ] /Im (bouquetDegree (fst α)))
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree =
    fst (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreeMain α)

  -- Characterisation of generators
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreePresGens : (w : Fin k) →
    fun (fst π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree)
      (πᵃᵇFinSphereBouquetMapGenerator α w) ≡ [ ℤFinGenerator w ]
  π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreePresGens =
    snd (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreeMain α)
