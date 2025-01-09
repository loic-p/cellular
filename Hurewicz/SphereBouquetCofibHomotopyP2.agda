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



open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.Connected
open import Cubical.CW.Homology
open import Cubical.CW.Subcomplex


open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence


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
-- open import Cubical.Homotopy.Group.Properties

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

open import Hurewicz.random
open import Hurewicz.AbPath


open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Pushout as PO


open import Cubical.Algebra.Group.Subgroup
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.S1
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.HITs.FreeAbGroup.Base

open import Cubical.Algebra.Group.Free
open import Cubical.Data.List renaming ([_] to [_]L)



open import Cubical.HITs.Bouquet as Bouq
open import Cubical.HITs.Bouquet.Discrete



open import Cubical.HITs.FreeGroup as FG
open import Cubical.HITs.FreeGroup.NormalForm
open import Cubical.HITs.FreeGroupoid.Properties
open import Cubical.Algebra.Group.Free


open import Hurewicz.SphereBouquetCofibHomotopy

open import Cubical.Algebra.Group.GroupPath


-- -- Homs are equal if they agree on generators


-- (AbGroup→Group ℤ[Fin c2 ])
--                   / (imSubgroup (bouquetDegree α)
--                   , isNormalIm (bouquetDegree α)
--                     λ _ _ → AbGroupStr.+Comm (snd ℤ[Fin c2 ]) _ _)


agreeOnℤFinGenerator→≡' : ∀ {ℓ} {n : ℕ} (G : Group ℓ)
  → {ϕ ψ : GroupHom (AbGroup→Group (ℤ[Fin n ])) G}
  → ((x : _) → fst ϕ (ℤFinGenerator x) ≡ fst ψ (ℤFinGenerator x))
  → ϕ ≡ ψ
agreeOnℤFinGenerator→≡' G {ϕ} {ψ} w =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
   (funExt
    (elimPropℤFin _ _ (λ _ → isOfHLevelPath' 1 (GroupStr.is-set (snd G)) _ _)
      (IsGroupHom.pres1 (snd ϕ) ∙ sym (IsGroupHom.pres1 (snd ψ)))
      w
      (λ f g p q → IsGroupHom.pres· (snd ϕ) f g
                 ∙∙ (λ i → GroupStr._·_ (snd G) (p i) (q i))
                 ∙∙ sym (IsGroupHom.pres· (snd ψ) f g ))
      λ f p → IsGroupHom.presinv (snd ϕ) f
           ∙∙ cong (GroupStr.inv (G .snd) ) p
           ∙∙ sym (IsGroupHom.presinv (snd ψ) f)))


ℤ[]/-GroupHom≡ : ∀ {ℓ} {n : ℕ} (G : Group ℓ)
  {Q : NormalSubgroup (AbGroup→Group ℤ[Fin n ])}
  → (ϕ ψ : GroupHom (AbGroup→Group (ℤ[Fin n ]) / Q ) G)
 → ((k : _) → fst ϕ [ ℤFinGenerator k ] ≡ fst ψ [ ℤFinGenerator k ])
 → ϕ ≡ ψ 
ℤ[]/-GroupHom≡ G ϕ ψ s = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
  (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd G) _ _)
    λ x → funExt⁻ (cong fst (agreeOnℤFinGenerator→≡' G
      {ϕ = compGroupHom ([_] , makeIsGroupHom λ f g → refl) ϕ}
      {ψ = compGroupHom ([_] , makeIsGroupHom λ f g → refl) ψ}
      s)) x))


makeℤ[]/Equiv : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'} {n : ℕ}
  {T : NormalSubgroup (AbGroup→Group ℤ[Fin n ])}
  (ϕ : GroupEquiv (AbGroup→Group ℤ[Fin n ] / T) G)
  (ψ : GroupEquiv (AbGroup→Group ℤ[Fin n ] / T) H)
  (m : GroupHom G H)
  → ((k : _) → fst m (fst (fst ϕ) [ ℤFinGenerator k ])
               ≡ fst (fst ψ) [ ℤFinGenerator k ])
  → isEquiv (fst m)
makeℤ[]/Equiv {n = n} {T = T} ϕ ψ m ind =
  subst isEquiv (cong fst altt) (compEquiv (invEquiv (fst ϕ)) (fst ψ) .snd)
  where
  alt : GroupHom (AbGroup→Group ℤ[Fin n ] / T) (AbGroup→Group ℤ[Fin n ] / T)
  alt = compGroupHom (GroupEquiv→GroupHom ϕ)
          (compGroupHom m (GroupEquiv→GroupHom (invGroupEquiv ψ)))

  lem : alt ≡ idGroupHom
  lem = ℤ[]/-GroupHom≡ _ _ _
    λ w → cong (invEq (fst ψ)) (ind w)
         ∙ retEq (fst ψ) [ ℤFinGenerator w ]

  altt : compGroupHom (GroupEquiv→GroupHom (invGroupEquiv ϕ)) (GroupEquiv→GroupHom ψ) ≡ m
  altt = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt λ x → 
      (sym (funExt⁻ (cong fst (cong (compGroupHom (GroupEquiv→GroupHom (invGroupEquiv ϕ)))
                (cong (λ X → compGroupHom X (GroupEquiv→GroupHom ψ)) lem))) x))
                ∙ secEq (fst ψ) _
                ∙ cong (fst m) (secEq (fst ϕ) x))

module _ {n m k : ℕ} (α : SphereBouquet∙ (suc n) (Fin m)
                       →∙ SphereBouquet∙ (suc n) (Fin k)) where

  preπSphereBouquet/Generator : (k : Fin k) → (S₊∙ (suc n) →∙ (cofib (fst α) , inl tt))
  preπSphereBouquet/Generator k =
       (λ x → inr (inr (k , x)))
    , (λ i → inr (push k (~ i))) ∙ (λ i → inr (snd α (~ i))) ∙ sym (push (inl tt))

  πSphereBouquet/Generator : (k : Fin k) → π'Gr n (cofib (fst α) , inl tt) .fst
  πSphereBouquet/Generator k =
     ∣ preπSphereBouquet/Generator k  ∣₂

  πᵃᵇSphereBouquet/Generator : (k : Fin k) → Abelianization (π'Gr n (cofib (fst α) , inl tt))
  πᵃᵇSphereBouquet/Generator k = η (πSphereBouquet/Generator k)

πₙ⋁Sⁿ≅ℤ[]Generator : (n k : ℕ) (w : Fin k)
  → fst (GroupIso→GroupHom (πₙ⋁Sⁿ≅ℤ[] n k))
      ∣ (λ x → inr (w , x)) , (λ i → push w (~ i)) ∣₂
  ≡ ℤFinGenerator w
πₙ⋁Sⁿ≅ℤ[]Generator n (suc k) w = πₙ⋁Sⁿ≅ℤ[]Gen _ _ _

private
  Preπ'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree : {n m k : ℕ}
    (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
    → Σ[ ϕ ∈ (GroupIso (AbGroup→Group (AbelianizationAbGroup (π'Gr n (cofib (fst α) , inl tt))))
               (AbGroup→Group ℤ[Fin k ]
             / ((imSubgroup (bouquetDegree (fst α)))
             , (isNormalIm _ (λ f g i x → +Comm (f x) (g x) i))))) ]
         ((w : Fin k) → Iso.fun (fst ϕ) (πᵃᵇSphereBouquet/Generator α w) ≡ [ ℤFinGenerator w ])
  Preπ'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree {n = zero} {m} {k} α =
    lem (Iso.inv (compIso (invIso CharacBouquet→∙Bouquet) sphereBouqetMapIso) α) α
         (Iso.rightInv (compIso (invIso CharacBouquet→∙Bouquet) sphereBouqetMapIso) α)
    where
    Goal : (α : _) (s : (w : _) → _) → Type
    Goal α s =
      Σ[ ϕ ∈ (GroupIso (AbGroup→Group (AbelianizationAbGroup (π'Gr zero (cofib (fst α) , inl tt))))
               (AbGroup→Group ℤ[Fin k ]
             / ((imSubgroup (bouquetDegree (fst α)))
             , (isNormalIm _ (λ f g i x → +Comm (f x) (g x) i))))) ]
         ((w : Fin k) → Iso.fun (fst ϕ) (s w) ≡ [ ℤFinGenerator w ])

    module _ (α' : Fin m → FreeGroup (Fin k)) where
    module _ (α' : Fin m → FreeGroup (Fin k)) where
      open presB α'
      open spB α'
      toF∙ = Iso.fun sphereBouqetMapIso (Iso.inv CharacBouquet→∙Bouquet α')

      toF∙snd : snd toF∙ ≡ refl
      toF∙snd = cong₃ _∙∙_∙∙_ (λ _ → refl)
        (cong (cong (fst (Iso.fun (pre∘∙equiv (invEquiv∙ Bouquet≃∙SphereBouquet))
              (Iso.inv CharacBouquet→∙Bouquet α'))))
              (cong₂ _∙_ (cong sym (cong₂ _∙_ refl (∙∙lCancel _) ∙ sym (rUnit refl)))
                (cong₃ _∙∙_∙∙_ (sym (rUnit _)
                  ∙ cong (cong (Iso.inv (invIso (equivToIso (fst Bouquet≃∙SphereBouquet)))))
                         lemma ∙ refl) refl (sym (rUnit _))
                ∙ sym (rUnit refl))
              ∙ sym (rUnit refl) ))
        (cong₃ _∙∙_∙∙_ refl refl
          (sym (lUnit _) ∙ ∙∙lCancel _))
          ∙ cong₃ _∙∙_∙∙_ refl refl (sym (rUnit refl))
          ∙ sym (rUnit refl)
         where
         lemma : Iso.rightInv (invIso (equivToIso (fst Bouquet≃∙SphereBouquet))) (
              (fst
               (isoToEquiv (invIso (equivToIso (fst Bouquet≃∙SphereBouquet))))
               (pt (Bouquet∙ (Fin m))))) ≡ refl
         lemma = ∙∙lCancel _

      module _ (lock : lockUnit {ℓ-zero}) where
          rIs = (fst (invGroupIso (π'BoquetFunCofib≅Free/Imα>1-Lock lock)))
          r = GroupIso→GroupHom (invGroupIso (π'BoquetFunCofib≅Free/Imα>1-Lock lock))

      η' : _ → Abelianization (π'Gr 0 (cofib (fst toF∙) , inl tt))
      η' = η

      presGen : (lock : _) (w : Fin k) (t : _) (p : t ≡ πᵃᵇSphereBouquet/Generator toF∙ w)
        → Iso.inv (rIs lock) t ≡ [ ℤFinGenerator w ]
      presGen l w t p =
        (π'BoquetFunCofib≅Free/Imα>1-LockComp l t
         ∙ cong (Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock l)))
            (rw l))
          ∙ tss l
        where
        tss : (l : _) → Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock l)) [ η (η w) ] ≡ [ ℤFinGenerator w ]
        tss unlock = refl 
        rw' : Iso.inv (helpIso-Lock unlock .fst) [ η (η w) ] ≡ πᵃᵇSphereBouquet/Generator toF∙ w
        rw' = cong η' (cong ∣_∣₂
          (ΣPathP (funExt
          (λ { base i → inr (push w i)
            ; (loop i) j → inr (doubleCompPath-filler (push w) (λ j → inr (w , loop j)) (sym (push w)) (~ j) i)})
            , ((sym (lUnit (sym (push (inl tt)))))
            ◁ compPath-filler' (λ i → inr (push w (~ i))) (sym (push (inl tt))))
            ▷ (cong₂ _∙_ refl (lUnit (sym (push (inl tt))))))
          ∙ λ i → preπSphereBouquet/Generator (toF , toF∙snd (~ i)) w))

        rw : (l : _) → Iso.fun (helpIso-Lock l .fst) t ≡ [ η (η w) ]
        rw = λ {unlock → cong (Iso.fun (helpIso-Lock unlock .fst)) p
           ∙ cong (Iso.fun (helpIso-Lock unlock .fst)) (sym rw')
           ∙ Iso.rightInv (helpIso-Lock unlock .fst) [ η (η w) ]}

        presGen' : (lock : _) (w : Fin k)
          → Iso.inv (rIs lock) (πᵃᵇSphereBouquet/Generator toF∙ w) ≡ [ ℤFinGenerator w ]
        presGen' l w = presGen l w _ refl

        presGen⁻ : (lock : _)(w : Fin k) → Iso.fun (rIs lock) [ ℤFinGenerator w ] ≡ (πᵃᵇSphereBouquet/Generator toF∙ w)
        presGen⁻ lock w = cong (Iso.fun (rIs lock)) (sym (presGen lock w _ refl))
                   ∙ Iso.rightInv (rIs lock) (πᵃᵇSphereBouquet/Generator toF∙ w)

      abstract
        rIs' : (lock : lockUnit {ℓ-zero}) → GroupIso 
                            (AbGroup→Group ℤ[Fin k ]
                          / ((imSubgroup (bouquetDegree toF))
                          , (isNormalIm _ (λ f g i x → +Comm (f x) (g x) i))))
                          (AbGroup→Group (AbelianizationAbGroup (π'Gr zero (cofib toF , inl tt))))
        rIs' l = rIs l , isGroupHomInv (GroupIso→GroupEquiv (π'BoquetFunCofib≅Free/Imα>1-Lock l))

      G : lockUnit → (a : (w : _) → _)
        → (t : (w : _) → a w ≡ (πᵃᵇSphereBouquet/Generator toF∙ w))
        → Goal toF∙ a
      fst (G l a t) = π'BoquetFunCofib≅Free/Imα>1-Lock l
      snd (G l a t) w = cong (Iso.inv (rIs l)) (t w) ∙ presGen l w _ refl


    lem : (w : Fin m → FreeGroup (Fin k))
          (α : SphereBouquet∙ (suc zero) (Fin m) →∙ SphereBouquet∙ (suc zero) (Fin k))
          (s : Iso.fun sphereBouqetMapIso (Iso.inv CharacBouquet→∙Bouquet w) ≡ α)
         → Goal α (πᵃᵇSphereBouquet/Generator α)
    lem w = J> G w unlock _ (λ _ → refl)
  Preπ'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree {n = suc n} {m} {k} α =
    →Goal unlock _ (λ _ → refl)
    where
    open πCofibBouquetMap _ _ _ α
    open import Cubical.Algebra.Group.IsomorphismTheorems

    eEqL : (lock : lockUnit {ℓ-zero})
      → GroupIso ( (π'Gr (suc n) (cofib (fst α) , inl tt)))
               (AbGroup→Group ℤ[Fin k ]
             / ((imSubgroup (bouquetDegree (fst α)))
             , (isNormalIm _ (λ f g i x → +Comm (f x) (g x) i))))
    eEqL unlock = π'CofibBouquetMap≅ℤ[]/BouquetDegree α

    eEq : (lock : lockUnit {ℓ-zero}) → _
    eEq lock = invGroupIso (eEqL lock)

    eHom = GroupIso→GroupHom (eEq unlock)


    eEqElem : (l : _) (f : _) → Iso.inv (fst (eEq l)) f
                      ≡ (Iso.fun (fst (πCofibBouquetMap.Iso3 _ _ _ α)))
                         ((Iso.fun (fst (πCofibBouquetMap.Iso2 _ _ _ α)))
                           ((Iso.fun (fst (πCofibBouquetMap.Iso1 _ _ _ α))) f))
    eEqElem unlock f = refl

    eEqElem' : (f : _) (r : _) (q : _)
      → Iso.fun (fst (surjImIso (π'∘∙Hom (suc n) inr') surjectiveα)) (∣ r ∣₂ , ∣ q ∣₁) ≡ ∣ f ∣₂
      → (Iso.fun (fst (πCofibBouquetMap.Iso3 _ _ _ α)))
                           ((Iso.fun (fst (πCofibBouquetMap.Iso2 _ _ _ α)))
                             ((Iso.fun (fst (πCofibBouquetMap.Iso1 _ _ _ α))) ∣ f ∣₂))
                      ≡ [ fst (GroupIso→GroupHom (πₙ⋁Sⁿ≅ℤ[] n k)) (fst q) ]
    eEqElem' f r q t =
        cong (Iso.fun (fst (πCofibBouquetMap.Iso3 n k _ α)))
             (cong (Iso.fun (fst (πCofibBouquetMap.Iso2 n k _ α)))
               (cong (Iso.fun (fst (isoThm1 _)))
                 (sym (cong (Iso.inv (fst (surjImIso (π'∘∙Hom (suc n) inr') surjectiveα))) t)
               ∙ (Iso.leftInv (fst (surjImIso (π'∘∙Hom (suc n) inr') surjectiveα)) (∣ r ∣₂ , ∣ q ∣₁)))))
           ∙ cong [_] refl

    eHomGen : (l : _) (w : _) → Iso.inv (fst (eEq l)) (πSphereBouquet/Generator α w)
                      ≡ [ ℤFinGenerator  w ]
    eHomGen l w = (eEqElem l (∣ preπSphereBouquet/Generator α w ∣₂)
      ∙ eEqElem' _ (preπSphereBouquet/Generator α w)
                   (∣ (λ x → inr (w , x)) , sym (push w) ∣₂ , refl)
                   refl)
       ∙ cong [_] (πₙ⋁Sⁿ≅ℤ[]Generator n k w)

    eHomGen' : (l : lockUnit {ℓ-zero}) (w : _) (s : _) (q : πSphereBouquet/Generator α w ≡ s)
      → Iso.fun (fst (eEqL l)) s  ≡ [ ℤFinGenerator  w ]
    eHomGen' l w = J> eHomGen l w

    Goal : (s : (w : _) → _) → Type
    Goal s =
      Σ[ ϕ ∈ (GroupIso (AbGroup→Group (AbelianizationAbGroup (π'Gr (suc n) (cofib (fst α) , inl tt))))
               (AbGroup→Group ℤ[Fin k ]
             / ((imSubgroup (bouquetDegree (fst α)))
             , (isNormalIm _ (λ f g i x → +Comm (f x) (g x) i))))) ]
         ((w : Fin k) → Iso.fun (fst ϕ) (s w) ≡ [ ℤFinGenerator w ])

    →Goal : lockUnit {ℓ-zero} → (s : (w : _) → _)
            (p : (w : _) → s w ≡ πᵃᵇSphereBouquet/Generator α w) → Goal s
    fst (→Goal l s p) =
      compGroupIso (invGroupIso (AbelianizationIdempotent (Group→AbGroup _ (π'-comm _))))
                   (eEqL l)
    snd (→Goal l s p) w =
      cong (Iso.fun (fst (eEqL l)))
         (cong (Iso.inv (fst (AbelianizationIdempotent (Group→AbGroup _ (π'-comm _))))) (p w))
      ∙ eHomGen' l w _ refl

module _ {n m k : ℕ}
  (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k)) where
  π'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree :
    GroupIso (AbGroup→Group (AbelianizationAbGroup (π'Gr n (cofib (fst α) , inl tt))))
               (AbGroup→Group ℤ[Fin k ]
             / ((imSubgroup (bouquetDegree (fst α)))
             , (isNormalIm _ (λ f g i x → +Comm (f x) (g x) i))))
  π'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree =
    fst (Preπ'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree α)

  π'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegreePresGens : (w : Fin k) →
    Iso.fun (fst π'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree)
      (πᵃᵇSphereBouquet/Generator α w) ≡ [ ℤFinGenerator w ]
  π'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegreePresGens = snd (Preπ'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree α)


  -- ϕ'≡ψ' : ϕ' ≡ ψ'
  -- ϕ'≡ψ' = ℤ[]/-GroupHom≡ _ ϕ' ψ'
  --   λ w → cong (fst ϕ ∘ η) (sym (lem w))
  --        ∙ ind w
  --        ∙ cong (fst ψ ∘ η) (lem w)
  --   where
  --   lem : (w : Fin k) → _
  --   lem w = sym (Iso.rightInv (fst eEq) (πSphereBouquet/Generator α w))
  --        ∙  cong (Iso.fun (fst eEq)) (eHomGen w)

open import Hurewicz.SphereBouquetCofib2
Badoo! : {n m k : ℕ} (α : SphereBouquet∙ (suc n) (Fin m)
                       →∙ SphereBouquet∙ (suc n) (Fin k))
  (ϕ : GroupHom (AbGroup→Group (AbelianizationAbGroup
                  (π'Gr n (cofib (fst α) , inl tt))))
                (Hˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ (fst α)) n))
  → ((k : _) → fst ϕ (πᵃᵇSphereBouquet/Generator α k)
               ≡ genHˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ (fst α) k)
  → isEquiv (fst ϕ)
Badoo! α ϕ hyp =
  makeℤ[]/Equiv
    (GroupIso→GroupEquiv
      (invGroupIso (π'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree α)))
    (GroupIso→GroupEquiv
      (invGroupIso (GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap (fst α)))) ϕ
      λ k → cong (fst ϕ)
          (sym (cong (Iso.inv (fst (π'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree α)))
            (π'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegreePresGens α k))
          ∙ Iso.leftInv (fst (π'ᵃᵇCofibBouquetMap≅ℤ[]/BouquetDegree α)) _)
        ∙ hyp k
        ∙ sym (Iso.leftInv (fst (GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap (fst α)))
          (genHˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ (fst α) k))
        ∙ cong (ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/ (fst α))
          (isGen-genHˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ (fst α) k)



-- πSphereBouquet/-GroupHom≡ : {n m k : ℕ} (G : Group ℓ-zero)
--   (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
--   (ϕ ψ : GroupHom ((AbGroup→Group (AbelianizationAbGroup (π'Gr n (cofib (fst α) , inl tt))))) G)
--   (ind : (w : _) → fst ϕ (πᵃᵇSphereBouquet/Generator α w)
--                   ≡ fst ψ (πᵃᵇSphereBouquet/Generator α w))
--   → ϕ ≡ ψ 
-- πSphereBouquet/-GroupHom≡ {n = zero} {m} {k} G α ϕ ψ ind =
--   lem (Iso.inv (compIso (invIso CharacBouquet→∙Bouquet) sphereBouqetMapIso) α) α
--       (Iso.rightInv (compIso (invIso CharacBouquet→∙Bouquet) sphereBouqetMapIso) α)
--       ϕ ψ ind
--   where

--   module _ (α' : Fin m → FreeGroup (Fin k)) where
--     open presB α'
--     open spB α'
--     toF∙ = Iso.fun sphereBouqetMapIso (Iso.inv CharacBouquet→∙Bouquet α')

--     toF∙snd : snd toF∙ ≡ refl
--     toF∙snd = cong₃ _∙∙_∙∙_ (λ _ → refl)
--       (cong (cong (fst (Iso.fun (pre∘∙equiv (invEquiv∙ Bouquet≃∙SphereBouquet))
--             (Iso.inv CharacBouquet→∙Bouquet α'))))
--             (cong₂ _∙_ (cong sym (cong₂ _∙_ refl (∙∙lCancel _) ∙ sym (rUnit refl)))
--               (cong₃ _∙∙_∙∙_ (sym (rUnit _)
--                 ∙ cong (cong (Iso.inv (invIso (equivToIso (fst Bouquet≃∙SphereBouquet)))))
--                        lemma ∙ refl) refl (sym (rUnit _))
--               ∙ sym (rUnit refl))
--             ∙ sym (rUnit refl) ))
--       (cong₃ _∙∙_∙∙_ refl refl
--         (sym (lUnit _) ∙ ∙∙lCancel _))
--         ∙ cong₃ _∙∙_∙∙_ refl refl (sym (rUnit refl))
--         ∙ sym (rUnit refl)
--        where
--        lemma : Iso.rightInv (invIso (equivToIso (fst Bouquet≃∙SphereBouquet))) (
--             (fst
--              (isoToEquiv (invIso (equivToIso (fst Bouquet≃∙SphereBouquet))))
--              (pt (Bouquet∙ (Fin m))))) ≡ refl
--        lemma = ∙∙lCancel _

--     module _ (ϕ ψ : GroupHom (AbGroup→Group (AbelianizationAbGroup (π'Gr zero (cofib toF , inl tt)))) G)
--       (ind : (w : _) → fst ϕ (πᵃᵇSphereBouquet/Generator toF∙ w)
--                       ≡ fst ψ (πᵃᵇSphereBouquet/Generator toF∙ w)) where

--       module _ (lock : lockUnit {ℓ-zero}) where 
--         rIs = (fst (invGroupIso (π'BoquetFunCofib≅Free/Imα>1-Lock lock)))
--         r = GroupIso→GroupHom (invGroupIso (π'BoquetFunCofib≅Free/Imα>1-Lock lock))

--         ϕ' ψ' : GroupHom _ _
--         ϕ' = compGroupHom r ϕ
--         ψ' = compGroupHom r ψ

--       η' : _ → Abelianization (π'Gr 0 (cofib (fst toF∙) , inl tt))
--       η' = η


--       presGen : (lock : _) (w : Fin k) (t : _) (p : t ≡ πᵃᵇSphereBouquet/Generator toF∙ w)
--         → Iso.inv (rIs lock) t ≡ [ ℤFinGenerator w ]
--       presGen l w t p =
--         (π'BoquetFunCofib≅Free/Imα>1-LockComp l t
--          ∙ cong (Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock l)))
--             (rw l))
--           ∙ tss l
--         where
--         tss : (l : _) → Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock l)) [ η (η w) ] ≡ [ ℤFinGenerator w ]
--         tss unlock = refl 
--         rw' : Iso.inv (helpIso-Lock unlock .fst) [ η (η w) ] ≡ πᵃᵇSphereBouquet/Generator toF∙ w
--         rw' = cong η' (cong ∣_∣₂
--           (ΣPathP (funExt
--           (λ { base i → inr (push w i)
--             ; (loop i) j → inr (doubleCompPath-filler (push w) (λ j → inr (w , loop j)) (sym (push w)) (~ j) i)})
--             , ((sym (lUnit (sym (push (inl tt)))))
--             ◁ compPath-filler' (λ i → inr (push w (~ i))) (sym (push (inl tt))))
--             ▷ (cong₂ _∙_ refl (lUnit (sym (push (inl tt))))))
--           ∙ λ i → preπSphereBouquet/Generator (toF , toF∙snd (~ i)) w))

--         rw : (l : _) → Iso.fun (helpIso-Lock l .fst) t ≡ [ η (η w) ]
--         rw = λ {unlock → cong (Iso.fun (helpIso-Lock unlock .fst)) p
--            ∙ cong (Iso.fun (helpIso-Lock unlock .fst)) (sym rw')
--            ∙ Iso.rightInv (helpIso-Lock unlock .fst) [ η (η w) ]}

--       presGen⁻ : (lock : _)(w : Fin k) → Iso.fun (rIs lock) [ ℤFinGenerator w ] ≡ (πᵃᵇSphereBouquet/Generator toF∙ w)
--       presGen⁻ lock w = cong (Iso.fun (rIs lock)) (sym (presGen lock w _ refl))
--                  ∙ Iso.rightInv (rIs lock) (πᵃᵇSphereBouquet/Generator toF∙ w)

--       mainLemma : (l : _) → ϕ' l ≡ ψ' l
--       mainLemma l = ℤ[]/-GroupHom≡ _ _ _
--         λ k → cong (fst ϕ) (presGen⁻ l k) ∙ ind k ∙ sym (cong (fst ψ) (presGen⁻ l k))
  
--       main : ϕ ≡ ψ
--       main = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
--         (funExt λ x → sym (cong (ϕ .fst) (Iso.rightInv (rIs unlock) x))
--         ∙ funExt⁻ (cong fst (mainLemma unlock)) (Iso.inv (rIs unlock) x)
--         ∙ cong (ψ .fst) (Iso.rightInv (rIs unlock) x))

--   lem : (w : Fin m → FreeGroup (Fin k))
--         (α : SphereBouquet∙ (suc zero) (Fin m) →∙ SphereBouquet∙ (suc zero) (Fin k))
--         (s : Iso.fun sphereBouqetMapIso (Iso.inv CharacBouquet→∙Bouquet w) ≡ α)
--         (ϕ ψ : GroupHom ((AbGroup→Group (AbelianizationAbGroup (π'Gr zero (cofib (fst α) , inl tt))))) G)
--         (ind : (w : _) → fst ϕ (πᵃᵇSphereBouquet/Generator α w)
--                         ≡ fst ψ (πᵃᵇSphereBouquet/Generator α w))
--         → ϕ ≡ ψ 
--   lem w = J> (main w)
-- πSphereBouquet/-GroupHom≡ {n = suc n} {k = k} G α ϕ ψ ind =
--   Σ≡Prop (λ _ → isPropIsGroupHom _ _)
--     (funExt (Abi.elimProp _ (λ _ → GroupStr.is-set (snd G) _ _)
--     λ g → (cong (fst ϕ) λ i → η (Iso.rightInv (fst eEq) g (~ i)))
--         ∙ funExt⁻ (cong fst (ϕ'≡ψ')) (Iso.inv (fst eEq) g)
--         ∙ cong (fst ψ) λ i → η (Iso.rightInv (fst eEq) g i)))
--   where
--   open πCofibBouquetMap _ _ _ α
--   open import Cubical.Algebra.Group.IsomorphismTheorems
--   eEq = invGroupIso (π'CofibBouquetMap≅ℤ[]/BouquetDegree α)
--   eHom = GroupIso→GroupHom eEq

--   ϕ' = compGroupHom (compGroupHom eHom (AbelianizationGroupStructure.ηAsGroupHom _)) ϕ
--   ψ' = compGroupHom (compGroupHom eHom (AbelianizationGroupStructure.ηAsGroupHom _)) ψ


--   eEqElem : (f : _) → Iso.inv (fst eEq) f
--                     ≡ (Iso.fun (fst (πCofibBouquetMap.Iso3 _ _ _ α)))
--                        ((Iso.fun (fst (πCofibBouquetMap.Iso2 _ _ _ α)))
--                          ((Iso.fun (fst (πCofibBouquetMap.Iso1 _ _ _ α))) f))
--   eEqElem = λ f → refl

--   eEqElem' : (f : _) (r : _) (q : _)
--     → Iso.fun (fst (surjImIso (π'∘∙Hom (suc n) inr') surjectiveα)) (∣ r ∣₂ , ∣ q ∣₁) ≡ ∣ f ∣₂
--     → (Iso.fun (fst (πCofibBouquetMap.Iso3 _ _ _ α)))
--                          ((Iso.fun (fst (πCofibBouquetMap.Iso2 _ _ _ α)))
--                            ((Iso.fun (fst (πCofibBouquetMap.Iso1 _ _ _ α))) ∣ f ∣₂))
--                     ≡ [ fst (GroupIso→GroupHom (πₙ⋁Sⁿ≅ℤ[] n k)) (fst q) ]
--   eEqElem' f r q t =
--       cong (Iso.fun (fst (πCofibBouquetMap.Iso3 n k _ α)))
--            (cong (Iso.fun (fst (πCofibBouquetMap.Iso2 n k _ α)))
--              (cong (Iso.fun (fst (isoThm1 _)))
--                (sym (cong (Iso.inv (fst (surjImIso (π'∘∙Hom (suc n) inr') surjectiveα))) t)
--              ∙ (Iso.leftInv (fst (surjImIso (π'∘∙Hom (suc n) inr') surjectiveα)) (∣ r ∣₂ , ∣ q ∣₁)))))
--          ∙ cong [_] refl

--   eHomGen : (w : _) → Iso.inv (fst eEq) (πSphereBouquet/Generator α w)
--                     ≡ [ ℤFinGenerator  w ]
--   eHomGen w = (eEqElem (∣ preπSphereBouquet/Generator α w ∣₂)
--     ∙ eEqElem' _ (preπSphereBouquet/Generator α w)
--                  (∣ (λ x → inr (w , x)) , sym (push w) ∣₂ , refl)
--                  refl)
--      ∙ cong [_] (πₙ⋁Sⁿ≅ℤ[]Generator n k w)

--   ϕ'≡ψ' : ϕ' ≡ ψ'
--   ϕ'≡ψ' = ℤ[]/-GroupHom≡ _ ϕ' ψ'
--     λ w → cong (fst ϕ ∘ η) (sym (lem w))
--          ∙ ind w
--          ∙ cong (fst ψ ∘ η) (lem w)
--     where
--     lem : (w : Fin k) → _
--     lem w = sym (Iso.rightInv (fst eEq) (πSphereBouquet/Generator α w))
--          ∙  cong (Iso.fun (fst eEq)) (eHomGen w)

-- module _ {m k : ℕ}
--   (α' : Fin m → FreeGroup (Fin k)) where
--   open spB {m = m} {k = k} α'

--   abstract
--     η' : π'Gr 0 (cofib (fst αSphereBouquet) , inl tt) .fst
--       → fst (AbelianizationAbGroup (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt)))
--     η' = η

--     η'≡ : η' ≡ η
--     η'≡ = refl


--   π'BoquetFunCofib≅Free/Imα>1-onη : (lock : _) (f : S₊∙ 1 →∙ SphereBouquet∙ 1 (Fin k))
--     → Iso.fun (fst (π'BoquetFunCofib≅Free/Imα>1-Lock lock))
--         (η' ∣ (inr ∘ (fst f)) , (λ i → inr (snd f i)) ∙ sym (push (inl tt)) ∣₂)
--      ≡ [  bouquetDegree {m = 1} (fst f ∘ Iso.fun bouquetFin1) .fst (λ _ → 1) ]
--   π'BoquetFunCofib≅Free/Imα>1-onη lock f =
--       -- G ∣ inr ∘ fst f , (λ i → inr (snd f i)) ∙ sym (push (inl tt)) ∣₂
--       cong (Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock lock)) ∘ Iso.fun (fst (helpIso-Lock lock))) (cong η' (f≡altf lock))
--     ∙ T f''
--     ∙ h2 lock f''
--     ∙ cong [_] (cong (λ s → bouquetDegree (s ∘ Iso.fun bouquetFin1) .fst (λ _ → 1)) (cong fst bask))
--     where
--     f→ : lockUnit {ℓ-zero} → (f : S₊∙ 1 →∙ SphereBouquet∙ 1 (Fin k)) → (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt) .fst)
--     f→ unlock f = ∣ (inr ∘ (fst f)) , (λ i → inr (snd f i)) ∙ sym (push (inl tt)) ∣₂

--     altf→ : lockUnit {ℓ-zero} → (f'' : FreeGroup (Fin k)) → (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt) .fst)
--     altf→ unlock f'' = ∣ (inr ∘ Ω→SphereMap 1 (cong Bouquet→SphereBouquet (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f'')) .fst) , sym (push (inl tt)) ∣₂

--     abstract
    
--       f'' : FreeGroup (Fin k)
--       f'' = Iso.fun Iso-ΩS¹Bouquet-FreeGroup (cong SphereBouquet→Bouquet ((SphereMap→Ω 1) f))

--       bask : Ω→SphereMap 1 (cong Bouquet→SphereBouquet (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f''))
--            ≡ f
--       bask = ΣPathP ((funExt (λ { base → sym (snd f)
--                               ; (loop i) j → hah j i}))
--                   , λ i j → snd f (~ i ∨ j))
--         where
--         hah : Square (cong Bouquet→SphereBouquet (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f''))
--                      (cong (fst f) loop) (sym (snd f)) (sym (snd f))
--         hah = (cong (cong Bouquet→SphereBouquet)
--                (Iso.leftInv Iso-ΩS¹Bouquet-FreeGroup (cong SphereBouquet→Bouquet ((SphereMap→Ω 1) f)))
--              ∙ (λ j i → Iso.leftInv Iso-SphereBouquet-Bouquet (SphereMap→Ω 1 f i) j))
--              ◁ symP (doubleCompPath-filler (sym (snd f)) (cong (fst f) loop) (snd f))

--       f≡altf : (lock : _) → f→ lock f ≡ altf→  lock f''
--       f≡altf lock = (λ i → ∣ (inr ∘ (fst (bask (~ i)))) , (λ j → inr (snd (bask (~ i)) j)) ∙ sym (push (inl tt)) ∣₂ )
--              ∙ cong ∣_∣₂ (ΣPathP (refl , sym (lUnit _)))


--     G : (x : _) → Iso.fun (fst (π'BoquetFunCofib≅Free/Imα>1-Lock lock)) (η x)
--                 ≡ Iso.fun (fst (π'BoquetFunCofib≅Free/Imα>1-Lock lock)) (η' x)
--     G = λ x → cong (Iso.fun (fst (π'BoquetFunCofib≅Free/Imα>1-Lock lock))) (sym (funExt⁻ η'≡ x))

--     module _ (f' : FreeGroup (Fin k)) where


--       Ls : (lock : _) → η' (altf→ lock f')
--         ≡ Iso.inv (fst (helpIso-Lock lock)) [ η f' ]
--       Ls unlock = cong η' (cong ∣_∣₂ (ΣPathP (funExt (λ { base → refl ; (loop i) → refl}) , lUnit _)))
--              ∙ funExt⁻ η'≡ _ 


--       LsPre : (lock : _) (x : _) (y : _) → Iso.inv (fst (helpIso-Lock lock)) x ≡ y
--         → Iso.fun (fst (helpIso-Lock lock)) y ≡ x
--       LsPre lock x y p = sym (sym (Iso.rightInv (fst (helpIso-Lock lock)) x)
--                        ∙ cong (Iso.fun (fst (helpIso-Lock lock))) p)

--       Ls' : (lock : _) → Iso.fun (fst (helpIso-Lock lock)) (η' (altf→ lock f'))
--          ≡  [ η f' ]
--       Ls' lock = LsPre lock [ η f' ] (η' (altf→ lock f')) (sym (Ls lock))

--       T : Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock lock))
--             ((Iso.fun (fst (helpIso-Lock lock)) (η' (altf→ lock f'))))
--         ≡ Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock lock)) [ η f' ]
--       T = cong (Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock lock))) (Ls' lock)

--     h2 : (lock : _) (f' : FreeGroup (Fin k))
--       →  Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock lock)) [ η f' ]
--        ≡ [ bouquetDegree {m = 1} (Ω→SphereMap 1
--             (cong Bouquet→SphereBouquet
--               (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f')) .fst ∘ Iso.fun bouquetFin1)
--               .fst (λ _ → 1) ]
--     h2 unlock f' = cong [_]
--       (funExt⁻ (cong fst (freeGroupHom≡ {f = compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _)
--                            (GroupIso→GroupHom (presB.AbFreeGroup≅𝕫[] α' k))}
--                      {g = g , ttt} λ s → funExt (λ k → ℤFinGeneratorComm s k
--                        ∙ HA s k)))
--                      f')
--       where
--       g' : (f' : _) → _
--       g' f' = (Ω→SphereMap 1
--               (cong Bouquet→SphereBouquet (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f'))
--               .fst
--               ∘ Iso.fun bouquetFin1)

--       g : (f' : FreeGroup (Fin k)) → _
--       g f' = bouquetDegree (g' f') .fst (λ _ → 1)

--       LAA : (f h : _) → cong (λ s → g' (f FG.· h) (inr ((zero , tt) , s))) loop
--           ≡ ((refl ∙ refl) ∙∙ cong (λ s → g' f (inr ((zero , tt) , s))) loop ∙∙ (refl ∙ refl))
--           ∙ ((refl ∙ refl) ∙∙ cong (λ s → g' h (inr ((zero , tt) , s))) loop ∙∙ (refl ∙ refl))
--       LAA f h = cong (cong (Bouquet→SphereBouquet)) (InvIso-ΩS¹Bouquet-FreeGroupPresStr f h)
--               ∙ cong-∙ Bouquet→SphereBouquet
--                    (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f) (Iso.inv Iso-ΩS¹Bouquet-FreeGroup h)
--               ∙ cong₂ _∙_ (rUnit _ ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
--                           (rUnit _ ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))

--       ttt : IsGroupHom (freeGroupGroup (Fin k) .snd) g
--           (AbGroupStr→GroupStr (snd ℤ[Fin k ]))
--       ttt = makeIsGroupHom λ f h
--         → (cong (λ p → bouquetDegree p .fst (λ _ → pos (suc zero)))
--                 ((λ _ → g' (f FG.· h))
--                 ∙ funExt (λ { (inl x) → refl
--                             ; (inr ((zero , tt) , base)) → refl
--                             ; (inr ((zero , tt) , loop i)) j → LAA f h j i
--                             ; (push (zero , tt) i) → refl})
--                 ∙ λ _ → fst (SphereBouquet∙Π (g' f , refl) (g' h , refl))) )
--         ∙ funExt⁻ (cong fst (bouquetDegree+ _ _ _
--             (g' f , refl) (g' h , refl))) (λ _ → 1)

--       HA : (s : Fin k) (k : _) → ℤFinGenerator k s ≡ g (η s) k
--       HA s k with (fst k ≟ᵗ fst s)
--       ... | lt x = refl
--       ... | eq x = refl
--       ... | gt x = refl


--   {-
--       cong (Iso.fun (fst (π'BoquetFunCofib≅Free/Imα>1-Lock lock)) ∘ η') f≡altf
--     ∙ Ls'' f'' lock
--     ∙ h2 f''
--     ∙ ? -- λ i → [ bouquetDegree (fst (bask i) ∘ Iso.fun bouquetFin1) .fst (λ _ → 1) ]
--     where
--     η' : π'Gr 0 (cofib (fst αSphereBouquet) , inl tt) .fst
--       → fst (AbelianizationAbGroup (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt)))
--     η' = η

--     f→ : (f : S₊∙ 1 →∙ SphereBouquet∙ 1 (Fin k)) → (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt) .fst)
--     f→ f = ∣ (inr ∘ (fst f)) , (λ i → inr (snd f i)) ∙ sym (push (inl tt)) ∣₂

--     altf→ : (f'' : FreeGroup (Fin k)) → (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt) .fst)
--     altf→ f'' = ∣ (inr ∘ Ω→SphereMap 1 (cong Bouquet→SphereBouquet (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f'')) .fst) , sym (push (inl tt)) ∣₂

--     abstract
--       f'' : FreeGroup (Fin k)
--       f'' = Iso.fun Iso-ΩS¹Bouquet-FreeGroup (cong SphereBouquet→Bouquet ((SphereMap→Ω 1) f))

--       bask : Ω→SphereMap 1 (cong Bouquet→SphereBouquet (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f''))
--            ≡ f
--       bask = ΣPathP ((funExt (λ { base → sym (snd f)
--                               ; (loop i) j → hah j i}))
--                   , λ i j → snd f (~ i ∨ j))
--         where
--         hah : Square (cong Bouquet→SphereBouquet (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f''))
--                      (cong (fst f) loop) (sym (snd f)) (sym (snd f))
--         hah = (cong (cong Bouquet→SphereBouquet)
--                (Iso.leftInv Iso-ΩS¹Bouquet-FreeGroup (cong SphereBouquet→Bouquet ((SphereMap→Ω 1) f)))
--              ∙ (λ j i → Iso.leftInv Iso-SphereBouquet-Bouquet (SphereMap→Ω 1 f i) j))
--              ◁ symP (doubleCompPath-filler (sym (snd f)) (cong (fst f) loop) (snd f))

--       f≡altf : f→ f ≡ altf→ f''
--       f≡altf = (λ i → ∣ (inr ∘ (fst (bask (~ i)))) , (λ j → inr (snd (bask (~ i)) j)) ∙ sym (push (inl tt)) ∣₂ )
--              ∙ cong ∣_∣₂ (ΣPathP (refl , sym (lUnit _)))

--     module _ (f' : FreeGroup (Fin k)) where
--       Ls : (lock : _) → η' (altf→ f')
--         ≡ Iso.inv (fst (helpIso-Lock lock)) [ η f' ]
--       Ls unlock = cong η' (cong ∣_∣₂ (ΣPathP (funExt (λ { base → refl ; (loop i) → refl}) , lUnit _)))

--       Ls' : (lock : _) → Iso.fun (fst (helpIso-Lock lock)) (η' (altf→ f'))
--          ≡  [ η f' ]
--       Ls' lock = cong (Iso.fun (fst (helpIso-Lock lock))) (Ls lock)
--                ∙ Iso.rightInv (fst (helpIso-Lock lock)) [ η f' ]

--       Ls'' : (lock : _) → Iso.fun (fst (π'BoquetFunCofib≅Free/Imα>1-Lock lock)) (η' (altf→ f'))
--                          ≡ Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock lock)) [ η f' ]
--       Ls'' lock = π'BoquetFunCofib≅Free/Imα>1-LockComp lock (η' (altf→ f'))
--                 ∙ cong (Iso.fun (fst (Free/Imα≅ℤ[]/ImBouquetDegree-Lock lock))) (Ls' lock)

--     h2 : (f' : FreeGroup (Fin k))
--       →  Iso.fun (fst Free/Imα≅ℤ[]/ImBouquetDegree) [ η f' ]
--        ≡ [ bouquetDegree {m = 1} (Ω→SphereMap 1
--             (cong Bouquet→SphereBouquet
--               (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f')) .fst ∘ Iso.fun bouquetFin1)
--               .fst (λ _ → 1) ]
--     h2 = ?

-- -}

--     {- λ f → cong [_]
--        ({!!}
--        ∙ {!degree!})
--     {- funExt⁻ (cong fst (freeGroupHom≡
--       {f = compGroupHom (compGroupHom (AbelianizationGroupStructure.ηAsGroupHom (freeGroupGroup (Fin k)))
--                         ([_] , makeIsGroupHom (λ _ _ → refl)))
--                         (GroupIso→GroupHom Free/Imα≅ℤ[]/ImBouquetDegree)}
--       {g = {!!}}
--       {!!}))
-- -}
-- -}
