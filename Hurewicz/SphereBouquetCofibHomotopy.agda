{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.SphereBouquetCofibHomotopy where

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
open import Cubical.CW.Homology.Base
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

open import Cubical.Data.AbPath


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

open import Cubical.Foundations.Structure

open import Cubical.HITs.Bouquet as Bouq
open import Cubical.HITs.Bouquet.Discrete



open import Cubical.HITs.FreeGroup as FG
open import Cubical.HITs.FreeGroup.NormalForm
open import Cubical.HITs.FreeGroupoid.Properties
open import Cubical.Algebra.Group.Free
open import Cubical.Algebra.Group.IsomorphismTheorems

open import Cubical.Homotopy.Group.PiSphereBouquet
open import Cubical.Homotopy.Group.PiCofibBouquetMap
open import Cubical.Homotopy.BlakersMassey
open import Cubical.Algebra.Group.Instances.Pi

open import Cubical.Homotopy.Group.LES
open import Cubical.Algebra.Group.IsomorphismTheorems

open import Cubical.ZCohomology.Groups.Sn
open import Cubical.Homotopy.Group.PinSn

open import Cubical.HITs.Bouquet.Properties
open import Cubical.Foundations.Powerset

module _ {m k : ℕ} (f : Fin m → FreeGroup (Fin k)) where
  gens→finSphereBouquetFun : SphereBouquet 1 (Fin m) → SphereBouquet 1 (Fin k)
  gens→finSphereBouquetFun = Iso.fun Iso-Bouquet→∙-SphereBouquet₁→∙
                               (Iso.inv CharacFinBouquetFunIso f) .fst

  AbFreeGroup≅ℤ[] : (m : _)
    → GroupIso (AbelianizationGroup (freeGroupGroup (Fin m)))
                (AbGroup→Group ℤ[Fin m ])
  AbFreeGroup≅ℤ[] m = compGroupIso GroupIso-AbelienizeFreeGroup→FreeAbGroup
                                   (invGroupIso (ℤFin≅FreeAbGroup m))

  AbFreeGroup→ℤ[] : (m : _) →
    GroupHom (AbelianizationGroup (freeGroupGroup (Fin m)))
             (AbGroup→Group ℤ[Fin m ])
  AbFreeGroup→ℤ[] m = GroupIso→GroupHom (AbFreeGroup≅ℤ[] m)

  bouquetDegree-AbFreeGroup→ℤ[] : (x : _)
    → fst (bouquetDegree gens→finSphereBouquetFun) (AbFreeGroup→ℤ[] m .fst x)
     ≡ AbFreeGroup→ℤ[] k .fst (AbelianizationFun (FG.rec f) .fst x)
  bouquetDegree-AbFreeGroup→ℤ[] =
    Abi.elimProp _ (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
     (funExt⁻ (cong fst (help main)))
    where
    help = freeGroupHom≡
      {f = compGroupHom
             (compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _)
                           (AbFreeGroup→ℤ[] m))
            (bouquetDegree gens→finSphereBouquetFun)}
      {g = compGroupHom
             (compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _)
                           (AbelianizationFun (FG.rec f))) (AbFreeGroup→ℤ[] k)}

    main : (a : _) → bouquetDegree gens→finSphereBouquetFun .fst
                       (AbFreeGroup→ℤ[] m .fst (η (η a)))
                    ≡ AbFreeGroup→ℤ[] k .fst
                       (fst (AbelianizationFun (FG.rec f)) (η (η a)))
    main a = funExt λ s
      → sumFin-choose _ _ (λ _ → refl) +Comm _ _ a
          (characdiag s)
           λ x p → cong₂ _·ℤ_ (charac¬  x p) refl
      where
      charac¬ : (x' : Fin m) → ¬ x' ≡ a
        → fst (AbFreeGroup→ℤ[] m) (η (η a)) x' ≡ pos 0
      charac¬ x' p with (fst a ≟ᵗ fst x')
      ... | lt x = refl
      ... | eq x = ⊥.rec (p (Σ≡Prop (λ _ → isProp<ᵗ) (sym x)))
      ... | gt x = refl

      lem : ℤFinGenerator a a ≡ 1
      lem with (fst a ≟ᵗ fst a)
      ... | lt x = ⊥.rec (¬m<ᵗm x)
      ... | eq x = refl
      ... | gt x = ⊥.rec (¬m<ᵗm x)

      aux : (x : FreeGroup (Fin k)) (y : S¹)
        → fst (SphereBouquet∙ 1 (Fin k))
      aux b base = inl tt
      aux b (loop i) =
        Bouquet→SphereBouquet (Iso.inv Iso-ΩFinBouquet-FreeGroup b i)
      auxId : (x : _) → gens→finSphereBouquetFun (inr (a , x)) ≡ aux (f a) x
      auxId base = refl
      auxId (loop i) = refl

      characdiagMain : (w : _)
        → (λ s → degree (suc zero) (λ x → pickPetal s (aux w x)))
         ≡ fst (AbFreeGroup→ℤ[] k) (η w)
      characdiagMain =
        funExt⁻ (cong fst (freeGroupHom≡ {Group = AbGroup→Group ℤ[Fin k ]}
          {f = _ , makeIsGroupHom λ f g
            → funExt λ t → cong (degree 1)
              (funExt (λ { base → refl
                         ; (loop i) j → lem2 t f g j i}))
              ∙ (degreeHom {n = 0}
                ((λ x → pickPetal t (aux f x)) , refl)
                ((λ x → pickPetal t (aux g x)) , refl))}
          {g = _ , compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _)
                                (AbFreeGroup→ℤ[] k) .snd}
          λ s → funExt λ w → final s w ∙ ℤFinGeneratorComm w s))
        where
        final : (s w : Fin k) → degree 1 (λ x → pickPetal w (aux (η s) x))
                           ≡ ℤFinGenerator w s
        final s w with (fst w ≟ᵗ fst s)
        ... | lt x = refl
        ... | eq x = refl
        ... | gt x = refl

        lem2 : (t : _) (f g : FreeGroup (Fin k))
          → cong (pickPetal t ∘ aux (f FG.· g)) loop
          ≡ (cong (pickPetal t ∘ aux f) loop ∙ refl)
           ∙ cong (pickPetal t ∘ aux g) loop ∙ refl
        lem2 t f g =
           cong (cong (pickPetal t ∘ Bouquet→SphereBouquet))
              (invIso-ΩFinBouquet-FreeGroupPresStr f g)
          ∙ cong-∙ (pickPetal t ∘ Bouquet→SphereBouquet)
              (Iso.inv Iso-ΩFinBouquet-FreeGroup f)
              (Iso.inv Iso-ΩFinBouquet-FreeGroup g)
          ∙ cong₂ _∙_ (rUnit _) (rUnit _)

      characdiag : (s : _) →
           ℤFinGenerator a a
        ·ℤ degree 1 (λ x → pickPetal s (gens→finSphereBouquetFun (inr (a , x))))
        ≡ fst (AbFreeGroup→ℤ[] k)
              (fst (AbelianizationFun (FG.rec f)) (η (η a))) s
      characdiag s = cong₂ _·ℤ_ lem refl
                   ∙ cong (degree (suc zero))
                          (funExt λ x → cong (pickPetal s) (auxId x))
                   ∙ funExt⁻ (characdiagMain (f a))  s

module _ {m k : ℕ} (α' : Fin m → FreeGroup (Fin k)) where
  private
    α :  Bouquet∙ (Fin m) →∙ Bouquet∙ (Fin k)
    α = Iso.inv CharacFinBouquetFunIso α'

    αSphereBouquet : SphereBouquet∙ (suc zero) (Fin m)
                  →∙ SphereBouquet∙ (suc zero) (Fin k)
    αSphereBouquet = Iso.fun Iso-Bouquet→∙-SphereBouquet₁→∙ α

    _·f_ : ∀ {ℓ} {A : Type ℓ} → FreeGroup A → FreeGroup A → FreeGroup A
    _·f_ = FG._·_

  Bouquet→CofibFinBouquetFun : Bouquet (Fin k) → cofib (fst α)
  Bouquet→CofibFinBouquetFun = inr

  Free/ImBouquetFun : Group₀
  Free/ImBouquetFun =
    AbelianizationAbGroup (freeGroupGroup (Fin k))
    /Im AbelianizationFun (FG.rec α')

  FinBouquetCode : Bouquet (Fin k) → Type
  FinBouquetCode base = Free/ImBouquetFun .fst
  FinBouquetCode (loop x i) =
    ua (isoToEquiv (·GroupAutomorphismR (Free/ImBouquetFun) [ η (η x) ])) i

  substFinBouquetCode : (p : _) (x : _)
    → subst FinBouquetCode (Iso.inv Iso-ΩFinBouquet-FreeGroup p) [ η x ]
     ≡ [ η (x FG.· p)  ]
  substFinBouquetCode = FG.elimProp (λ _ → isPropΠ (λ _ → squash/ _ _))
    (λ a x i → [ η (transportRefl x i FG.· η (transportRefl a i)) ])
    (λ g1 g2 p q x
      → cong (λ P → subst FinBouquetCode P [ η x ])
             (invIso-ΩFinBouquet-FreeGroupPresStr g1 g2)
      ∙ substComposite FinBouquetCode
         (Iso.inv Iso-ΩFinBouquet-FreeGroup g1)
         (Iso.inv Iso-ΩFinBouquet-FreeGroup g2) [ η x ]
      ∙ cong (subst FinBouquetCode (Iso.inv Iso-ΩFinBouquet-FreeGroup g2))
             (p x)
      ∙ q (x FG.· g1)
      ∙ λ i → [ η (FG.assoc x g1 g2 (~ i)) ])
    (λ x i → [ η ((transportRefl x ∙ FG.idr x) i) ])
    λ g p x
      → cong (λ P → subst FinBouquetCode P [ η x ])
          (invIso-ΩFinBouquet-FreeGroupPresInv g)
       ∙ cong (subst FinBouquetCode (sym (Iso.inv Iso-ΩFinBouquet-FreeGroup g)))
           (λ i → [ η ((FG.idr x
                     ∙ cong₂ FG._·_ refl (sym (FG.invl g))
                     ∙ (FG.assoc x (inv g) g)) i) ])
       ∙ sym (cong (subst FinBouquetCode (sym (Iso.inv Iso-ΩFinBouquet-FreeGroup g)))
               (p (x FG.· inv g)))
       ∙ subst⁻Subst FinBouquetCode (Iso.inv Iso-ΩFinBouquet-FreeGroup g )
         [ η (x FG.· inv g) ]

  CofibFinBoquetFunCode : cofib (fst α) → Type
  CofibFinBoquetFunCode (inl x) = Free/ImBouquetFun .fst
  CofibFinBoquetFunCode (inr x) = FinBouquetCode x
  CofibFinBoquetFunCode (push base i) = Free/ImBouquetFun .fst
  CofibFinBoquetFunCode (push (loop x j) i) = lem i j
    where
    open AbelianizationGroupStructure (freeGroupGroup (Fin k))
    lem : refl ≡ cong (FinBouquetCode) (Iso.inv Iso-ΩFinBouquet-FreeGroup (α' x))
    lem = sym uaIdEquiv
        ∙ cong ua (Σ≡Prop (λ _ → isPropIsEquiv _)
          (funExt (SQ.elimProp (λ _ → squash/ _ _)
            (Abi.elimProp _ (λ _ → squash/ _ _)
              λ g → sym (substFinBouquetCode (α' x) g
                  ∙ eq/ _ _ ∣ (η (η x))
                           , (sym (ridAb (η (α' x)))
                           ∙ commAb (η (α' x)) 1Ab)
                           ∙ cong₂ _·Ab_ (sym (rinvAb (η g))) refl
                           ∙ sym (assocAb (η g) (η (inv g)) (η (α' x)))
                           ∙ cong₂ _·Ab_ refl (commAb (η (inv g)) (η (α' x)))
                           ∙ assocAb (η g) (η (α' x)) (η (inv g)) ∣₁)))))
        ∙ retEq univalence _

  isSetCofibFinBoquetFunCode : (x : _) → isSet (CofibFinBoquetFunCode x)
  isSetCofibFinBoquetFunCode =
    PO.elimProp _ (λ _ → isPropIsSet)
      (λ _ → GroupStr.is-set (Free/ImBouquetFun .snd))
      (elimPropBouquet
        (λ _ → isPropIsSet)
        (GroupStr.is-set (Free/ImBouquetFun .snd)))

  FG→π₁cofibFinBouquetFun :
    GroupHom (freeGroupGroup (Fin k))
             (πGr 0 (cofib (fst α) , inr base))
  fst FG→π₁cofibFinBouquetFun b =
    ∣ (λ i → inr (Iso.inv Iso-ΩFinBouquet-FreeGroup b i)) ∣₂
  snd FG→π₁cofibFinBouquetFun = makeIsGroupHom λ a b
    → cong ∣_∣₂ ((λ i j → inr (invIso-ΩFinBouquet-FreeGroupPresStr a b i j))
     ∙ cong-∙ inr (Iso.inv Iso-ΩFinBouquet-FreeGroup a)
                  (Iso.inv Iso-ΩFinBouquet-FreeGroup b))

  private
    loopCofibFinBouquetFun : (x : Fin m)
      → Path (Path (cofib (fst α)) (inr base) (inr base))
             (λ i → inr (Iso.inv Iso-ΩFinBouquet-FreeGroup (α' x) i))
             refl
    loopCofibFinBouquetFun x i j =
      hcomp (λ k → λ {(i = i0) → push (loop x j) k
                     ; (i = i1) → push base k
                     ; (j = i0) → push base k
                     ; (j = i1) → push base k})
            (inl tt)

  AbFG→π₁ᵃᵇCofibFinBouquetFun : Abelianization (freeGroupGroup (Fin k))
                → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr base) ∥₂
  AbFG→π₁ᵃᵇCofibFinBouquetFun = fst Abelianizeπ₁→π₁ᵃᵇ
    ∘ AbelianizationFun FG→π₁cofibFinBouquetFun .fst

  Hom-AbFG-π₁ᵃᵇCofibFinBouquetFun :
    AbGroupHom (AbelianizationAbGroup (freeGroupGroup (Fin k)))
               (π₁ᵃᵇAbGroup (cofib (fst α) , inr base))
  Hom-AbFG-π₁ᵃᵇCofibFinBouquetFun =
    compGroupHom (AbelianizationFun FG→π₁cofibFinBouquetFun) Abelianizeπ₁→π₁ᵃᵇ

  AbFG→π₁ᵃᵇCofibFinBouquetFun≡' : (x : Abelianization (freeGroupGroup (Fin m)))
    → (a : FreeGroup (Fin k))
    → ·πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetFun ((AbelianizationFun (FG.rec α')) .fst x))
           (AbFG→π₁ᵃᵇCofibFinBouquetFun (η a))
     ≡ AbFG→π₁ᵃᵇCofibFinBouquetFun (η a)
  AbFG→π₁ᵃᵇCofibFinBouquetFun≡' = Abi.elimProp _ (λ _ → isPropΠ λ _ → squash₂ _ _)
    (FG.elimProp (λ _ → isPropΠ λ _ → squash₂ _ _)
    (λ c a → (λ i → ·πᵃᵇ ∣ paths (loopCofibFinBouquetFun c i) ∣₂
                          (AbFG→π₁ᵃᵇCofibFinBouquetFun (η a)))
                 ∙ cong ∣_∣₂ (cong paths (sym (lUnit _))))
    (λ g1 g2 p q a
      → cong₂ ·πᵃᵇ (cong AbFG→π₁ᵃᵇCofibFinBouquetFun
                    (IsGroupHom.pres·
                      (snd (AbelianizationFun (FG.rec α'))) (η g1) (η g2))
       ∙ IsGroupHom.pres·
          (snd (compGroupHom (AbelianizationFun FG→π₁cofibFinBouquetFun)
            (Abelianizeπ₁→π₁ᵃᵇ)))
          (fst (AbelianizationFun (FG.rec α')) (η g1))
          (fst (AbelianizationFun (FG.rec α')) (η g2)))
          (λ _ → (AbFG→π₁ᵃᵇCofibFinBouquetFun (η a)))
        ∙ sym (·πᵃᵇassoc (AbFG→π₁ᵃᵇCofibFinBouquetFun
                          (AbelianizationFun (FG.rec α') .fst (η g1)))
                        (AbFG→π₁ᵃᵇCofibFinBouquetFun
                          (AbelianizationFun (FG.rec α') .fst (η g2)))
                          (AbFG→π₁ᵃᵇCofibFinBouquetFun (η a)))
        ∙ cong (·πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetFun
                      (AbelianizationFun (FG.rec α') .fst (η g1)))) (q a)
        ∙ p a)
      (λ a → ·πᵃᵇlUnit (AbFG→π₁ᵃᵇCofibFinBouquetFun (η a)))
      λ g p a → cong₂ ·πᵃᵇ
         (sym (sym (IsGroupHom.presinv (snd (compGroupHom
                    (AbelianizationFun FG→π₁cofibFinBouquetFun)
                    (Abelianizeπ₁→π₁ᵃᵇ)))
                    (AbelianizationFun (FG.rec α') .fst (η g)))
           ∙ cong AbFG→π₁ᵃᵇCofibFinBouquetFun
                   (IsGroupHom.presinv
                     (snd (AbelianizationFun (FG.rec α'))) (η g))))
         (sym (sym (IsGroupHom.presinv (snd (compGroupHom
                    (AbelianizationFun FG→π₁cofibFinBouquetFun)
                 (Abelianizeπ₁→π₁ᵃᵇ))) (η (inv a)))
       ∙ cong (AbFG→π₁ᵃᵇCofibFinBouquetFun ∘ η)
              (GroupTheory.invInv (freeGroupGroup (Fin k)) a)))
       ∙ sym (-πᵃᵇinvDistr (AbFG→π₁ᵃᵇCofibFinBouquetFun
                           ((AbelianizationFun (FG.rec α')) .fst (η g)))
                          (AbFG→π₁ᵃᵇCofibFinBouquetFun (η (inv a))))
       ∙ cong -πᵃᵇ (p (inv a))
       ∙ sym (IsGroupHom.presinv (snd (compGroupHom
               (AbelianizationFun FG→π₁cofibFinBouquetFun)
                 (Abelianizeπ₁→π₁ᵃᵇ))) (η (inv a)))
       ∙ cong (AbFG→π₁ᵃᵇCofibFinBouquetFun ∘ η)
              (GroupTheory.invInv (freeGroupGroup (Fin k)) a))

  AbFG→π₁ᵃᵇCofibFinBouquetFun≡ : (x : Abelianization (freeGroupGroup (Fin m)))
    (a b : FreeGroup (Fin k))
      (q : ·πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetFun (AbelianizationFun (FG.rec α') .fst x))
               (AbFG→π₁ᵃᵇCofibFinBouquetFun (η b))
              ≡ AbFG→π₁ᵃᵇCofibFinBouquetFun (η a))
     → Path (∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr base) ∥₂)
             (AbFG→π₁ᵃᵇCofibFinBouquetFun (η a))
             (AbFG→π₁ᵃᵇCofibFinBouquetFun (η b))
  AbFG→π₁ᵃᵇCofibFinBouquetFun≡ x a b q =
    sym q ∙ AbFG→π₁ᵃᵇCofibFinBouquetFun≡' x b

  decodeCofibαinl : Abelianization (freeGroupGroup (Fin k))
    → ∥ inr base ≡ᵃᵇ inl tt ∥₂
  decodeCofibαinl =
    Abi.rec _ squash₂
      (λ s → ·πᵃᵇ (∣ paths (λ i → inr (Iso.inv Iso-ΩFinBouquet-FreeGroup s i)) ∣₂)
                   ∣ paths (sym (push base)) ∣₂)
   λ a b c → cong₂ ·πᵃᵇ (cong ∣_∣₂ (lem a b c)
                    ∙ cong (·πᵃᵇ (∣ paths (t a) ∣₂))
                           (·πᵃᵇcomm ∣ paths (t b) ∣₂ ∣ paths (t c) ∣₂)
                    ∙ sym (cong ∣_∣₂ (lem a c b)))
                        (λ _ → ∣ paths (sym (push base)) ∣₂)
    where
    t : (x : _) → Path (cofib (fst α)) _ _
    t x i = inr (Iso.inv Iso-ΩFinBouquet-FreeGroup x i)

    lem : (x y z : _)
      → Path (Pathᵃᵇ (cofib (fst α)) _ _)
              (paths (t (x ·f (y ·f z))))
              (paths (t x ∙ t y ∙ t z))
    lem x y z =
      cong paths (((λ j i → inr (invIso-ΩFinBouquet-FreeGroupPresStr x (y ·f z) j i))
         ∙ cong-∙ inr (Iso.inv Iso-ΩFinBouquet-FreeGroup x)
                      (Iso.inv Iso-ΩFinBouquet-FreeGroup (y ·f z)))
        ∙ cong₂ _∙_ refl
           ((λ j i → inr (invIso-ΩFinBouquet-FreeGroupPresStr y z j i))
          ∙ cong-∙ inr (Iso.inv Iso-ΩFinBouquet-FreeGroup y)
                       (Iso.inv Iso-ΩFinBouquet-FreeGroup z)))

  Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun :
    GroupHom Free/ImBouquetFun
             (AbGroup→Group (π₁ᵃᵇAbGroup (cofib (fst α) , inr base)))
  fst Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun =
    SQ.rec squash₂ AbFG→π₁ᵃᵇCofibFinBouquetFun main
    where
    main : (a b :  fst (AbelianizationAbGroup (freeGroupGroup (Fin k))))
           (q : ∃[ x ∈ fst (AbelianizationAbGroup (freeGroupGroup (Fin m))) ]
                _ ≡ _)
           → AbFG→π₁ᵃᵇCofibFinBouquetFun a ≡ AbFG→π₁ᵃᵇCofibFinBouquetFun b
    main = Abi.elimProp2 _ (λ _ _ → isPropΠ (λ _ → squash₂ _ _))
      λ a b → PT.elim (λ _ → squash₂ _ _)
        λ {(x , q)
          → AbFG→π₁ᵃᵇCofibFinBouquetFun≡ x a b
             (cong (λ s → ·πᵃᵇ s (AbFG→π₁ᵃᵇCofibFinBouquetFun (η b)))
                (cong AbFG→π₁ᵃᵇCofibFinBouquetFun q
                ∙ IsGroupHom.pres· (snd Hom-AbFG-π₁ᵃᵇCofibFinBouquetFun)
                                   (η a) (η (inv b)))
                ∙ (sym (·πᵃᵇassoc (AbFG→π₁ᵃᵇCofibFinBouquetFun (η a))
                                  (AbFG→π₁ᵃᵇCofibFinBouquetFun (η (inv b)))
                                  (AbFG→π₁ᵃᵇCofibFinBouquetFun (η b))))
                ∙ cong (·πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetFun (η a)))
                   (cong₂ ·πᵃᵇ (IsGroupHom.presinv
                                (snd Hom-AbFG-π₁ᵃᵇCofibFinBouquetFun) (η b)) refl
                   ∙ ·πᵃᵇlCancel ((AbFG→π₁ᵃᵇCofibFinBouquetFun (η b))))
                ∙ ·πᵃᵇrUnit (AbFG→π₁ᵃᵇCofibFinBouquetFun (η a)))}
  snd Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun =
     makeIsGroupHom (SQ.elimProp2
      (λ _ _ → squash₂ _ _)
      (IsGroupHom.pres· (snd Hom-AbFG-π₁ᵃᵇCofibFinBouquetFun)))

  decodeFinBouquetCode : (x : _) → FinBouquetCode x
    → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr x) ∥₂
  decodeFinBouquetCode base = fst Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun
  decodeFinBouquetCode (loop x i) = help i
    where
    lem : (p : _)
     → transport (λ i → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr (loop x i)) ∥₂)
                  (·πᵃᵇ p (-πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetFun (η (η x))))) ≡ p
    lem = ST.elim (λ _ → isSetPathImplicit)
      (elimProp≡ᵃᵇ (λ _ → squash₂ _ _) λ p
        → (λ j → transp (λ i → ∥ Pathᵃᵇ (cofib (fst α))
                                    (inr base) (inr (loop x (i ∨ j))) ∥₂) j
                        ∣ paths (p ∙ (λ i → inr (loop x (~ i ∨ j)))) ∣₂)
       ∙ cong ∣_∣₂ (cong paths (sym (rUnit p))))

    help : PathP (λ i → ua (isoToEquiv (·GroupAutomorphismR Free/ImBouquetFun
                                                             [ η (η x) ])) i
                      → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr (loop x i)) ∥₂)
            (fst Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun)
            (fst Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun)
    help = toPathP (funExt (SQ.elimProp (λ _ → squash₂ _ _)
      λ s → cong (transport (λ i → ∥ Pathᵃᵇ (cofib (fst α))
                                             (inr base) (inr (loop x i)) ∥₂))
         ((cong (fst Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun)
           (cong (Iso.inv (·GroupAutomorphismR Free/ImBouquetFun
                                                [ η (η x) ]))
             (transportRefl [ s ]))
          ∙ IsGroupHom.pres· (snd Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun)
            [ s ] [ η (inv (η x)) ]
          ∙ cong (·πᵃᵇ (AbFG→π₁ᵃᵇCofibFinBouquetFun s))
               (IsGroupHom.presinv
               (snd Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun) [ η (η x) ])))
       ∙ lem (AbFG→π₁ᵃᵇCofibFinBouquetFun s)))


  decodeCofibFinBoquetFun : (x : _) → CofibFinBoquetFunCode x
    → ∥ inr base ≡ᵃᵇ x ∥₂
  decodeCofibFinBoquetFun (inl x) p =
    ·πᵃᵇ (decodeFinBouquetCode base p) ∣ paths (sym (push base)) ∣₂
  decodeCofibFinBoquetFun (inr x) = decodeFinBouquetCode x
  decodeCofibFinBoquetFun (push a i) = help a i
    where
    help : (a : Bouquet (Fin m))
      → PathP (λ i → CofibFinBoquetFunCode (push a i)
                   → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (push a i) ∥₂)
               (λ p → ·πᵃᵇ (decodeFinBouquetCode base p)
                           ∣ paths (sym (push base)) ∣₂)
               (decodeFinBouquetCode (Iso.inv CharacFinBouquetFunIso α' .fst a))
    help =
      elimPropBouquet (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → squash₂)) _ _)
        (funExt (SQ.elimProp (λ _ → isOfHLevelPathP' 1 squash₂ _ _)
          (Abi.elimProp _ (λ _ → isOfHLevelPathP' 1 squash₂ _ _)
            λ g → λ i → ∣ paths (compPath-filler
              (λ i₂ → inr (Iso.inv Iso-ΩFinBouquet-FreeGroup g i₂))
              (sym (push base)) (~ i)) ∣₂)))

  FinBouquetCode+ : (x : _) → Free/ImBouquetFun .fst
    → FinBouquetCode x → FinBouquetCode x
  FinBouquetCode+ base p q = GroupStr._·_ (snd Free/ImBouquetFun) p q
  FinBouquetCode+ (loop x i) p = help i
    where
    typecheck : ∀ {ℓ} (A B : Type ℓ) (p : A ≡ B)
      (f : A → A) (g : B → B)
      → ((x : _) → transport p (f (transport (sym p) x)) ≡ g x)
      → PathP (λ i → p i → p i) f g
    typecheck = λ A → J> λ f g p
      → funExt λ x → sym (transportRefl _ ∙ cong f (transportRefl x)) ∙ p x

    typecheck' : ∀ {ℓ} {A B : Type ℓ} (p : A ≃ B)
      {f : A → A} {g : B → B} → ((x : _) → fst p (f (invEq p x)) ≡ g x)
        → PathP (λ i → ua p i → ua p i) f g
    typecheck' p {f = f} {g} h =
      typecheck _ _ (ua p) f g λ b
        → transportRefl _
         ∙ cong (fst p) (cong f (cong (invEq p) (transportRefl b))) ∙ h b

    help : PathP (λ i → ua (isoToEquiv (·GroupAutomorphismR Free/ImBouquetFun
                                         [ η (η x) ])) i
                      → ua (isoToEquiv (·GroupAutomorphismR Free/ImBouquetFun
                                         [ η (η x) ])) i)
                 (GroupStr._·_ (snd Free/ImBouquetFun) p)
                 (GroupStr._·_ (snd Free/ImBouquetFun) p)
    help =
     typecheck' (isoToEquiv (·GroupAutomorphismR Free/ImBouquetFun [ η (η x) ]))
      (SQ.elimProp (λ _ → squash/ _ _)
        (Abi.elimProp _ (λ _ → squash/ _ _) λ g
          → sym (GroupStr.·Assoc (snd Free/ImBouquetFun) p
                  (invEq (isoToEquiv (·GroupAutomorphismR Free/ImBouquetFun
                                       [ η (η x) ])) [ η g ])
                  [ η (η x) ])
              ∙ cong (snd Free/ImBouquetFun GroupStr.· p)
                 (sym (GroupStr.·Assoc (snd Free/ImBouquetFun)
                      [ η g ] [ η (inv (η x)) ]  [ η (η x) ])
                ∙ cong (snd Free/ImBouquetFun GroupStr.· [ η g ])
                  (GroupStr.·InvL (snd Free/ImBouquetFun) [ η (η x) ])
                ∙ GroupStr.·IdR (snd Free/ImBouquetFun) [ η g ])))

  CofibFinBoquetFunCode+ : (x : _) → Free/ImBouquetFun .fst
    → CofibFinBoquetFunCode x → CofibFinBoquetFunCode x
  CofibFinBoquetFunCode+ (inl x) p q = GroupStr._·_ (snd Free/ImBouquetFun) p q
  CofibFinBoquetFunCode+ (inr x) = FinBouquetCode+ x
  CofibFinBoquetFunCode+ (push x i) p = help x i
   where
   help : (x : Bouquet (Fin m))
     → PathP (λ i → CofibFinBoquetFunCode (push x i)
                   → CofibFinBoquetFunCode (push x i))
             (snd Free/ImBouquetFun GroupStr.· p)
             (FinBouquetCode+ (α .fst x) p)
   help = elimPropBouquet (λ _ → isOfHLevelPathP' 1
                           (isSetΠ (λ _ → isSetCofibFinBoquetFunCode _)) _ _)
                          refl

  cono'Inr : (x : _) (p : Path (cofib (fst α)) (inr base) (inr x)) → hProp ℓ-zero
  fst (cono'Inr base p) =
    ∃[ r ∈ Path (Bouquet (Fin k)) base base ] p ≡ λ i → inr (r i)
  snd (cono'Inr base p) = squash₁
  fst (cono'Inr (loop x i) p) =
    ∃[ r ∈ Path (Bouquet (Fin k)) base (loop x i) ] p ≡ λ i → inr (r i)
  snd (cono'Inr (loop x i) p) = squash₁

  cono : (x : cofib (fst α)) (p : inr base ≡ x) → Type
  cono (inl x) p = ∃[ r ∈ Path (Bouquet (Fin k)) base base ]
                    (p ≡ (λ i → inr (r i)) ∙ sym (push base))
  cono (inr x) p = fst (cono'Inr x p)
  cono (push a i) p = help a i p .fst
    where
    help : (a : Bouquet (Fin m))
      → PathP (λ i → Path (cofib (fst α))  (inr base) (push a i) → hProp ℓ-zero)
               (λ a → (∃[ r ∈ Path (Bouquet (Fin k)) base base ]
                 a ≡ (λ i → inr (r i)) ∙ sym (push base)) , squash₁)
               (cono'Inr (fst α a))
    help =
      elimPropBouquet (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → isSetHProp)) _ _)
        λ i p → (∃[ r ∈ Path (Bouquet (Fin k)) base base ]
                  p ≡ compPath-filler (λ i → inr (r i)) (sym (push base)) (~ i))
                , squash₁

  encodeCofibFinBoquetFun' : (x : _)
    → Pathᵃᵇ (cofib (fst α)) (inr base) x → CofibFinBoquetFunCode x
  encodeCofibFinBoquetFun' x (paths q) = subst CofibFinBoquetFunCode q [ η ε ]
  encodeCofibFinBoquetFun' x (com p q r i) = ha _ q p r i
    where
    aux : (x : cofib (fst α)) (p : inr base ≡ x)  → cono x p
    aux = J> ∣ refl , refl ∣₁

    ha : (x : _) (q p r : inr base ≡ x)
      → subst CofibFinBoquetFunCode (p ∙ sym q ∙ r) [ η ε ]
       ≡ subst CofibFinBoquetFunCode (r ∙ sym q ∙ p) [ η ε ]
    ha = J> λ p q
      → cong (λ p → subst CofibFinBoquetFunCode p [ η ε ])
              (cong (p ∙_) (sym (lUnit q)))
      ∙ substComposite CofibFinBoquetFunCode p q [ η ε ]
      ∙ PT.rec2 (squash/ _ _)
          (λ {(x' , xe) (y' , ye)
            → lem (Iso.fun Iso-ΩFinBouquet-FreeGroup x')
                  (Iso.fun Iso-ΩFinBouquet-FreeGroup y')
                  p
                  (cong (cong Bouquet→CofibFinBouquetFun)
                    (Iso.leftInv Iso-ΩFinBouquet-FreeGroup x') ∙ sym xe)
                  q
                  (cong (cong Bouquet→CofibFinBouquetFun)
                    (Iso.leftInv Iso-ΩFinBouquet-FreeGroup y') ∙ sym ye)})
          (aux _ p)
          (aux _ q)
      ∙ sym (substComposite CofibFinBoquetFunCode q p [ η ε ])
      ∙ cong (λ p → subst CofibFinBoquetFunCode p [ η ε ])
             (cong (q ∙_) (lUnit p))
      where
      lem : (x y : FreeGroup (Fin k))
            (p : Path (cofib (fst α)) (inr base) (inr base))
            (s : (λ i → inr (Iso.inv Iso-ΩFinBouquet-FreeGroup x i)) ≡ p)
            (q : Path (cofib (fst α)) (inr base) (inr base))
            (s' : (λ i → inr (Iso.inv Iso-ΩFinBouquet-FreeGroup y i)) ≡ q)
         → subst CofibFinBoquetFunCode q (subst CofibFinBoquetFunCode p [ η ε ])
          ≡ subst CofibFinBoquetFunCode p (subst CofibFinBoquetFunCode q [ η ε ])
      lem x y =
        J> (J> cong (subst CofibFinBoquetFunCode y')
              (substFinBouquetCode x ε
             ∙ GroupStr.·IdL (snd Free/ImBouquetFun) [ η x ])
         ∙ substFinBouquetCode y x
         ∙ cong [_] (AbelianizationGroupStructure.commAb
                     (freeGroupGroup (Fin k)) (η x) (η y))
         ∙ sym (substFinBouquetCode x y)
         ∙ cong (subst CofibFinBoquetFunCode x')
             (sym (substFinBouquetCode y ε
                ∙ GroupStr.·IdL (snd Free/ImBouquetFun) [ η y ])) )
        where
        x' y' : Path (cofib (fst α)) (inr base) (inr base)
        x' =  (λ i → inr (Iso.inv Iso-ΩFinBouquet-FreeGroup x i))
        y' =  (λ i → inr (Iso.inv Iso-ΩFinBouquet-FreeGroup y i))

  encodeCofibFinBoquetFun : (x : _)
    → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) x ∥₂ → CofibFinBoquetFunCode x
  encodeCofibFinBoquetFun x =
    ST.rec (isSetCofibFinBoquetFunCode _) (encodeCofibFinBoquetFun' x)

  decodeEncodeCofibα : (x : _) (p : ∥ Pathᵃᵇ (cofib (fst α)) (inr base) x ∥₂)
    → decodeCofibFinBoquetFun x (encodeCofibFinBoquetFun x p) ≡ p
  decodeEncodeCofibα x =
    ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
      (J (λ x p → decodeCofibFinBoquetFun x
                    (encodeCofibFinBoquetFun x ∣ paths p ∣₂) ≡ ∣ paths p ∣₂)
         refl))

  encodeDecodeCofibα : (p : _)
    → encodeCofibFinBoquetFun (inr base) (decodeCofibFinBoquetFun (inr base) p)
     ≡ p
  encodeDecodeCofibα = SQ.elimProp (λ _ → squash/ _ _)
    (Abi.elimProp _ (λ _ → squash/ _ _)
      λ w → substFinBouquetCode w ε ∙ λ i → [ η (FG.idl w (~ i)) ])

  Free/≅π₁ᵃᵇCofibBouquetMap :
    GroupIso Free/ImBouquetFun
             (AbGroup→Group (π₁ᵃᵇAbGroup (cofib (fst α) , inr base)))
  Iso.fun (fst Free/≅π₁ᵃᵇCofibBouquetMap) =
    Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun .fst
  Iso.inv (fst Free/≅π₁ᵃᵇCofibBouquetMap) = encodeCofibFinBoquetFun (inr base)
  Iso.rightInv (fst Free/≅π₁ᵃᵇCofibBouquetMap) = decodeEncodeCofibα (inr base)
  Iso.leftInv (fst Free/≅π₁ᵃᵇCofibBouquetMap) = encodeDecodeCofibα
  snd Free/≅π₁ᵃᵇCofibBouquetMap =
    Hom-Free/ImBouquetFun-π₁ᵃᵇCofibFinBouquetFun .snd

  Free/≅π₁ᵃᵇCofibBouquetMap' :
    GroupIso Free/ImBouquetFun
             (AbGroup→Group
               (AbelianizationAbGroup (πGr 0 (cofib (fst α) , inr base))))
  Free/≅π₁ᵃᵇCofibBouquetMap' =
    compGroupIso Free/≅π₁ᵃᵇCofibBouquetMap
      (invGroupIso (Abelianizeπ₁≅π₁ᵃᵇ (_ , inr base)))

  cofibIso' : Iso (cofib (fst α)) (cofib (fst αSphereBouquet))
  cofibIso' = pushoutIso _ _ _ _
    (invEquiv (Bouquet≃∙SphereBouquet .fst)) (idEquiv _)
    (invEquiv (Bouquet≃∙SphereBouquet .fst))
    (λ i x → tt)
    (funExt λ x → cong (invEq (isoToEquiv Iso-SphereBouquet-Bouquet))
      (cong (fst α) (sym (Iso.rightInv Iso-SphereBouquet-Bouquet x))))

  helpIso : GroupIso Free/ImBouquetFun
             (AbGroup→Group
               (AbelianizationAbGroup
                 (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt))))
  helpIso =
    compGroupIso Free/≅π₁ᵃᵇCofibBouquetMap'
      (GroupEquiv→GroupIso (AbelianizationEquiv
        (compGroupEquiv
          (GroupIso→GroupEquiv
            (invGroupIso (π'Gr≅πGr 0 (cofib (fst α) , inr base))))
          (GroupIso→GroupEquiv
            (π'GrIso 0 (isoToEquiv (cofibIso') , sym (push (inl tt))))))))

  Free/ImBouquetFun≅ℤ[]/ImBouquetDegree :
    GroupIso Free/ImBouquetFun
             (ℤ[Fin k ] /Im bouquetDegree (fst αSphereBouquet))
  Free/ImBouquetFun≅ℤ[]/ImBouquetDegree =
    Hom/ImIso _ _ (AbFreeGroup≅ℤ[] α' m) (AbFreeGroup≅ℤ[] α' k)
                  (bouquetDegree-AbFreeGroup→ℤ[] α')

  helpIso-Lock : lockUnit {ℓ-zero}
    → GroupIso (AbGroup→Group
                (AbelianizationAbGroup
                  (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt))))
               Free/ImBouquetFun
  helpIso-Lock unlock = invGroupIso helpIso

  Free/ImBouquetFun≅ℤ[]/ImBouquetDegree-Lock : lockUnit {ℓ-zero}
    → GroupIso Free/ImBouquetFun
               (ℤ[Fin k ] /Im (bouquetDegree (fst αSphereBouquet)))
  Free/ImBouquetFun≅ℤ[]/ImBouquetDegree-Lock unlock =
    Free/ImBouquetFun≅ℤ[]/ImBouquetDegree

  π'BoquetFunCofib≅Free/ImBouquetFun>1-Lock : lockUnit {ℓ-zero}
    → GroupIso ((AbelianizationGroup (π'Gr 0 (cofib∙ (fst αSphereBouquet)))))
               (ℤ[Fin k ] /Im (bouquetDegree (fst αSphereBouquet)))
  π'BoquetFunCofib≅Free/ImBouquetFun>1-Lock t =
    compGroupIso (helpIso-Lock t) (Free/ImBouquetFun≅ℤ[]/ImBouquetDegree-Lock t)

  π'BoquetFunCofib≅Free/ImBouquetFun>1-LockComp : (lock : lockUnit {ℓ-zero})
    → (x : _) → Iso.fun (π'BoquetFunCofib≅Free/ImBouquetFun>1-Lock lock .fst) x
               ≡ Iso.fun (fst (Free/ImBouquetFun≅ℤ[]/ImBouquetDegree-Lock lock))
                  (Iso.fun (helpIso-Lock lock .fst) x)
  π'BoquetFunCofib≅Free/ImBouquetFun>1-LockComp = λ lock x → refl


  π'BoquetFunCofib≅Free/ImBouquetFun>1 :
    GroupIso (AbelianizationGroup
              (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt)))
             (ℤ[Fin k ] /Im (bouquetDegree (fst αSphereBouquet)))
  π'BoquetFunCofib≅Free/ImBouquetFun>1 =
    π'BoquetFunCofib≅Free/ImBouquetFun>1-Lock unlock
