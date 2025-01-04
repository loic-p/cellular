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
open import Cubical.CW.Homology
open import Cubical.CW.Subcomplex


open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
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
open import Cubical.Data.Int
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


elimPropBouquet : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Bouquet A → Type ℓ'}
  (pr : (x : _) → isProp (B x))
  (b : B base)
  → (x  : Bouquet A) → B x
elimPropBouquet pr b base = b
elimPropBouquet {B = B} pr b (loop x i) =
  isProp→PathP {B = λ i → B (loop x i)} (λ _ → pr _) b b i

Iso-ΩS¹Bouquet-FreeGroup : {n : ℕ} → Iso (fst (Ω (Bouquet∙ (Fin n)))) (FreeGroup (Fin n))
Iso-ΩS¹Bouquet-FreeGroup =
  compIso
    (compIso (invIso (setTruncIdempotentIso (isOfHLevelPath' 2
      (isGroupoidBouquet DiscreteFin) _ _)))
             (equivToIso (TruncatedFamiliesEquiv base)))
    (equivToIso (invEquiv freeGroupTruncIdempotent≃))

open import Cubical.HITs.FreeGroupoid.Base as FGrp

InvIso-ΩS¹Bouquet-FreeGroupPresStr : {n : ℕ} (x y : FreeGroup (Fin n))
  → Iso.inv Iso-ΩS¹Bouquet-FreeGroup (FG._·_ x y)
   ≡ Iso.inv Iso-ΩS¹Bouquet-FreeGroup x ∙ Iso.inv Iso-ΩS¹Bouquet-FreeGroup y
InvIso-ΩS¹Bouquet-FreeGroupPresStr x y =
  cong (F ∘ G) (l1 x y) ∙ l2 (H x) (H y)
  where
  F = Iso.fun (setTruncIdempotentIso (isOfHLevelPath' 2 (isGroupoidBouquet DiscreteFin) _ _))
  G = invEq (TruncatedFamiliesEquiv base)
  H = fst freeGroupTruncIdempotent≃

  l2 : (x y : _) → F (G (ST.rec2 squash₂ (λ x y → ∣ x FGrp.· y ∣₂) x y))
                 ≡ F (G x) ∙ F (G y)
  l2 = ST.elim2 (λ _ _ → isOfHLevelPath 2
                 (isOfHLevelPath' 2 (isGroupoidBouquet DiscreteFin) _ _) _ _)
                 λ _ _ → refl

  l1 : (x t : _) → H (x FG.· t) ≡ ST.rec2 squash₂ (λ x y → ∣ x FGrp.· y ∣₂) (H x) (H t) 
  l1 x t = cong H (cong₂ FG._·_ (sym (retEq freeGroupTruncIdempotent≃ _))
                                (sym (retEq freeGroupTruncIdempotent≃ _)))
         ∙ cong H (sym (h (H x) (H t)))
         ∙ secEq freeGroupTruncIdempotent≃ _
    where
    h : (x y : _) → invEq freeGroupTruncIdempotent≃ (ST.rec2 squash₂ (λ x y → ∣ x FGrp.· y ∣₂) x y)
                  ≡ (invEq freeGroupTruncIdempotent≃ x FG.· invEq freeGroupTruncIdempotent≃ y)
    h = ST.elim2 (λ _ _ → isOfHLevelPath 2 trunc _ _) λ _ _ → refl

InvIso-ΩS¹Bouquet-FreeGroupPresInv : {n : ℕ} (x : FreeGroup (Fin n))
  → Iso.inv Iso-ΩS¹Bouquet-FreeGroup (FG.inv x)
   ≡ sym (Iso.inv Iso-ΩS¹Bouquet-FreeGroup x)
InvIso-ΩS¹Bouquet-FreeGroupPresInv {n = n} =
  morphLemmas.distrMinus FG._·_ _∙_ (Iso.inv (Iso-ΩS¹Bouquet-FreeGroup {n = n}))
    InvIso-ΩS¹Bouquet-FreeGroupPresStr ε refl inv sym
      (sym ∘ lUnit) (sym ∘ rUnit) FG.invl rCancel GLaws.assoc refl

module _ {ℓ} {A : Type ℓ} where
  SphereBouquet→Bouquet : SphereBouquet 1 A → Bouquet A
  SphereBouquet→Bouquet (inl x) = base
  SphereBouquet→Bouquet (inr (s , base)) = base
  SphereBouquet→Bouquet (inr (s , loop i)) = loop s i
  SphereBouquet→Bouquet (push a i) = base

  Bouquet→SphereBouquet : Bouquet A → SphereBouquet 1 A
  Bouquet→SphereBouquet base = inl tt
  Bouquet→SphereBouquet (loop x i) =
    (push x ∙∙ (λ i → inr (x , loop i)) ∙∙ sym (push x)) i

  Iso-SphereBouquet-Bouquet : Iso (SphereBouquet 1 A) (Bouquet A)
  Iso.fun Iso-SphereBouquet-Bouquet = SphereBouquet→Bouquet
  Iso.inv Iso-SphereBouquet-Bouquet = Bouquet→SphereBouquet
  Iso.rightInv Iso-SphereBouquet-Bouquet base = refl
  Iso.rightInv Iso-SphereBouquet-Bouquet (loop x i) j =
    SphereBouquet→Bouquet
      (doubleCompPath-filler (push x) (λ i → inr (x , loop i)) (sym (push x)) (~ j) i)
  Iso.leftInv Iso-SphereBouquet-Bouquet (inl x) = refl
  Iso.leftInv Iso-SphereBouquet-Bouquet (inr (s , base)) = push s
  Iso.leftInv Iso-SphereBouquet-Bouquet (inr (s , loop i)) j =
    doubleCompPath-filler (push s) (λ i → inr (s , loop i)) (sym (push s)) (~ j) i
  Iso.leftInv Iso-SphereBouquet-Bouquet (push a i) j = push a (i ∧ j)

  Bouquet≃∙SphereBouquet : SphereBouquet∙ 1 A ≃∙ Bouquet A , base
  fst Bouquet≃∙SphereBouquet = isoToEquiv (Iso-SphereBouquet-Bouquet)
  snd Bouquet≃∙SphereBouquet = refl

makeSphereBouquetFun : {m k : ℕ}
  → (Fin m → FreeGroup (Fin k))
    →  SphereBouquet∙ (suc zero) (Fin m)
    →∙ SphereBouquet∙ (suc zero) (Fin k)
fst (makeSphereBouquetFun F) (inl x) = inl tt
fst (makeSphereBouquetFun F) (inr (s , base)) = inl tt
fst (makeSphereBouquetFun F) (inr (s , loop i)) =
  cong Bouquet→SphereBouquet (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (F s)) i
fst (makeSphereBouquetFun F) (push a i) = inl tt
snd (makeSphereBouquetFun F) = refl

makeSphereBouquetFun' : {m k : ℕ}
  → (Fin m → FreeGroup (Fin k))
    →  Bouquet∙ (Fin m)
    →∙ Bouquet∙ (Fin k)
fst (makeSphereBouquetFun' f) base = base
fst (makeSphereBouquetFun' f) (loop x i) = Iso.inv Iso-ΩS¹Bouquet-FreeGroup (f x) i
snd (makeSphereBouquetFun' f) = refl

FAGAbGroup→AbGroupHom : ∀ {ℓ ℓ'} {A : Type ℓ} {G : AbGroup ℓ'}
  → (A → fst G) → AbGroupHom (FAGAbGroup {A = A}) G
fst (FAGAbGroup→AbGroupHom {G = G} f) =
  Rec.f (AbGroupStr.is-set (snd G)) f
    (AbGroupStr.0g (snd G)) (AbGroupStr._+_ (snd G)) (AbGroupStr.-_ (snd G))
    (AbGroupStr.+Assoc (snd G)) (AbGroupStr.+Comm (snd G))
    (AbGroupStr.+IdR (snd G)) (AbGroupStr.+InvR (snd G))
snd (FAGAbGroup→AbGroupHom {G = G} f) = makeIsGroupHom λ x y → refl

FAGAbGroupGroupHom≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {G : AbGroup ℓ'}(f g : AbGroupHom (FAGAbGroup {A = A}) G)
               → (∀ a → (fst f) (⟦ a ⟧) ≡ (fst g) (⟦ a ⟧)) → f ≡ g
FAGAbGroupGroupHom≡ {G = G} f g p =
  GroupHom≡ (funExt (ElimProp.f (AbGroupStr.is-set (snd G) _ _)
    p (IsGroupHom.pres1 (snd f) ∙ sym (IsGroupHom.pres1 (snd g)))
    (λ p q → IsGroupHom.pres· (snd f) _ _
            ∙ cong₂ (AbGroupStr._+_ (snd G)) p q
            ∙ sym (IsGroupHom.pres· (snd g) _ _))
    λ p → IsGroupHom.presinv (snd f) _
        ∙ cong (AbGroupStr.-_ (snd G)) p
        ∙ sym (IsGroupHom.presinv (snd g) _)))

module _ {ℓ} {A : Type ℓ} where
  freeGroup→freeAbGroup : GroupHom (freeGroupGroup A) (AbGroup→Group (FAGAbGroup {A = A}))
  freeGroup→freeAbGroup = FG.rec {Group = AbGroup→Group (FAGAbGroup {A = A})} ⟦_⟧

  AbelienizeFreeGroup→FreeAbGroup : AbGroupHom (AbelianizationAbGroup (freeGroupGroup A)) (FAGAbGroup {A = A})
  AbelienizeFreeGroup→FreeAbGroup = fromAbelianization FAGAbGroup freeGroup→freeAbGroup

  FreeAbGroup→AbelienizeFreeGroup : AbGroupHom (FAGAbGroup {A = A}) (AbelianizationAbGroup (freeGroupGroup A))
  FreeAbGroup→AbelienizeFreeGroup = FAGAbGroup→AbGroupHom λ a → η (η a)

  GroupIso-AbelienizeFreeGroup→FreeAbGroup :
    AbGroupIso (AbelianizationAbGroup (freeGroupGroup A)) (FAGAbGroup {A = A})
  Iso.fun (fst GroupIso-AbelienizeFreeGroup→FreeAbGroup) = AbelienizeFreeGroup→FreeAbGroup .fst
  Iso.inv (fst GroupIso-AbelienizeFreeGroup→FreeAbGroup) = FreeAbGroup→AbelienizeFreeGroup .fst
  Iso.rightInv (fst GroupIso-AbelienizeFreeGroup→FreeAbGroup) x i =
    FAGAbGroupGroupHom≡
      (compGroupHom FreeAbGroup→AbelienizeFreeGroup AbelienizeFreeGroup→FreeAbGroup)
      idGroupHom (λ _ → refl) i .fst x
  Iso.leftInv (fst GroupIso-AbelienizeFreeGroup→FreeAbGroup) = Abi.elimProp _ (λ _ → isset _ _)
    (funExt⁻ (cong fst (freeGroupHom≡
      {f = compGroupHom  freeGroup→freeAbGroup FreeAbGroup→AbelienizeFreeGroup }
      {g = AbelianizationGroupStructure.ηAsGroupHom (freeGroupGroup A)}
      λ _ → refl)))
  snd GroupIso-AbelienizeFreeGroup→FreeAbGroup = AbelienizeFreeGroup→FreeAbGroup .snd

open import Cubical.Foundations.Powerset
module _ {ℓ ℓ'} {A : Type ℓ} (B : Pointed ℓ') where
  BouquetFun∙→Ω : (Bouquet∙ A →∙ B) → (A → Ω B .fst)
  BouquetFun∙→Ω f x = sym (snd f) ∙∙ cong (fst f) (loop x) ∙∙ snd f

  Ω→BouquetFun∙ : (A → Ω B .fst) → (Bouquet∙ A →∙ B)
  fst (Ω→BouquetFun∙ f) base = pt B
  fst (Ω→BouquetFun∙ f) (loop x i) = f x i
  snd (Ω→BouquetFun∙ f) = refl

  CharacBouquetFun∙ : Iso (Bouquet∙ A →∙ B) (A → Ω B .fst)
  Iso.fun CharacBouquetFun∙ = BouquetFun∙→Ω
  Iso.inv CharacBouquetFun∙ = Ω→BouquetFun∙
  Iso.rightInv CharacBouquetFun∙ h =
    funExt λ x → sym (rUnit (h x))
  fst (Iso.leftInv CharacBouquetFun∙ h i) base = snd h (~ i)
  fst (Iso.leftInv CharacBouquetFun∙ h i) (loop x j) =
    doubleCompPath-filler (sym (snd h)) (cong (fst h) (loop x)) (snd h) (~ i) j
  snd (Iso.leftInv CharacBouquetFun∙ h i) j = snd h (~ i ∨ j)


CharacBouquet→∙Bouquet : {m k : ℕ}
  → Iso (Bouquet∙ (Fin m) →∙ Bouquet∙ (Fin k))
         (Fin m → FreeGroup (Fin k))
CharacBouquet→∙Bouquet = compIso (CharacBouquetFun∙ (Bouquet∙ (Fin _)))
  (codomainIso Iso-ΩS¹Bouquet-FreeGroup)

module spB {m k : ℕ}
  (α' : Fin m → FreeGroup (Fin k)) where
  α :  Bouquet∙ (Fin m)
    →∙ Bouquet∙ (Fin k)
  α = Iso.inv CharacBouquet→∙Bouquet α'

  pickGens : GroupHom (freeGroupGroup (Fin m)) (freeGroupGroup (Fin k))
  pickGens = FG.rec α'

  pickGens' : GroupHom (freeGroupGroup (Fin m)) (AbGroup→Group (AbelianizationAbGroup (freeGroupGroup (Fin k))))
  pickGens' = compGroupHom pickGens (AbelianizationGroupStructure.ηAsGroupHom _)

  _·f_ : ∀ {ℓ} {A : Type ℓ} → FreeGroup A → FreeGroup A → FreeGroup A
  _·f_ = FG._·_

  Free/Imα' : Group₀
  Free/Imα' = AbGroup→Group (AbelianizationAbGroup (freeGroupGroup (Fin k)))
            / (imSubgroup pickGens' , isNormalIm _ λ _ _ → AbelianizationGroupStructure.commAb _ _ _)

  Code' : Fin k → S¹ → Type₀
  Code' k base = Free/Imα' .fst
  Code' k (loop i) = ua (isoToEquiv (·GroupAutomorphismR (Free/Imα') [ η (η k) ])) i

  CodePre : Bouquet (Fin k) → Type
  CodePre base = Free/Imα' .fst
  CodePre (loop x i) = ua (isoToEquiv (·GroupAutomorphismR (Free/Imα') [ η (η x) ])) i


  substCodePre : (p : _) (x : _)
    → subst CodePre (Iso.inv Iso-ΩS¹Bouquet-FreeGroup p) [ η x ]
     ≡ [ η (x FG.· p)  ]
  substCodePre = FG.elimProp (λ _ → isPropΠ (λ _ → squash/ _ _))
    (λ a x i → [ η (transportRefl x i FG.· η (transportRefl a i)) ])
    (λ g1 g2 p q x
      → cong (λ P → subst CodePre P [ η x ])
             (InvIso-ΩS¹Bouquet-FreeGroupPresStr g1 g2)
      ∙ substComposite CodePre
         (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g1)
         (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g2) [ η x ]
      ∙ cong (subst CodePre (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g2))
             (p x)
      ∙ q (x FG.· g1)
      ∙ λ i → [ η (FG.assoc x g1 g2 (~ i)) ])
    (λ x i → [ η ((transportRefl x ∙ FG.idr x) i) ])
    λ g p x → cong (λ P → subst CodePre P [ η x ])
                (InvIso-ΩS¹Bouquet-FreeGroupPresInv g)
             ∙ cong (subst CodePre (sym (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g)))
                 (λ i → [ η ((FG.idr x
                           ∙ cong₂ FG._·_ refl (sym (FG.invl g))
                           ∙ (FG.assoc x (inv g) g)) i) ])
             ∙ sym (cong (subst CodePre (sym (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g)))
                     (p (x FG.· inv g)))
             ∙ subst⁻Subst CodePre (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g )
               [ η (x FG.· inv g) ]


  CodeCofibα : cofib (fst α) → Type
  CodeCofibα (inl x) = Free/Imα' .fst
  CodeCofibα (inr x) = CodePre x
  CodeCofibα (push base i) = Free/Imα' .fst
  CodeCofibα (push (loop x j) i) = H i j
    where
    open AbelianizationGroupStructure (freeGroupGroup (Fin k))
    H : refl ≡ cong (CodePre) (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (α' x))
    H = sym uaIdEquiv
          ∙ cong ua (Σ≡Prop (λ _ → isPropIsEquiv _)
            (funExt (SQ.elimProp (λ _ → squash/ _ _)
              (Abi.elimProp _ (λ _ → squash/ _ _)
                λ g → sym (substCodePre (α' x) g
                    ∙ eq/ _ _ ∣ (η x)
                             , (sym (ridAb (η (α' x)))
                             ∙ commAb (η (α' x)) 1Ab)
                             ∙ cong₂ _·Ab_ (sym (rinvAb (η g))) refl
                             ∙ sym (assocAb (η g) (η (inv g)) (η (α' x)))
                             ∙ cong₂ _·Ab_ refl (commAb (η (inv g)) (η (α' x)))
                             ∙ assocAb (η g) (η (α' x)) (η (inv g)) ∣₁)))))
          ∙ retEq univalence _


  isSetCodeCofibα : (x : _) → isSet (CodeCofibα x)
  isSetCodeCofibα =
    PO.elimProp _ (λ _ → isPropIsSet)
      (λ _ → GroupStr.is-set (Free/Imα' .snd))
      (elimPropBouquet
        (λ _ → isPropIsSet)
        (GroupStr.is-set (Free/Imα' .snd)))

  L : GroupHom (freeGroupGroup (Fin k))
      (πGr 0 (Pushout (λ _ → tt) (fst α) , inr base))
  fst L b = ∣ (λ i → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup b i)) ∣₂
  snd L = makeIsGroupHom λ a b
    → cong ∣_∣₂ ((λ i j → inr (InvIso-ΩS¹Bouquet-FreeGroupPresStr a b i j))
      ∙ cong-∙ inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup a)
                   (Iso.inv Iso-ΩS¹Bouquet-FreeGroup b))

  Lα : (x : Fin m) → Path (Path (cofib (fst α)) (inr base) (inr base))
                       (λ i → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (α' x) i))
                       refl
  Lα x i j = hcomp (λ k → λ {(i = i0) → push (loop x j) k
                           ; (i = i1) → push base k
                           ; (j = i0) → push base k
                           ; (j = i1) → push base k})
                  (inl tt)


  decodeCofibαinrFun : FreeGroup (Fin k) → ∥ _≡ᵃᵇ_ {A = cofib (fst α)} (inr base) (inr base) ∥₂
  decodeCofibαinrFun s = ∣ paths ((λ i → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup s i))) ∣₂

  decodeCofibαinlFun : FreeGroup (Fin k) → ∥ _≡ᵃᵇ_ {A = cofib (fst α)} (inr base) (inl tt) ∥₂
  decodeCofibαinlFun s = ·πᵃᵇ (decodeCofibαinrFun s) ∣ paths (sym (push base)) ∣₂

  decodeCofibαinr : Abelianization (freeGroupGroup (Fin k)) → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr base) ∥₂
  decodeCofibαinr = fst Abelianizeπ₁→π₁ᵃᵇ ∘ AbelianizationFun L .fst

  inr' : Bouquet (Fin k) → cofib (fst α)
  inr' = inr

  decodeCofibαinrHom : AbGroupHom (AbelianizationAbGroup (freeGroupGroup (Fin k)))
                                  (π₁ᵃᵇAbGroup (cofib (fst α) , inr base))
  decodeCofibαinrHom = compGroupHom (AbelianizationFun L) Abelianizeπ₁→π₁ᵃᵇ

  decodeCofibαinr≡ : (x : FreeGroup (Fin m)) → (a : FreeGroup (Fin k))
    → ·πᵃᵇ (decodeCofibαinr (pickGens' .fst x)) (decodeCofibαinr (η a)) ≡ decodeCofibαinr (η a)
  decodeCofibαinr≡ = FG.elimProp (λ _ → isPropΠ λ _ → squash₂ _ _)
    (λ c a → (λ i → ·πᵃᵇ ∣ paths (Lα c i) ∣₂ (decodeCofibαinr (η a)))
                 ∙ cong ∣_∣₂ (cong paths (sym (lUnit _))))
    (λ g1 g2 p q a
      → cong₂ ·πᵃᵇ (cong decodeCofibαinr (IsGroupHom.pres· (snd pickGens') g1 g2)
                 ∙ IsGroupHom.pres· (snd (compGroupHom (AbelianizationFun L) (Abelianizeπ₁→π₁ᵃᵇ)))
                                    (fst pickGens' g1) (fst pickGens' g2))
               (λ _ → (decodeCofibαinr (η a)))
                    ∙ sym (·πᵃᵇassoc (decodeCofibαinr (pickGens' .fst g1))
                                    (decodeCofibαinr (pickGens' .fst g2)) (decodeCofibαinr (η a)))
                    ∙ cong (·πᵃᵇ (decodeCofibαinr (pickGens' .fst g1))) (q a)
                    ∙ p a)
      (λ a → ·πᵃᵇlUnit (decodeCofibαinr (η a)))
      λ g p a → cong₂ ·πᵃᵇ
                  (sym (sym (IsGroupHom.presinv (snd (compGroupHom (AbelianizationFun L)
                          (Abelianizeπ₁→π₁ᵃᵇ))) (pickGens' .fst g))
                    ∙ cong decodeCofibαinr (IsGroupHom.presinv (snd pickGens') g)))
                  (sym (sym (IsGroupHom.presinv (snd (compGroupHom (AbelianizationFun L)
                          (Abelianizeπ₁→π₁ᵃᵇ))) (η (inv a)))
                ∙ cong (decodeCofibαinr ∘ η) (GroupTheory.invInv (freeGroupGroup (Fin k)) a)))
                ∙ sym (-πᵃᵇinvDistr (decodeCofibαinr (pickGens' .fst g)) (decodeCofibαinr (η (inv a))))
                ∙ cong -πᵃᵇ (p (inv a))
                ∙ sym (IsGroupHom.presinv (snd (compGroupHom (AbelianizationFun L)
                          (Abelianizeπ₁→π₁ᵃᵇ))) (η (inv a)))
                ∙ cong (decodeCofibαinr ∘ η) (GroupTheory.invInv (freeGroupGroup (Fin k)) a)

  h : (x : FreeGroup (Fin m)) (a b : FreeGroup (Fin k)) (q : ·πᵃᵇ (decodeCofibαinr (pickGens' .fst x)) (decodeCofibαinr (η b)) ≡ decodeCofibαinr (η a))
     → Path (∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr base) ∥₂)
             (decodeCofibαinr (η a)) (decodeCofibαinr (η b))
  h x a b q = sym q ∙ decodeCofibαinr≡ x b


  decodeCofibαinl : Abelianization (freeGroupGroup (Fin k)) → ∥ (inr base) ≡ᵃᵇ inl tt ∥₂
  decodeCofibαinl = Abi.rec _ squash₂ decodeCofibαinlFun
   λ a b c → cong₂ ·πᵃᵇ (cong ∣_∣₂ (lem a b c)
                    ∙ cong (·πᵃᵇ (∣ paths (t a) ∣₂))
                           (·πᵃᵇcomm ∣ paths (t b) ∣₂ ∣ paths (t c) ∣₂)
                    ∙ sym (cong ∣_∣₂ (lem a c b)))
                        (λ _ → ∣ paths (sym (push base)) ∣₂)
    where
    t : (x : _) → Path (cofib (fst α)) _ _
    t x i = inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup x i)

    lem : (x y z : _)
      → Path (Pathᵃᵇ (cofib (fst α)) _ _)
          (paths (t (x ·f (y ·f z))))
          (paths (t x ∙ t y ∙ t z))

    lem x y z =
      cong paths (((λ j i → inr (InvIso-ΩS¹Bouquet-FreeGroupPresStr x (y ·f z) j i))
         ∙ cong-∙ inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup x)
                      (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (y ·f z)))
        ∙ cong₂ _∙_ refl ((λ j i → inr (InvIso-ΩS¹Bouquet-FreeGroupPresStr y z j i))
                        ∙ cong-∙ inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup y)
                                     (Iso.inv Iso-ΩS¹Bouquet-FreeGroup z)))


  InrHom : GroupHom Free/Imα' (AbGroup→Group (π₁ᵃᵇAbGroup (cofib (fst α) , inr base)))
  fst InrHom = SQ.rec squash₂ decodeCofibαinr main
    where
    main : (a b : _) (q : _) → _
    main = Abi.elimProp2 _ (λ _ _ → isPropΠ (λ _ → squash₂ _ _))
      λ a b → PT.elim (λ _ → squash₂ _ _)
        λ {(x , q)
          → h x a b (cong (λ s → ·πᵃᵇ s (decodeCofibαinr (η b)) )
                (cong decodeCofibαinr q ∙ IsGroupHom.pres· (snd decodeCofibαinrHom) (η a) (η (inv b)))
                ∙ (sym (·πᵃᵇassoc (decodeCofibαinr (η a)) (decodeCofibαinr (η (inv b))) (decodeCofibαinr (η b))))
                ∙ cong (·πᵃᵇ (decodeCofibαinr (η a)))
                   (cong₂ ·πᵃᵇ (IsGroupHom.presinv (snd decodeCofibαinrHom) (η b)) refl
                   ∙ ·πᵃᵇlCancel ((decodeCofibαinr (η b))))
                ∙ ·πᵃᵇrUnit (decodeCofibαinr (η a)))}
  snd InrHom =
    makeIsGroupHom (SQ.elimProp2
      (λ _ _ → squash₂ _ _)
      (IsGroupHom.pres· (snd decodeCofibαinrHom)))

  decodeCofibαInrFull : (x : _) → CodeCofibα (inr x) → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr x) ∥₂
  decodeCofibαInrFull base = fst InrHom
  decodeCofibαInrFull (loop x i) = help i
    where
    lem : (p : _)
     → transport (λ i₁ → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr (loop x i₁)) ∥₂)
                  (·πᵃᵇ p (-πᵃᵇ (decodeCofibαinr (η (η x))))) ≡ p
    lem = ST.elim (λ _ → isSetPathImplicit)
      (elimProp≡ᵃᵇ (λ _ → squash₂ _ _) λ p
        → (λ j → transp (λ i₁ → ∥ Pathᵃᵇ (cofib (fst α))
                                    (inr base) (inr (loop x (i₁ ∨ j))) ∥₂) j
                        ∣ paths (p ∙ (λ i₁ → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (η x) (~ i₁ ∨ j)))) ∣₂)
       ∙ cong ∣_∣₂ (cong paths (sym (rUnit p))))

    help : PathP (λ i → ua (isoToEquiv (·GroupAutomorphismR Free/Imα' [ η (η x) ])) i
                      →  ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr (loop x i)) ∥₂)
                (fst InrHom) (fst InrHom)
    help = toPathP (funExt (SQ.elimProp (λ _ → squash₂ _ _)
      λ s → cong (transport (λ i → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr (loop x i)) ∥₂))
                  ((cong (fst InrHom)
                    (cong (Iso.inv (·GroupAutomorphismR Free/Imα' [ η (η x) ]))
                      (transportRefl [ s ]))
                   ∙ IsGroupHom.pres· (snd InrHom) [ s ] [ η (inv (η x)) ]
                   ∙ cong (·πᵃᵇ (decodeCofibαinr s)) (IsGroupHom.presinv (snd InrHom) [ η (η x) ])))
                ∙ lem (decodeCofibαinr s)))


  decodeCofibα : (x : _) → CodeCofibα x → ∥ (inr base) ≡ᵃᵇ x ∥₂
  decodeCofibα (inl x) p = ·πᵃᵇ (decodeCofibαInrFull base p) ∣ paths (sym (push base)) ∣₂
  decodeCofibα (inr x) = decodeCofibαInrFull x
  decodeCofibα (push a i) = help a i
    where
    help : (a : Bouquet (Fin m))
      → PathP (λ i → CodeCofibα (push a i) → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (push a i) ∥₂)
               (λ p → ·πᵃᵇ (decodeCofibαInrFull base p) ∣ paths (sym (push base)) ∣₂)
               (decodeCofibαInrFull (Iso.inv CharacBouquet→∙Bouquet α' .fst a))
    help =
      elimPropBouquet (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → squash₂)) _ _)
        (funExt (SQ.elimProp (λ _ → isOfHLevelPathP' 1 squash₂ _ _)
          (Abi.elimProp _ (λ _ → isOfHLevelPathP' 1 squash₂ _ _)
            λ g → λ i → ∣ paths (compPath-filler
              (λ i₂ → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g i₂))
              (sym (push base)) (~ i)) ∣₂)))

  CodeCofibα+Inr : (x : _) → (CodeCofibα (inr base)) → CodeCofibα (inr x) → CodeCofibα (inr x)
  CodeCofibα+Inr base p q = GroupStr._·_ (snd Free/Imα') p q
  CodeCofibα+Inr (loop x i) p = help i
    where
    typecheck : ∀ {ℓ} (A B : Type ℓ) (p : A ≡ B)
      (f : A → A) (g : B → B) → ((x : _) → transport p (f (transport (sym p) x)) ≡ g x)
      → PathP (λ i → p i → p i) f g
    typecheck = λ A → J> λ f g p → funExt λ x → sym (transportRefl _ ∙ cong f (transportRefl x)) ∙ p x

    typecheck' : ∀ {ℓ} {A B : Type ℓ} (p : A ≃ B)
      {f : A → A} {g : B → B} → ((x : _) → fst p (f (invEq p x)) ≡ g x)
        → PathP (λ i → ua p i → ua p i) f g
    typecheck' p {f = f} {g} h =
      typecheck _ _ (ua p) f g λ b
        → transportRefl _ ∙ cong (fst p) (cong f (cong (invEq p) (transportRefl b))) ∙ h b

    help : PathP (λ i → ua (isoToEquiv (·GroupAutomorphismR Free/Imα' [ η (η x) ]))  i
           → ua (isoToEquiv (·GroupAutomorphismR Free/Imα' [ η (η x) ])) i)
           (GroupStr._·_ (snd Free/Imα') p)
           (GroupStr._·_ (snd Free/Imα') p)
    help = typecheck' (isoToEquiv (·GroupAutomorphismR Free/Imα' [ η (η x) ]))
      (SQ.elimProp (λ _ → squash/ _ _)
        (Abi.elimProp _ (λ _ → squash/ _ _)
          λ g → sym (GroupStr.·Assoc (snd Free/Imα') p
                  ((invEq (isoToEquiv (·GroupAutomorphismR Free/Imα' [ η (η x) ])) [ η g ]))
                  [ η (η x) ])
              ∙ cong (snd Free/Imα' GroupStr.· p)
                 (sym (GroupStr.·Assoc (snd Free/Imα')
                      [ η g ] [ η (inv (η x)) ]  [ η (η x) ])
                ∙ cong (snd Free/Imα' GroupStr.· [ η g ])
                  (GroupStr.·InvL (snd Free/Imα') [ η (η x) ])
                ∙ GroupStr.·IdR (snd Free/Imα') [ η g ])))


  CodeCofibα+ : (x : _) → (CodeCofibα (inr base)) → CodeCofibα x → CodeCofibα x
  CodeCofibα+ (inl x) p q = GroupStr._·_ (snd Free/Imα') p q
  CodeCofibα+ (inr x) = CodeCofibα+Inr x
  CodeCofibα+ (push x i) p = help x i
    where
    help : (x : Bouquet (Fin m))
      → PathP (λ i → CodeCofibα (push x i) → CodeCofibα (push x i))
              ((snd Free/Imα' GroupStr.· p))
              (CodeCofibα+Inr (α .fst x) p)
    help = elimPropBouquet
      (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → isSetCodeCofibα _)) _ _)
      refl

  preEncodeHom : (x : cofib (fst α)) (p : inr base ≡ x) (s t : Free/Imα' .fst)
    → subst CodeCofibα p (GroupStr._·_ (snd Free/Imα') s t)
    ≡ CodeCofibα+ x s (subst CodeCofibα p t )
  preEncodeHom = J> λ s t → transportRefl _
    ∙ cong (GroupStr._·_ (snd Free/Imα') s) (sym (transportRefl t))

  cono'Inr : (x : _) (p : Path (cofib (fst α)) (inr base) (inr x)) → hProp ℓ-zero
  cono'Inr base p = (∃[ r ∈ Path (Bouquet (Fin k)) base base ] p ≡ λ i → inr (r i)) , squash₁
  fst (cono'Inr (loop x i) p) =
    ∃[ r ∈ Path (Bouquet (Fin k)) base (loop x i) ] p ≡ λ i → inr (r i)
  snd (cono'Inr (loop x i) p) = squash₁

  cono : (x : cofib (fst α)) (p : inr base ≡ x) → Type
  cono (inl x) p = ∃[ r ∈ Path (Bouquet (Fin k)) base base ] p ≡ (λ i → inr (r i)) ∙ sym (push base)
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

  toCono : (x : cofib (fst α)) (p : inr base ≡ x)  → cono x p
  toCono = J> ∣ refl , refl ∣₁


  encodeCofibαPre : (x : _) → Pathᵃᵇ (cofib (fst α)) (inr base) x → CodeCofibα x
  encodeCofibαPre x (paths q) = subst CodeCofibα q [ η ε ]
  encodeCofibαPre x (com p q r i) = ha _ q p r i
    where

    ha : (x : _) (q p r : inr base ≡ x)
      → subst CodeCofibα (p ∙ sym q ∙ r) [ η ε ]
       ≡ subst CodeCofibα (r ∙ sym q ∙ p) [ η ε ]
    ha = J> λ p q
      → cong (λ p → subst CodeCofibα p [ η ε ]) (cong (p ∙_) (sym (lUnit q)))
      ∙ substComposite CodeCofibα p q [ η ε ]
      ∙ PT.rec2 (squash/ _ _)
          (λ {(x' , xe) (y' , ye)
            → lem (Iso.fun Iso-ΩS¹Bouquet-FreeGroup x') (Iso.fun Iso-ΩS¹Bouquet-FreeGroup y')
                  p
                  (cong (cong inr') (Iso.leftInv Iso-ΩS¹Bouquet-FreeGroup x') ∙ sym xe)
                  q
                  (cong (cong inr') (Iso.leftInv Iso-ΩS¹Bouquet-FreeGroup y') ∙ sym ye)})
          (toCono _ p)
          (toCono _ q)
      ∙ sym (substComposite CodeCofibα q p [ η ε ])
      ∙ cong (λ p → subst CodeCofibα p [ η ε ]) (cong (q ∙_) (lUnit p))
      where
      lem : (x y : FreeGroup (Fin k)) (p : Path (cofib (fst α)) (inr base) (inr base))
            (s : (λ i → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup x i)) ≡ p)
            (q : Path (cofib (fst α)) (inr base) (inr base))
            (s' : (λ i → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup y i)) ≡ q)
         → subst CodeCofibα q (subst CodeCofibα p [ η ε ])
         ≡ subst CodeCofibα p (subst CodeCofibα q [ η ε ])
      lem x y =
        J> (J> cong (subst CodeCofibα y')
             (substCodePre x ε ∙ GroupStr.·IdL (snd Free/Imα') [ η x ])
         ∙ substCodePre y x
         ∙ cong [_] (AbelianizationGroupStructure.commAb
                     (freeGroupGroup (Fin k)) (η x) (η y))
         ∙ sym (substCodePre x y)
         ∙ cong (subst CodeCofibα x')
             (sym (substCodePre y ε ∙ GroupStr.·IdL (snd Free/Imα') [ η y ])) )
        where
        x' y' : Path (cofib (fst α)) (inr base) (inr base)
        x' =  (λ i₁ → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup x i₁))
        y' =  (λ i₁ → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup y i₁))

  encodeCofibα : (x : _) → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) x ∥₂ → CodeCofibα x
  encodeCofibα x = ST.rec (isSetCodeCofibα _) (encodeCofibαPre x)

  decodeEncodeCofibα : (x : _) (p : ∥ Pathᵃᵇ (cofib (fst α)) (inr base) x ∥₂)
    → decodeCofibα x (encodeCofibα x p) ≡ p
  decodeEncodeCofibα x = ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
    (J (λ x p → decodeCofibα x (encodeCofibα x ∣ paths p ∣₂) ≡ ∣ paths p ∣₂)
      refl))

  encodeDecodeCofibα : (p : _) → encodeCofibα (inr base) (decodeCofibα (inr base) p) ≡ p
  encodeDecodeCofibα = SQ.elimProp (λ _ → squash/ _ _)
    (Abi.elimProp _ (λ _ → squash/ _ _)
      λ w → substCodePre w ε ∙ λ i → [ η (FG.idl w (~ i)) ])

  Free/≅π₁ᵃᵇCofibBouquetMap : GroupIso Free/Imα' (AbGroup→Group (π₁ᵃᵇAbGroup (cofib (fst α) , inr base)))
  Iso.fun (fst Free/≅π₁ᵃᵇCofibBouquetMap) = InrHom .fst
  Iso.inv (fst Free/≅π₁ᵃᵇCofibBouquetMap) = encodeCofibα (inr base)
  Iso.rightInv (fst Free/≅π₁ᵃᵇCofibBouquetMap) = decodeEncodeCofibα (inr base)
  Iso.leftInv (fst Free/≅π₁ᵃᵇCofibBouquetMap) = encodeDecodeCofibα
  snd Free/≅π₁ᵃᵇCofibBouquetMap = InrHom .snd

  Free/≅π₁ᵃᵇCofibBouquetMap' :
    GroupIso Free/Imα'
             (AbGroup→Group
               (AbelianizationAbGroup (πGr 0 (cofib (fst α) , inr base))))
  Free/≅π₁ᵃᵇCofibBouquetMap' =
    compGroupIso Free/≅π₁ᵃᵇCofibBouquetMap
      (invGroupIso (Abelianizeπ₁≅π₁ᵃᵇ (_ , inr base)))
  
module _ {m k : ℕ} (α' : Bouquet∙ (Fin m) →∙ Bouquet∙ (Fin k)) where
