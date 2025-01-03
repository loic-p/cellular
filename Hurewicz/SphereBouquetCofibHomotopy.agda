{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.SphereBouquetCofibHomotopy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed


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


open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Pushout as PO

·GroupAutomorphism : ∀ {ℓ} (G : Group ℓ) (g : fst G) → Iso (fst G) (fst G)
Iso.fun (·GroupAutomorphism G g) = GroupStr._·_ (snd G) g
Iso.inv (·GroupAutomorphism G g) = GroupStr._·_ (snd G) (GroupStr.inv (snd G) g)
Iso.rightInv (·GroupAutomorphism G g) h =
  GroupStr.·Assoc (snd G) _ _ _
  ∙ cong₂ (GroupStr._·_ (snd G)) (GroupStr.·InvR (snd G) g) refl
  ∙ GroupStr.·IdL (snd G) h
Iso.leftInv (·GroupAutomorphism G g) h =
  GroupStr.·Assoc (snd G) _ _ _
  ∙ cong₂ (GroupStr._·_ (snd G)) (GroupStr.·InvL (snd G) g) refl
  ∙ GroupStr.·IdL (snd G) h

·GroupAutomorphismR : ∀ {ℓ} (G : Group ℓ) (g : fst G) → Iso (fst G) (fst G)
Iso.fun (·GroupAutomorphismR G g) x = GroupStr._·_ (snd G) x g
Iso.inv (·GroupAutomorphismR G g) x = GroupStr._·_ (snd G) x (GroupStr.inv (snd G) g)
Iso.rightInv (·GroupAutomorphismR G g) h =
  sym (GroupStr.·Assoc (snd G) _ _ _)
  ∙ cong₂ (GroupStr._·_ (snd G)) refl (GroupStr.·InvL (snd G) g) -- 
  ∙ GroupStr.·IdR (snd G) h
Iso.leftInv (·GroupAutomorphismR G g) h =
    sym (GroupStr.·Assoc (snd G) _ _ _)
  ∙ cong₂ (GroupStr._·_ (snd G)) refl (GroupStr.·InvR (snd G) g) -- 
  ∙ GroupStr.·IdR (snd G) h

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

Iso-ΩS¹Bouquet-FreeGroup : {n : ℕ} → Iso (fst (Ω (Bouquet∙ (Fin n)))) (FreeGroup (Fin n))
Iso-ΩS¹Bouquet-FreeGroup =
  compIso
    (compIso (invIso (setTruncIdempotentIso (isOfHLevelPath' 2
      (isGroupoidBouquet DiscreteFin) _ _)))
             (equivToIso (TruncatedFamiliesEquiv base)))
    (equivToIso (invEquiv freeGroupTruncIdempotent≃))

GroupIso-πS¹Bouquet-FreeGroup : {!{n : ℕ} → Iso (fst (Ω (Bouquet∙ (Fin n)))) (FreeGroup (Fin n))!}
GroupIso-πS¹Bouquet-FreeGroup = {!!}

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

-- Iso (Free A)ᵃᵇ ≅ (FreeAb A)
module _ {ℓ} {G : Group ℓ} (H : AbGroup ℓ) (ϕ : GroupHom G (AbGroup→Group H)) where
  fromAbelianization : AbGroupHom (AbelianizationAbGroup G) H
  fst fromAbelianization = Abi.rec G (AbGroupStr.is-set (snd H)) (fst ϕ)
    λ x y z → IsGroupHom.pres· (snd ϕ) _ _
            ∙ cong₂ (AbGroupStr._+_ (snd H)) refl
                (IsGroupHom.pres· (snd ϕ) _ _
                ∙ AbGroupStr.+Comm (snd H) _ _
                ∙ sym (IsGroupHom.pres· (snd ϕ) _ _))
            ∙ sym (IsGroupHom.pres· (snd ϕ) _ _)
  snd fromAbelianization =
    makeIsGroupHom (Abi.elimProp2 _
      (λ _ _ → AbGroupStr.is-set (snd H) _ _)
      λ x y → IsGroupHom.pres· (snd ϕ) x y)

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
module spB {m k : ℕ}
  (α' : Fin m → FreeGroup (Fin k)) where
  α :  Bouquet∙ (Fin m)
    →∙ Bouquet∙ (Fin k)
  α = makeSphereBouquetFun' α'

  αD' : AbGroupHom (ℤ[Fin m ]) (ℤ[Fin k ])
  fst αD' F t = {!!}
  snd αD' = {!!}

  pickGens : GroupHom (freeGroupGroup (Fin m)) (freeGroupGroup (Fin k))
  pickGens = FG.rec α'

  pickGens' : GroupHom (freeGroupGroup (Fin m)) (AbGroup→Group (AbelianizationAbGroup (freeGroupGroup (Fin k))))
  pickGens' = compGroupHom pickGens (AbelianizationGroupStructure.ηAsGroupHom _)

  _·f_ : ∀ {ℓ} {A : Type ℓ} → FreeGroup A → FreeGroup A → FreeGroup A
  _·f_ = FG._·_

  Free/Imα' : Group₀
  Free/Imα' = AbGroup→Group (AbelianizationAbGroup (freeGroupGroup (Fin k)))
            / (imSubgroup pickGens' , isNormalIm _ λ _ _ → AbelianizationGroupStructure.commAb _ _ _)

  -- ℤ/Imα : Group₀
  -- ℤ/Imα = AbGroup→Group (ℤ[Fin k ]) / ((imSubgroup (bouquetDegree (fst α))) , (isNormalIm _ λ _ _ → AbGroupStr.+Comm (snd ℤ[Fin k ]) _ _))

  Code' : Fin k → S¹ → Type₀
  Code' k base = Free/Imα' .fst
  Code' k (loop i) = ua (isoToEquiv (·GroupAutomorphismR (Free/Imα') [ η (η k) ])) i

  CodePre : Bouquet (Fin k) → Type
  CodePre base = Free/Imα' .fst
  CodePre (loop x i) = ua (isoToEquiv (·GroupAutomorphismR (Free/Imα') [ η (η x) ])) i

  CodeCofibα : cofib (fst α) → Type
  CodeCofibα (inl x) = Free/Imα' .fst
  CodeCofibα (inr x) = CodePre x
  CodeCofibα (push base i) = Free/Imα' .fst
  CodeCofibα (push (loop x j) i) = H _ refl i j
    where
    H : (t : _) → α' x ≡ t → refl ≡ cong (CodePre ∘ fst α) (loop x)
    H = FG.elimProp {!(cong (fst α) (loop x))!}
      (λ p q → transport (λ i → refl ≡ cong CodePre (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (q (~ i))))
                          ((sym uaIdEquiv
                          ∙ cong ua (Σ≡Prop {!!} (funExt (SQ.elimProp {!!} (Abi.elimProp _ {!!} (λ g → eq/ _ _ ∣ (inv (η x)) , {!!} ∣₁))))))
                          ∙ (λ j → isoToPath (·GroupAutomorphismR Free/Imα' [ η (q j) ]))))
                          {!λ g1 !}
      (λ p → transport (λ i → refl ≡ cong CodePre (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (p (~ i))))
                          refl)
        {!!}


  isSetCodeCofibα : (x : _) → isSet (CodeCofibα x)
  isSetCodeCofibα = {!!}

  decodeCofibα : (x : _) → CodeCofibα x → ∥ inr base ≡ x ∥₂
  decodeCofibα (inl x) = {!!}
  decodeCofibα (inr base) = SQ.elim {!!} {!!} {!!}
  decodeCofibα (inr (loop x i)) = {!!}
  decodeCofibα (push a i) = {!a!}

    -- sym uaIdEquiv ∙ {!!} ∙ λ i → cong CodePre (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (α' x))
  {-
  CodeCofibα (inl x) = Free/Imα' .fst
  CodeCofibα (inr x) = CodePre x
  CodeCofibα (push (inl x) i) = Free/Imα' .fst
  CodeCofibα (push (inr (x , y)) i) = {!fst (makeSphereBouquetFun α') (inr (x , y))!}
    where
    oh : (y : S¹) → Free/Imα' .fst
                   ≃ CodePre (fst (makeSphereBouquetFun α') (inr (x , y)))
    oh base = idEquiv (Free/Imα' .fst)
    oh (loop i) = {!!}
      where
      cool : PathP (λ i → Free/Imα' .fst
                         ≃ CodePre (Bouquet→SphereBouquet
                            (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (α' x) i)))
                    (idEquiv _) (idEquiv _)
      cool = ΣPathPProp (λ _ → isPropIsEquiv _)
        (funExt (SQ.elimProp
          (λ _ → isOfHLevelPathP' 1 (GroupStr.is-set (Free/Imα' .snd)) _ _)
          (Abi.elimProp _
            (λ _ → isOfHLevelPathP' 1 (GroupStr.is-set (Free/Imα' .snd)) _ _)
            (FG.elimProp {!!} {!!} {!!} {!!} {!!}))))

  CodeCofibα (push (push a i₁) i) = {!!}
  -}


--   theIs : (t : Fin k) → ℤ/Imα .fst ≃ ℤ/Imα .fst
--   theIs t = isoToEquiv (·GroupAutomorphism ℤ/Imα [ ℤFinGenerator t ])

--   Code : SphereBouquet 1 (Fin k) → Type
--   Code (inl x) = ℤ/Imα .fst
--   Code (inr (t , base)) = ℤ/Imα .fst
--   Code (inr (t , loop i)) = ua (theIs t) i
--   Code (push a i) = ℤ/Imα .fst

--   Bah : (t : _) (x : _) (y : Code x) → fst α t ≡ x → Code x ≃ ℤ/Imα .fst
--   Bah t (inl x) y p = idEquiv _
--   Bah (inl x) (inr (s , base)) y p = substEquiv Code (sym (snd α) ∙ p ∙ sym (push s))
--   Bah (inr x) (inr (s , base)) y p = {!!}
--   Bah (push a i) (inr (s , base)) y p = {!!}
--   Bah t (inr (s , loop i)) = {!!}
--     where
--     W : (t : _) → _
--     W t = PathP (λ i → ua (theIs s) i → fst α t ≡ inr (s , loop i) → ua (theIs s) i ≃ ℤ/Imα .fst) (λ _ _ → idEquiv _) (λ _ _ → idEquiv _)

--     W∙ : W (inl tt)
--     W∙ = toPathP (funExt λ r → funExt λ o → {!!})

--     isS : (t : _) → isProp (W t)
--     isS = λ t → isOfHLevelPathP' 1 (isSetΠ2 (λ _ _ → isOfHLevel≃ 2 squash/ squash/)) _ _

--     L : (t : _) → W t
--     L = PO.elimProp _ isS (λ _ → W∙) (uncurry λ s → toPropElim (λ _ → isS _) (subst W (push s) W∙))
--   Bah t (push a i) y p = {!y!} -- idEquiv _
  
--   CodeCofib : cofib (fst α) → Type
--   CodeCofib (inl x) = ℤ/Imα .fst
--   CodeCofib (inr x) = Code x
--   CodeCofib (push (inl x) i) = {! ℤ/Imα .fst!}
--   CodeCofib (push (inr (t , y)) i) = {!y!}
--   CodeCofib (push (push a i₁) i) = {!!}

-- ΩSphere→ : {m k : ℕ}
--   (α : SphereBouquet∙ (suc zero) (Fin m)
--   →∙ SphereBouquet∙ (suc zero) (Fin k))
--   → cofib (fst α) → Type
-- ΩSphere→ α (inl x) = {!!}
-- ΩSphere→ α (inr x) = {!x -- ℤ[Fin_]!}
-- ΩSphere→ α (push a i) = {!!}

-- toCofib∙ : {n m k : ℕ}
--   (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
--   → SphereBouquet∙ (suc n) (Fin k) →∙ (cofib (fst α) , inl tt)
-- fst (toCofib∙ α) = inr
-- snd (toCofib∙ α) = (λ i → inr (snd α (~ i))) ∙ sym (push (inl tt))

-- intoCofib : (n m k : ℕ) (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
--   → (f : S₊∙ (suc n) →∙ (cofib (fst α) , inl tt))
--   → ∃[ g ∈ S₊∙ (suc n) →∙ SphereBouquet∙ (suc n) (Fin k) ]
--       f ≡ (toCofib∙ α ∘∙ g)
-- -- intoCofib n zero k α f = ∣ ((Iso.fun lem , refl) ∘∙ f)
-- --   , ΣPathP ((λ i x → Iso.leftInv lem (fst f x) (~ i))
-- --   , main _ _) ∣₁
-- --   where
-- --   lem : Iso (cofib (fst α)) (SphereBouquet (suc n) (Fin k))
-- --   Iso.fun lem (inl x) = inl tt
-- --   Iso.fun lem (inr x) = x
-- --   Iso.fun lem (push (inl x) i) = snd α (~ i)
-- --   Iso.inv lem x = inr x
-- --   Iso.rightInv lem x = refl
-- --   Iso.leftInv lem (inl x) = (λ i → inr (snd α (~ i))) ∙ sym (push (inl tt))
-- --   Iso.leftInv lem (inr x) = refl
-- --   Iso.leftInv lem (push (inl x) i) j =
-- --     compPath-filler'' (λ i → inr (snd α (~ i))) (sym (push (inl tt))) (~ i) j

-- --   main : (t : _) (sndf : _ ≡ t)
-- --     → PathP (λ i → Iso.leftInv lem t (~ i) ≡ inl tt)
-- --              (sym sndf)
-- --              ((λ i → inr (((λ i₁ → Iso.fun lem (sndf (~ i₁))) ∙ refl) i))
-- --               ∙ (λ i → inr (snd α (~ i))) ∙ (λ i → push (inl tt) (~ i)))
-- --   main = J> ((λ i j → ((λ i₁ → inr (snd α (~ i₁)))
-- --                      ∙ (sym (push (inl tt)))) (~ i ∨ j))
-- --     ▷ (lUnit _
-- --     ∙ cong₂ _∙_ (rUnit refl ∙ sym (cong-∙ inr refl refl))
-- --                 refl))
-- intoCofib n m k α f = {!!}
--   where
--   conFib : isConnected 2 (fiber (fst f) (inl tt))
--   conFib = ∣ (ptSn (suc n)) , (snd f) ∣
--          , (TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
--             (uncurry (sphereElim n (λ _ → isOfHLevelΠ (suc n)
--               λ _ → isProp→isOfHLevelSuc n (isOfHLevelTrunc 2 _ _))
--               λ y → TR.rec {!!} {!!}
--               (isConnectedPath 1
--                (isConnectedPath 2 {A = cofib (fst α)}
--                 {!!} (fst f (ptSn (suc n))) (inl tt)) (snd f) y .fst))))

--   conCofib : isConnectedFun 2 (fst f)
--   conCofib = PO.elimProp _ (λ _ → isPropIsContr)
--     (λ { tt → conFib})
--     (PO.elimProp _ (λ _ → isPropIsContr)
--       (λ { tt → subst (isConnected 2 ∘ (fiber (fst f)))
--                   (push (inl tt) ∙ (λ i → inr (snd α i))) conFib})
--       (uncurry λ k → sphereElim n (λ _ → isProp→isOfHLevelSuc n isPropIsContr)
--         (subst (isConnected 2 ∘ (fiber (fst f)))
--           ((push (inl tt) ∙ (λ i → inr (snd α i)))
--                           ∙ (λ i → inr (push k i))) conFib)))

--   conCofib' : isConnectedFun 1 (fst f)
--   conCofib' = {!!} -- PO.elimProp _ (λ _ → isPropIsContr)

--   ooh : ∥ ((k : Fin k) (x : _) → fiber (fst f) (inr x)) ∥₁
--   ooh = {!!}

--   main : ∥ ((x : S₊ (suc n)) → Σ[ s ∈ SphereBouquet (suc n) (Fin k) ]
--            (Σ[ t ∈ ((p : ptSn (suc n) ≡ x) → s ≡ inl tt) ] 
--             Σ[ h ∈ (f .fst x ≡ inr s) ]
--             (((p : ptSn (suc n) ≡ x)
--             → Square (snd f) (cong inr (t p))
--                       (cong (fst f) p ∙ h)
--                       (sym ((λ i → inr (snd α (~ i))) ∙ sym (push (inl tt)))))))) ∥₁
--   main = sphereToTrunc (suc n) λ x → PT.rec {!!}
--     (λ F → ∣ inr ({!!} , {!F!}) , {!!} ∣ₕ) ooh

--   s = inrConnected 2 (fst α) (λ _ → tt) {!approxSphereMap∙ !}
