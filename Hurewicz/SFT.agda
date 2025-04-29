{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.SFT where

open import Cubical.CW.Subcomplex
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


open import Cubical.Data.Sum as ⊎
PushoutEmptyDomainIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso (Pushout {A = ⊥} {B = A} {C = B} (λ()) (λ())) (A ⊎ B)
Iso.fun PushoutEmptyDomainIso (inl x) = inl x
Iso.fun PushoutEmptyDomainIso (inr x) = inr x
Iso.inv PushoutEmptyDomainIso (inl x) = inl x
Iso.inv PushoutEmptyDomainIso (inr x) = inr x
Iso.rightInv PushoutEmptyDomainIso (inl x) = refl
Iso.rightInv PushoutEmptyDomainIso (inr x) = refl
Iso.leftInv PushoutEmptyDomainIso (inl x) = refl
Iso.leftInv PushoutEmptyDomainIso (inr x) = refl

module _
  {ℓ' : Level} (P : Type → Type ℓ') (P1 : P Unit) (P0 : P ⊥)
  (Ppush : (A B C : Type) (f : A → B) (g : A → C)
         → P A → P B → P C → P (Pushout f g)) where

  PFin1 : P (Fin 1)
  PFin1 = subst P (isoToPath Iso-Unit-Fin1) P1

  P⊎ : {B C : Type} → P B → P C → P (B ⊎ C)
  P⊎ {B = B} {C} pB pC =
    subst P (isoToPath PushoutEmptyDomainIso)
      (Ppush ⊥ B C (λ ()) (λ ()) P0 pB pC)

  PFin : (n : ℕ) → P (Fin n)
  PFin zero =
    subst P (ua (propBiimpl→Equiv isProp⊥ (λ x → ⊥.rec (¬Fin0 x)) (λ()) ¬Fin0))
            P0
  PFin (suc n) = subst P (sym (isoToPath Iso-Fin-Unit⊎Fin)) (P⊎ P1 (PFin n))

  PS : (n : ℕ) → P (S⁻ n)
  PS zero = P0
  PS (suc zero) = subst P (isoToPath (invIso Iso-Bool-Fin2)) (PFin 2)
  PS (suc (suc n)) =
    subst P (isoToPath (compIso PushoutSuspIsoSusp (invIso (IsoSucSphereSusp n))))
      (Ppush (S₊ n) Unit Unit _ _ (PS (suc n)) P1 P1)


  PFin×S : (n m : ℕ) → P (Fin n × S⁻ m)
  PFin×S zero m = subst P (ua (uninhabEquiv (λ()) (λ x → ¬Fin0 (fst x)))) P0
  PFin×S (suc n) m =
    subst P (isoToPath (compIso (compIso (⊎Iso (invIso rUnit×Iso) Σ-swap-Iso)
                       (compIso (invIso ×DistR⊎Iso) Σ-swap-Iso))
                       (Σ-cong-iso-fst (invIso Iso-Fin-Unit⊎Fin))))
            (P⊎ (PS m) (PFin×S n m))

  PCWskel : (B : CWskel ℓ-zero) → (n : ℕ) → P (fst B n)
  PCWskel B zero = subst P (ua (uninhabEquiv (λ()) (CW₀-empty B))) P0
  PCWskel B (suc n) =
    subst P (ua (invEquiv (B .snd .snd .snd .snd n)))
            (Ppush _ _ _ _ _ (PFin×S _ _) (PCWskel B n) (PFin _))

  PisFinCW : (B : Type) → isFinCW B → P B
  PisFinCW B fCWB =
    subst P (ua (compEquiv (isoToEquiv (realiseFin _ (fCWB .snd .fst)))
            (invEquiv (fCWB .snd .snd))))
            (PCWskel (finCWskel→CWskel _ (fCWB .snd .fst)) (fCWB .fst))

  PfinCW : (B : finCW ℓ-zero) → isProp (P (fst B)) → P (fst B)
  PfinCW (B , Bstr) isp = PT.rec isp (PisFinCW B) Bstr




postulate
  isPushoutᶠⁱⁿᶜʷ : ∀ {ℓ} (B C D : finCW ℓ)
    (f : finCW→CW B →ᶜʷ finCW→CW C) (g : finCW→CW B →ᶜʷ finCW→CW D)
     → ∥ isFinCW (Pushout f g) ∥₁


open import Cubical.HITs.Pushout.Flattening
open import Cubical.Foundations.Transport

module _ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (f : A → B) (g : A → C) (X : Pushout f g → Type ℓ''') where

  open FlatteningLemma f g (X ∘ inl) (X ∘ inr) (λ a → substEquiv X (push a))

  PushoutΣL : Σ[ a ∈ A ] X (inl (f a)) → Σ[ b ∈ B ] X (inl b)
  PushoutΣL (a , x) = f a , x

  PushoutΣR : Σ[ a ∈ A ] X (inl (f a)) → Σ[ c ∈ C ] X (inr c)
  PushoutΣR (a , x) = g a , subst X (push a) x

  PushoutΣ : Type _
  PushoutΣ = Pushout PushoutΣL PushoutΣR


  repairLeft : (a : Pushout f g) → X a ≃ E a
  repairLeft (inl x) = idEquiv _
  repairLeft (inr x) = idEquiv _
  repairLeft (push a i) = help i
    where
    help : PathP (λ i → X (push a i) ≃ E (push a i)) (idEquiv _) (idEquiv _) 
    help = ΣPathPProp (λ _ → isPropIsEquiv _)
      (toPathP (funExt λ x → transportRefl _ ∙ substSubst⁻ X (push a) x))

  ΣPushout≃PushoutΣ : Σ _ X ≃ PushoutΣ
  ΣPushout≃PushoutΣ =
    compEquiv (Σ-cong-equiv-snd repairLeft) flatten

-- todo move
CWskelUnit* : ∀ {ℓ} → CWskel ℓ
fst CWskelUnit* zero = ⊥*
fst CWskelUnit* (suc n) = Unit*
fst (snd CWskelUnit*) zero = 1
fst (snd CWskelUnit*) (suc x) = 0
fst (snd (snd CWskelUnit*)) zero ()
fst (snd (snd CWskelUnit*)) (suc n) _ = tt*
snd (snd (snd (snd CWskelUnit*))) zero =
    compEquiv (compEquiv (compEquiv (invEquiv LiftEquiv)
    (isoToEquiv Iso-Unit-Fin1))
      (isoToEquiv (PushoutEmptyFam (λ()) λ()))) (symPushout _ _)
snd (snd (snd (snd CWskelUnit*))) (suc n) =
  isoToEquiv (PushoutEmptyFam (λ()) λ())

open import Cubical.Data.Sequence.Base
convergesCWskelUnit* : ∀ {ℓ} → converges (realiseSeq (CWskelUnit* {ℓ})) 1
convergesCWskelUnit* zero = idIsEquiv _
convergesCWskelUnit* (suc k) = idIsEquiv _

isFinCWUnit* : ∀ {ℓ} → isFinCW (Unit* {ℓ})
fst isFinCWUnit* = 1
fst (fst (snd isFinCWUnit*)) = CWskelUnit* .fst
fst (snd (fst (snd isFinCWUnit*))) = CWskelUnit* .snd
snd (snd (fst (snd isFinCWUnit*))) = convergesCWskelUnit*
fst (snd (snd isFinCWUnit*)) = _
snd (snd (snd isFinCWUnit*)) = converges→isEquivIncl {seq = realiseSeq CWskelUnit*} 1
  convergesCWskelUnit*

finCWUnit* : (ℓ : Level) → finCW ℓ
fst (finCWUnit* ℓ) = Unit*
snd (finCWUnit* ℓ) = ∣ isFinCWUnit* ∣₁

finCWUnit : finCW ℓ-zero
fst finCWUnit = Unit
snd finCWUnit = subst (∥_∥₁ ∘ isFinCW) (sym (ua Unit≃Unit*)) ∣ isFinCWUnit* ∣₁

isFinCW⊥ : isFinCW ⊥
fst isFinCW⊥ = 0
fst (fst (snd isFinCW⊥)) _ = ⊥
fst (fst (snd (fst (snd isFinCW⊥)))) _ = 0
fst (snd (fst (snd (fst (snd isFinCW⊥))))) _ (x , _) = ¬Fin0 x
snd (snd (snd (fst (snd (fst (snd isFinCW⊥)))))) n =
  uninhabEquiv (λ()) (Iso.inv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0))
equiv-proof (snd (snd (fst (snd isFinCW⊥))) k) ()
snd (snd isFinCW⊥) =
  uninhabEquiv (λ()) (SeqColim→Prop (λ _ → isProp⊥) λ x w → w)



isFinCWΣ : (A : finCW ℓ-zero) (B : fst A → finCW ℓ-zero)
  → ∥ isFinCW (Σ (fst A) (fst ∘ B)) ∥₁ 
isFinCWΣ A = PfinCW (λ A → (B : A → finCW ℓ-zero) → ∥ isFinCW (Σ A (fst ∘ B)) ∥₁)
  (λ B → PT.map (λ sndB → subst isFinCW (sym (ua (ΣUnit (fst ∘ B)))) sndB) (snd (B tt)))
  (λ _ → ∣ subst isFinCW (ua (invEquiv (ΣEmpty _))) isFinCW⊥ ∣₁)
  (λ A0 A1 A2 f g p q r B
    → subst (λ T → ∥ isFinCW T ∥₁)
             (ua (invEquiv (ΣPushout≃PushoutΣ f g (fst ∘ B))))
             (isPushoutᶠⁱⁿᶜʷ (_ , p (λ x → B (inl (f x)))) (_ , q λ x → B (inl x)) (_ , r λ a → B (inr a)) _ _))
  A
  (isPropΠ λ _ → squash₁)

isFinCW× : (A B : finCW ℓ-zero) → ∥ isFinCW (fst A × fst B) ∥₁ 
isFinCW× A B = isFinCWΣ A (λ _ → B)

open import Cubical.HITs.Join
isFinCWJoinPushout : (A B : finCW ℓ-zero) → ∥ isFinCW (joinPushout (fst A) (fst B)) ∥₁ 
isFinCWJoinPushout A B = isPushoutᶠⁱⁿᶜʷ (_ , (isFinCW× A B)) A B fst snd

isFinCWJoin : (A B : finCW ℓ-zero) → ∥ isFinCW (join (fst A) (fst B)) ∥₁ 
isFinCWJoin A B =
  subst (∥_∥₁ ∘ isFinCW) (joinPushout≡join (fst A) (fst B)) (isFinCWJoinPushout A B)

---Suspension
Susp^ : ℕ → Type ℓ → Type ℓ
Susp^ 0 X = X
Susp^ (suc n) X = Susp^ n (Susp X)

Susp^' : ℕ → Type ℓ → Type ℓ
Susp^' zero x = x
Susp^' (suc n) x = Susp (Susp^' n x)

Susp^'≡Susp^ : (n : ℕ) {A : Type ℓ} → Susp^' n A ≡ Susp^ n A  
Susp^'≡Susp^ zero {A = A} = refl
Susp^'≡Susp^ (suc n) {A = A} = lem n ∙ Susp^'≡Susp^ n {A = Susp A}
  where
  lem : (n : ℕ) → Susp (Susp^' n A) ≡ Susp^' n (Susp A)
  lem zero = refl
  lem (suc n) = cong Susp (lem n)


isFinCWSusp : (A : finCW ℓ-zero) → ∥ isFinCW (Susp (fst A)) ∥₁ 
isFinCWSusp A =
  subst (∥_∥₁ ∘ isFinCW) PushoutSusp≡Susp
    (isPushoutᶠⁱⁿᶜʷ A finCWUnit finCWUnit _ _)

isFinCWSusp^' : (A : finCW ℓ-zero) (n : ℕ) → ∥ isFinCW (Susp^' n (fst A)) ∥₁ 
isFinCWSusp^' A zero = snd A
isFinCWSusp^' A (suc n) = isFinCWSusp (_ , isFinCWSusp^' A n)

isFinCWSusp^ : (A : finCW ℓ-zero) (n : ℕ) → ∥ isFinCW (Susp^ n (fst A)) ∥₁ 
isFinCWSusp^ A n = subst (∥_∥₁ ∘ isFinCW) (Susp^'≡Susp^ n) (isFinCWSusp^' A n)

open import Cubical.CW.Subcomplex
hasNDimFinCW : ℕ → Type ℓ → Type (ℓ-suc ℓ)
hasNDimFinCW {ℓ = ℓ} n X = Σ[ X' ∈ finCWskel ℓ n ] X ≃ realise (finCWskel→CWskel n X')

isNDimFinCW : ℕ → Type ℓ → Type (ℓ-suc ℓ)
isNDimFinCW n X = ∥ hasNDimFinCW n X ∥₁

mapFromNSkel : (X : Type ℓ) (hX : ∥ isFinCW X ∥₁) (n : ℕ)
  → ∃[ Y ∈ Type ℓ ] Σ[ hY ∈ isNDimFinCW n Y ] Σ[ f ∈ (Y → X) ] isConnectedFun n f
mapFromNSkel X = PT.rec (isPropΠ (λ _ → squash₁))
  λ {(dim , Xstr) → λ n
    → ∣ Xstr .fst .fst n
     , ∣ ((subComplex (finCWskel→CWskel dim (Xstr .fst)) n .fst)
       , ((subComplex (finCWskel→CWskel dim (Xstr .fst)) n .snd)
       , (subComplexYieldsFinCWskel (finCWskel→CWskel dim (Xstr .fst)) n .snd)))
       , (isoToEquiv (realiseSubComplex n (Xstr .fst .fst , Xstr .fst .snd .fst))) ∣₁
     , subst (λ X → Σ (Xstr .fst .fst n → X) (isConnectedFun n))
             (ua (invEquiv (Xstr .snd)))
             ((CW↪∞ ((Xstr .fst .fst) , (Xstr .fst .snd .fst)) n)
             , (isConnected-CW↪∞ n ((Xstr .fst .fst) , (Xstr .fst .snd .fst)))) ∣₁}
