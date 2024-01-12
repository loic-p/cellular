{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function

open import Cubical.Data.Bool hiding (_≤_ ;  _≟_ ; isProp≤)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetTruncation as ST

open import Cubical.Homotopy.Loopspace

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Properties

open import prelude
open import freeabgroup
open import degree

module spherebouquet where

-- Move
suspFun∙ : {A B : Type} (f : A → B)
       → Susp∙ A →∙ Susp∙ B
fst (suspFun∙ f) = suspFun f
snd (suspFun∙ f) = refl

--a sphere bouquet is the wedge sum of A n-dimensional spheres
SphereBouquet : (n : ℕ) (A : Type) → Type
SphereBouquet n A = Pushout (terminal A) ((λ a → (a , ptSn n)))

SphereBouquet→Prop : ∀ {ℓ} (n : ℕ) {A : Type} (a : A)
  → {B : SphereBouquet n A → Type ℓ}
  → ((b : _) → isProp (B b))
  → ((x : _) (y : _) → B (inr (x , y)))
  → (s : _) → B s
SphereBouquet→Prop n a {B = B} pr d =
  elimProp _ pr (λ t → subst B (sym (push a)) (d a _)) λ {(x , y) → d x y}

Bouquet : (A : Type) (B : A → Pointed₀) → Type
Bouquet A B = Pushout (terminal A) (λ a → a , pt (B a))

isContrSphereBouquetZero : (n : ℕ) → isContr (SphereBouquet n (Fin zero))
fst (isContrSphereBouquetZero n) = inl tt
snd (isContrSphereBouquetZero n) (inl x) = refl
snd (isContrSphereBouquetZero n) (inr x) = ⊥.rec (¬Fin0 (fst x))
snd (isContrSphereBouquetZero n) (push a i) j =
  ⊥.rec {A = Square {A = SphereBouquet n (Fin zero)}
        (λ _ → inl tt) (push a) (λ _ → inl tt)
        (⊥.rec (¬Fin0 a))} (¬Fin0 a) j i

isConnectedSphereBouquet : {n : ℕ} {A : Type} (x : SphereBouquet (suc n) A) → ∥ x ≡ inl tt ∥₁
isConnectedSphereBouquet {n} {A} = elimProp (λ x → ∥ x ≡ inl tt ∥₁) (λ x → squash₁) (λ x → ∣ refl ∣₁)
  (λ (a , s) → sphereToPropElim n {A = λ x → ∥ inr (a , x) ≡ inl tt ∥₁}
                                  (λ x → squash₁) ∣ sym (push a) ∣₁ s)

Bouquet→ΩBouquetSusp-filler : (A : Type) (B : A → Pointed₀)
  → (a : _) → (i j k : I) → Bouquet A (λ a → Susp∙ (fst (B a)))
Bouquet→ΩBouquetSusp-filler A B a i j k =
  hfill (λ k → λ {(i = i0) → inl tt
                 ; (i = i1) → doubleCompPath-filler
                                (push a)
                                (λ i → inr (a
                                      , rCancel' (merid (snd (B a))) (~ k) i))
                                (sym (push a)) k j
                 ; (j = i0) → push a (~ k ∧ i)
                 ; (j = i1) → push a (~ k ∧ i)})
        (inS (push a i))
        k

Bouquet→ΩBouquetSusp : (A : Type) (B : A → Pointed₀)
  → Bouquet A B
  → Ω (Bouquet A (λ a → Susp∙ (fst (B a))) , inl tt) .fst
Bouquet→ΩBouquetSusp A B (inl x) = refl
Bouquet→ΩBouquetSusp A B (inr (a , b)) =
  (push a ∙∙ (λ i → inr (a , toSusp (B a) b i)) ∙∙ sym (push a))
Bouquet→ΩBouquetSusp A B (push a i) j = Bouquet→ΩBouquetSusp-filler A B a i j i1

SuspBouquet→Bouquet : (A : Type) (B : A → Pointed₀)
  → Susp (Bouquet A B) → Bouquet A (λ a → Susp∙ (fst (B a)))
SuspBouquet→Bouquet A B north = inl tt
SuspBouquet→Bouquet A B south = inl tt
SuspBouquet→Bouquet A B (merid a i) = Bouquet→ΩBouquetSusp A B a i

Bouquet→SuspBouquet : (A : Type) (B : A → Pointed₀)
  → Bouquet A (λ a → Susp∙ (fst (B a))) → Susp (Bouquet A B)
Bouquet→SuspBouquet A B (inl x) = north
Bouquet→SuspBouquet A B (inr (a , north)) = north
Bouquet→SuspBouquet A B (inr (a , south)) = south
Bouquet→SuspBouquet A B (inr (a , merid b i)) = merid (inr (a , b)) i
Bouquet→SuspBouquet A B (push a i) = north

SuspBouquet-Bouquet-cancel : (A : Type) (B : A → Pointed₀)
    → section (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
     × retract (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
SuspBouquet-Bouquet-cancel A B = sec , ret
  where
    sec : section (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
    sec (inl tt) i = inl tt
    sec (inr (a , north)) = push a
    sec (inr (a , south)) =
         (push a)
      ∙∙ (λ i → inr (a , merid (pt (B a)) i))
      ∙∙ (λ i → inr (a , south))
    sec (inr (a , merid b j)) i =
      hcomp (λ k → λ {(~ i ∧ j = i1) → push a (~ k)
                     ; (i = i1) → inr (a , merid b j)
                     ; (j = i0) → push a (i ∨ (~ k)) })
            (inr (a , (hcomp (λ k → λ {(i = i1) → merid b j
                            ; (j = i0) → north
                            ; (j = i1) → merid (pt (B a)) (i ∨ (~ k))})
                   (merid b j))))
    sec (push a j) i = push a (i ∧ j)

    module _ (a : A) (b : fst (B a)) (i j : I) where
      ret-fill₁ : I →  Susp (Bouquet A B)
      ret-fill₁ k =
        hfill (λ k → λ {(j = i0) → north
                       ; (j = i1) → merid (inr (a , pt (B a))) ((~ k) ∨ i)
                       ; (i = i0) → Bouquet→SuspBouquet A B
                                      (inr (a , compPath-filler (merid b)
                                                 (sym (merid (pt (B a)))) k j))
                       ; (i = i1) → merid (inr (a , b)) j})
              (inS (merid (inr (a , b)) j)) k

      ret-fill₂ : I → Susp (Bouquet A B)
      ret-fill₂ k =
        hfill (λ k → λ {(j = i0) → north
                     ; (j = i1) → merid (push a (~ k)) i
                     ; (i = i0) → Bouquet→SuspBouquet A B
                                    (doubleCompPath-filler (push a)
                                     (λ i → inr (a , toSusp (B a) b i))
                                     (sym (push a)) k j)
                     ; (i = i1) → merid (inr (a , b)) j})
               (inS (ret-fill₁ i1)) k

    ret : retract (SuspBouquet→Bouquet A B) (Bouquet→SuspBouquet A B)
    ret north i = north
    ret south = merid (inl tt)
    ret (merid (inl tt) j) i = merid (inl tt) (i ∧ j)
    ret (merid (inr (a , b)) j) i = ret-fill₂ a b i j i1
    ret (merid (push a k) j) i =
      hcomp (λ r → λ {(i = i0) → Bouquet→SuspBouquet A B
                                   (Bouquet→ΩBouquetSusp-filler A B a k j r)
                     ; (i = i1) → merid (push a (~ r ∨ k)) j
                     ; (j = i0) → north
                     ; (j = i1) → merid (push a (~ r)) i
                     ; (k = i0) → merid (push a (~ r)) (i ∧ j)
                     ; (k = i1) → side r i j}
                     )
            (merid (inr (a , pt (B a))) (i ∧ j))
         where
         side : Cube {A = Susp (Bouquet A B)}
                   (λ i j → merid (inr (a , pt (B a))) (i ∧ j))
                   (λ i j → ret-fill₂ a (pt (B a)) i j i1)
                   (λ r j → Bouquet→SuspBouquet A B
                              (Bouquet→ΩBouquetSusp-filler A B a i1 j r))
                   (λ r j → merid (inr (a , (pt (B a)))) j)
                   (λ r i → north)
                   λ r i → merid (push a (~ r)) i
         side r i j =
           hcomp (λ k
             → λ {(r = i0) → Bouquet→SuspBouquet A B
                                (inr (a , rCancel-filler'
                                           (merid (pt (B a))) i k j))
                 ; (r = i1) →  ret-fill₂ a (pt (B a)) i j k
                 ; (i = i0) → Bouquet→SuspBouquet A B
                                (doubleCompPath-filler
                                  (push a)
                                  (λ j → inr (a
                                    , rCancel' (merid (pt (B a))) (~ r ∧ k) j))
                                  (sym (push a)) (r ∧ k) j)
                 ; (i = i1) → merid (inr (a , snd (B a))) j
                 ; (j = i0) → north
                 ; (j = i1) → merid (push a (~ r ∨ ~ k)) i})
             (hcomp (λ k
               → λ {(r = i0) → Bouquet→SuspBouquet A B
                                  (inr (a , rCancel-filler'
                                             (merid (pt (B a))) (~ k ∨ i) i0 j))
                   ; (r = i1) → ret-fill₁ a (pt (B a)) i j k
                   ; (i = i0) → Bouquet→SuspBouquet A B
                                  (inr (a , compPath-filler
                                             (merid (pt (B a)))
                                             (sym (merid (pt (B a)))) k j))
                   ; (i = i1) → merid (inr (a , snd (B a))) j
                   ; (j = i0) → north
                   ; (j = i1) →  merid (inr (a , snd (B a))) (~ k ∨ i)})
                   (merid (inr (a , snd (B a))) j))

Iso-SuspBouquet-Bouquet : (A : Type) (B : A → Pointed₀)
  → Iso (Susp (Bouquet A B)) (Bouquet A (λ a → Susp∙ (fst (B a))))
Iso.fun (Iso-SuspBouquet-Bouquet A B) = SuspBouquet→Bouquet A B
Iso.inv (Iso-SuspBouquet-Bouquet A B) = Bouquet→SuspBouquet A B
Iso.rightInv (Iso-SuspBouquet-Bouquet A B) = SuspBouquet-Bouquet-cancel A B .fst
Iso.leftInv (Iso-SuspBouquet-Bouquet A B) = SuspBouquet-Bouquet-cancel A B .snd

SuspBouquet≃Bouquet : (A : Type) (B : A → Pointed₀)
  → Susp (Bouquet A B) ≃ Bouquet A (λ a → Susp∙ (fst (B a)))
SuspBouquet≃Bouquet A B = isoToEquiv (Iso-SuspBouquet-Bouquet A B)
open import Cubical.Data.Sigma

sphereBouquetSuspIso₀ : {A : Type}
  → Iso (Bouquet A (λ a → Susp∙ (fst (S₊∙ zero))))
      (SphereBouquet 1 A)
Iso.fun sphereBouquetSuspIso₀ (inl x) = inl x
Iso.fun sphereBouquetSuspIso₀ (inr (a , b)) =
  inr (a , Iso.inv (IsoSucSphereSusp 0) b)
Iso.fun sphereBouquetSuspIso₀ (push a i) = push a i
Iso.inv sphereBouquetSuspIso₀ (inl x) = inl x
Iso.inv sphereBouquetSuspIso₀ (inr (a , b)) =
  inr (a , Iso.fun (IsoSucSphereSusp 0) b)
Iso.inv sphereBouquetSuspIso₀ (push a i) = push a i
Iso.rightInv sphereBouquetSuspIso₀ (inl x) = refl
Iso.rightInv sphereBouquetSuspIso₀ (inr (a , y)) i =
  inr (a , Iso.leftInv (IsoSucSphereSusp 0) y i)
Iso.rightInv sphereBouquetSuspIso₀ (push a i) = refl
Iso.leftInv sphereBouquetSuspIso₀ (inl x) = refl
Iso.leftInv sphereBouquetSuspIso₀ (inr (a , y)) i =
  inr (a , Iso.rightInv (IsoSucSphereSusp 0) y i)
Iso.leftInv sphereBouquetSuspIso₀ (push a i) = refl

sphereBouquetSuspIso : {A : Type} {n : ℕ}
  → Iso (Susp (SphereBouquet n A)) (SphereBouquet (suc n) A)
sphereBouquetSuspIso {A = A} {n = zero} =
  compIso (Iso-SuspBouquet-Bouquet A λ _ → S₊∙ zero) sphereBouquetSuspIso₀
sphereBouquetSuspIso {A = A} {n = suc n} = Iso-SuspBouquet-Bouquet A λ _ → S₊∙ (suc n)

sphereBouquet≃Susp : {A : Type} {n : ℕ}
  → Susp (SphereBouquet n A) ≃ SphereBouquet (suc n) A
sphereBouquet≃Susp = isoToEquiv (sphereBouquetSuspIso)

sphereBouquetSuspFun : {A : Type} {n : ℕ}
  → Susp (SphereBouquet n A) → SphereBouquet (suc n) A
sphereBouquetSuspFun {A = A} {n = n} = sphereBouquetSuspIso .Iso.fun

sphereBouquetSuspInvFun : {A : Type} {n : ℕ}
  → SphereBouquet (suc n) A → Susp (SphereBouquet n A)
sphereBouquetSuspInvFun {A = A} {n = n} = sphereBouquetSuspIso .Iso.inv

-- No need to check the push-case when considering maps from bouquets into
-- Eilenberg-MacLane spaces
Bouquet→KnEq : {A : Type} {B : A → Pointed₀} (m : ℕ)
     (f g : (Pushout (terminal A) ((λ a → a , B a .snd)) , inl tt)
         →∙ coHomK-ptd m)
  → ((x : _) → fst f (inr x) ≡ fst g (inr x))
  → (x : _) → f .fst x ≡ g .fst x
Bouquet→KnEq {A = A} {B = B} m f g idd (inl x) = snd f ∙ sym (snd g)
Bouquet→KnEq {A = A} {B = B} m f g idd (inr (a , x)) =
  (sym (rUnitₖ m (f .fst (inr (a , x))))
    ∙∙ cong (λ z → f .fst (inr (a , x)) +[ m ]ₖ z)
         (sym (snd g)
         ∙∙ (cong (fst g) (push a)
         ∙∙ sym (idd _)
         ∙∙ cong (fst f) (sym (push a)))
         ∙∙ snd f)
    ∙∙ rUnitₖ m (f .fst (inr (a , x))))
    ∙ idd (a , x)
Bouquet→KnEq {A = A} {B = B} m f g idd (push x i) =
  lem _ (sym (snd f)) _ (cong (fst f) (push x))
    _ (sym (snd g)) _ (cong (fst g) (push x))
    (idd (x , snd (B x))) i
  where
  lem : (f' : coHomK m) (f∙ : 0ₖ m ≡ f')
        (fx : coHomK m) (f-p : f' ≡ fx)
        (g' : coHomK m) (g∙ : 0ₖ m ≡ g')
        (gx : coHomK m) (g-p : g' ≡ gx)
        (idd1 : fx ≡ gx)
    → PathP (λ i → f-p i ≡ g-p i)
        (sym f∙ ∙ g∙)
        ((sym (rUnitₖ m fx)
           ∙∙ cong (λ z → fx +[ m ]ₖ z)
                   (g∙ ∙∙ g-p ∙∙ sym idd1 ∙∙ sym f-p ∙∙ sym f∙)
           ∙∙ rUnitₖ m fx)
        ∙ idd1)
  lem = J> (J> (J> (J>  λ p → sym (rUnit refl) ◁ sym (help m p))))
    where
    help : (m : ℕ) (p : _)
      → (sym (rUnitₖ m (0ₖ m))
      ∙∙ cong (+ₖ-syntax m (0ₖ m))
              ((sym p ∙ refl) ∙ refl)
      ∙∙ rUnitₖ m (0ₖ m))
       ∙ p
      ≡ refl
    help zero p = isSetℤ _ _ _ _
    help (suc zero) p =
      cong (_∙ p) (sym (rUnit _)
          ∙ λ i j → lUnitₖ 1 (rUnit (rUnit (sym p) (~ i)) (~ i) j) i)
          ∙ lCancel p
    help (suc (suc m)) p =
      cong (_∙ p) (sym (rUnit _)
          ∙ λ i j → lUnitₖ (2 +ℕ m) (rUnit (rUnit (sym p) (~ i)) (~ i) j) i)
      ∙ lCancel p

Bouquet→∙KnEq : {A : Type} {B : A → Pointed₀} (m : ℕ)
     (f g : (Pushout (terminal A) ((λ a → a , B a .snd)) , inl tt)
         →∙ coHomK-ptd m)
  → ((x : _) → fst f (inr x) ≡ fst g (inr x))
  → f ≡ g
Bouquet→∙KnEq m f g hom =
  ΣPathP ((funExt (Bouquet→KnEq m f g hom))
       , (flipSquare ((λ i → (λ j → snd f (i ∧ j))
                           ∙∙ (λ j → snd f (i ∨ j))
                           ∙∙ sym (snd g))
                  ◁ λ i → doubleCompPath-filler (snd f) refl (sym (snd g)) (~ i))))

--the suspension of a n-dimensional bouquet is a (n+1)-dimensional bouquet
--here is the action of suspension on morphisms
bouquetSusp→ : {n : ℕ} {A B : Type}
  → (SphereBouquet n A → SphereBouquet n B)
  → (SphereBouquet (suc n) A → SphereBouquet (suc n) B)
bouquetSusp→ {n = n} {A} {B} f =
     sphereBouquetSuspFun ∘ (suspFun f) ∘ sphereBouquetSuspInvFun

bouquetSusp→∘ : {n : ℕ} {A B C : Type}
  → (f : SphereBouquet n A → SphereBouquet n B)
  → (g : SphereBouquet n B → SphereBouquet n C)
  → bouquetSusp→ g ∘ bouquetSusp→ f ≡ bouquetSusp→ (g ∘ f)
bouquetSusp→∘ f g i =
  sphereBouquetSuspFun
          ∘ ((λ i → suspFun g ∘ (λ x → Iso.leftInv sphereBouquetSuspIso x i) ∘ suspFun f)
           ∙ sym (suspFun-comp g f)) i
          ∘ sphereBouquetSuspInvFun

-- probably not needed
-- private
--   bouquetSusp→' : {n : ℕ} {A B : Type}
--     → (SphereBouquet n A →∙ SphereBouquet n B)
--     → (SphereBouquet (suc n) A →∙ SphereBouquet (suc n) B)
--   fst (bouquetSusp→' {n} f) = sphereBouquetSuspFun ∘ suspFun (fst f) ∘ Iso.inv sphereBouquetSuspIso
--   snd (bouquetSusp→' {zero} f) = refl
--   snd (bouquetSusp→' {suc n} f) = refl

--   bouquetSusp→≡ : {n : ℕ} {A B : Type} (f : SphereBouquet n A →∙ SphereBouquet n B)
--     → bouquetSusp→ f ≡ bouquetSusp→' f
--   bouquetSusp→≡ {n = n} f = {!!}

chooseS : {n k : ℕ} (b : Fin k)
  → (SphereBouquet n (Fin k)) → S₊ n
chooseS {n = n} b (inl x) = ptSn n
chooseS {n = n} b (inr (b' , x)) with (fst b ≟ fst b')
... | lt x₁ = ptSn n
... | eq x₁ = x
... | gt x₁ = ptSn n
chooseS {n = n} {k = k} b (push b' i) with (fst b ≟ fst b')
... | lt x = ptSn n
... | eq x = ptSn n
... | gt x = ptSn n

--a morphisms between bouquets gives a morphisms of free abelian groups by taking degrees
bouquetDegree : {n m k : ℕ}
  → (SphereBouquet n (Fin m) → SphereBouquet n (Fin k))
  → (AbGroupHom (FreeAbGroup (Fin m)) (FreeAbGroup (Fin k)))
fst (bouquetDegree {m = m} {k = k} f) r x =
  sumFin λ (a : Fin m) → r a ·ℤ (degree _ (chooseS x ∘ f ∘ inr ∘ (a ,_)))
snd (bouquetDegree {n = n} f) =
  makeIsGroupHom λ x y
    → funExt λ a'
      → (λ j → sumFin (λ a
                → ·DistL+ (x a) (y a)
                     (degree _ (chooseS a' ∘ f ∘ inr ∘ (a ,_))) j))
      ∙ sumFin-hom (λ a → x a ·ℤ (degree _ (chooseS a' ∘ f ∘ inr ∘ (a ,_))))
                    λ a → y a ·ℤ (degree _ (chooseS a' ∘ f ∘ inr ∘ (a ,_)))

--degree is compatible with composition
EqHoms : ∀ {n m : ℕ}
  → {ϕ ψ : AbGroupHom (FreeAbGroup (Fin n)) (FreeAbGroup (Fin m))}
  → ((x : _) → fst ϕ (generator x) ≡ fst ψ (generator x))
  → ϕ ≡ ψ
EqHoms {n} {m} {ϕ} {ψ} idr =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
   (funExt
    (elimPropℤ[Fin] _ _ (λ _ → isOfHLevelPath' 1 (isSetΠ (λ _ → isSetℤ)) _ _)
      (IsGroupHom.pres1 (snd ϕ) ∙ sym (IsGroupHom.pres1 (snd ψ)))
      idr
      (λ f g p q → IsGroupHom.pres· (snd ϕ) f g
                 ∙∙ (λ i x → p i x + q i x)
                 ∙∙ sym (IsGroupHom.pres· (snd ψ) f g ))
      λ f p → IsGroupHom.presinv (snd ϕ) f
           ∙∙ (λ i x → -ℤ (p i x))
           ∙∙ sym (IsGroupHom.presinv (snd ψ) f)))

bouquetDegreeId : {n m : ℕ} → bouquetDegree (idfun (SphereBouquet n (Fin m))) ≡ idGroupHom
bouquetDegreeId {n = n} {m = m} =
  EqHoms λ (x : Fin m)
    → funExt λ t
      → sym (generator-is-generator' (λ w → degree n (λ x₁ → chooseS t (inr (w , x₁)))) x)
      ∙ help x t
  where
  help :  (x t : Fin m) → degree n (λ x₁ → chooseS t (inr (x , x₁))) ≡ generator x t
  help x y with (fst x ≟ fst y)
  ... | lt p = cong (degree n) (funExt lem) ∙ degree-const n
    where
    lem : (x₁ : S₊ n) → chooseS y (inr (x , x₁)) ≡ ptSn n
    lem x₁ with (fst y ≟ fst x)
    ... | lt x = refl
    ... | eq q = ⊥.rec (¬m<m (subst (fst x <_) q p))
    ... | gt x = refl
  ... | eq p = cong (degree n) (funExt lem) ∙ degree-idfun n
    where
    lem : (x₁ : S₊ n) → chooseS y (inr (x , x₁)) ≡ x₁
    lem x₁ with (fst y ≟ fst x)
    ... | lt q = ⊥.rec (¬m<m (subst (fst y <_) p q))
    ... | eq x = refl
    ... | gt q = ⊥.rec (¬m<m (subst (_< fst y) p q))
  ... | gt p = cong (degree n) (funExt lem) ∙ degree-const n
      where
    lem : (x₁ : S₊ n) → chooseS y (inr (x , x₁)) ≡ ptSn n
    lem x₁ with (fst y ≟ fst x)
    ... | lt x = refl
    ... | eq q = ⊥.rec (¬m<m (subst (_< fst x) q p))
    ... | gt x = refl

degreeComp∙ : {n m k l : ℕ}
  → (f : (SphereBouquet (suc n) (Fin m) , inl tt) →∙ (SphereBouquet (suc n) (Fin k) , inl tt))
  → (g : (SphereBouquet (suc n) (Fin l) , inl tt) →∙ (SphereBouquet (suc n) (Fin m) , inl tt))
  → bouquetDegree ((fst f) ∘ (fst g)) ≡ compGroupHom (bouquetDegree (fst g)) (bouquetDegree (fst f))
degreeComp∙ {n} {m} {k} {l} f g =
  EqHoms
    λ (x : Fin l)
    → funExt λ t
      → sumFinId l
         (λ a →
           ·Comm (generator x a) _
      ∙ cong (degree (suc n) (λ x₁ → chooseS t (fst f (fst g (inr (a , x₁))))) ·ℤ_)
             (generator-comm x a))
      ∙ sym (generator-is-generator
          (λ a → degree (suc n) (λ x₁ → chooseS t (fst f (fst g (inr (a , x₁)))))) x)
      ∙ main n m (λ s → fst g (inr (x , s)))
                 ((λ s → chooseS t (fst f s))
                 , (cong (chooseS t) (snd f)))
      ∙ sumFinId m λ a →
          degree-comp' (suc n)
              (λ x₁ → chooseS t (fst f (inr (a , x₁))))
              (λ x₁ → chooseS a (fst g (inr (x , x₁))))
         ∙ λ j → simplify x a (~ j)
              ·ℤ degree (suc n) (λ x₁ → chooseS t (fst f (inr (a , x₁))))
  where
  main : (n m : ℕ) (w : S₊ (suc n) → SphereBouquet (suc n) (Fin m))
       (F : ((SphereBouquet (suc n) (Fin m)) , inl tt) →∙ S₊∙ (suc n))
       → degree (suc n) (λ s → fst F (w s))
        ≡ sumFin λ a → degree (suc n) (λ s → fst F (inr (a , chooseS a (w s))))
  main n zero w (F , Fp) =
      (λ j → degree (suc n) (λ s → F (lem w j s)))
    ∙ (λ j → degree (suc n) (λ s → Fp j))
    ∙ degree-const (suc n)
    where
    lem : (f : S₊ (suc n) → SphereBouquet (suc n) (Fin zero)) → (f ≡ λ _ → inl tt)
    lem f = funExt λ x → sym (isContrSphereBouquetZero (suc n) .snd (f x))
  main n (suc m) w F =
    cong (Iso.fun (Hⁿ-Sⁿ≅ℤ n .fst))
      (cong ∣_∣₂ (funExt (λ x → asSum F (w x)))
            ∙ sym (sumFinK-comm
                (λ a s → ∣ fst F (inr (a , chooseS a (w s))) ∣ₕ)))
    ∙ sym (sumFinG-comm _ (Hⁿ-Sⁿ≅ℤ n)
            (λ a → ∣ (λ s → ∣ fst F (inr (a , chooseS a (w s))) ∣ₕ) ∣₂))
    where
    asSum : (F : (SphereBouquet (suc n) (Fin (suc m)) , inl tt) →∙ S₊∙ (suc n))
         → (p : SphereBouquet (suc n) (Fin (suc m)))
         → ∣ F .fst p ∣ₕ ≡ sumFinK {m = suc n} (λ i → ∣ fst F (inr (i , chooseS i p)) ∣ₕ)
    asSum F =
      Bouquet→KnEq (suc n)
       ((λ p → ∣ F .fst p ∣ₕ) , cong ∣_∣ₕ (snd F))
       ((λ p → sumFinK {m = suc n} (λ i → ∣ fst F (inr (i , chooseS i p)) ∣ₕ)) , sumPt)
       (uncurry main-lem)
      where
      id₁ : (x : Fin (suc m)) (y : _)
        → fst F (inr (x , chooseS x (inr (x , y)))) ≡ fst F (inr (x , y))
      id₁ (x , p) y with (x ≟ x)
      ... | lt x₁ = ⊥.rec (¬m<m x₁)
      ... | eq x₁ = refl
      ... | gt x₁ = ⊥.rec (¬m<m x₁)

      id₂ : (x : _) (x' : Fin (suc m)) (y : _) (q : ¬ x' ≡ x)
         → ∣ fst F (inr (x' , chooseS x' (inr (x , y)))) ∣ₕ ≡ 0ₖ (suc n)
      id₂ (x , p) (x' , t) y con with (x' ≟ x)
      ... | lt x₁ = cong ∣_∣ₕ (cong (fst F) (sym (push (x' , t))) ∙ snd F)
      ... | eq x₁ = ⊥.rec (con (Σ≡Prop (λ _ → isProp≤) x₁))
      ... | gt x₁ = cong ∣_∣ₕ (cong (fst F) (sym (push (x' , t))) ∙ snd F)

      sumPt : sumFinK (λ i → ∣ fst F (inr (i , chooseS i (inl tt))) ∣ₕ) ≡ 0ₖ (suc n)
      sumPt = sumFinGen0 _+ₖ_ (0ₖ (suc n)) (rUnitₖ _) _
               (λ i → ∣ fst F (inr (i , chooseS i (inl tt))) ∣ₕ)
               (λ s → cong ∣_∣ₕ (cong (fst F) (sym (push s)) ∙ snd F))

      main-lem : (x : Fin (suc m)) (y : S₊ (suc n))
        → ∣ F .fst (inr (x , y)) ∣ₕ
        ≡ sumFinK {n = suc m} {m = suc n} (λ i → ∣ fst F (inr (i , chooseS i (inr (x , y)))) ∣ₕ)
      main-lem x y = sym (sumFin-choose _+ₖ_ (0ₖ (suc n)) (rUnitₖ _) (commₖ _)
        (λ i → ∣ fst F (inr (i , chooseS i (inr (x , y)))) ∣ₕ) ∣ F .fst (inr (x , y)) ∣ₕ x
          (cong ∣_∣ₕ (id₁ x y))
          λ x' → id₂ x x' y)

  simplify : (x : Fin l) (a : Fin m)
    → sumFin (λ a₁ → generator x a₁ ·ℤ degree (suc n) (λ x₁ → chooseS a (fst g (inr (a₁ , x₁)))))
     ≡ degree (suc n) (λ x₁ → chooseS a (fst g (inr (x , x₁))))
  simplify x a =
       sumFinId l
           (λ p → ·Comm (generator x p) (degree (suc n) (λ x₁ → chooseS a (fst g (inr (p , x₁)))))
         ∙ λ i → degree (suc n) (λ x₁ → chooseS a (fst g (inr (p , x₁)))) ·ℤ generator-comm x p i)
     ∙ sym (generator-is-generator (λ a₁ → degree (suc n) (λ x₁ → chooseS a (fst g (inr (a₁ , x₁))))) x)

degreeComp-pos : {n m k l : ℕ}
  → (f : SphereBouquet (suc n) (Fin m) → SphereBouquet (suc n) (Fin k))
  → (g : SphereBouquet (suc n) (Fin l) → SphereBouquet (suc n) (Fin m))
  → bouquetDegree (f ∘ g) ≡ compGroupHom (bouquetDegree g) (bouquetDegree f)
degreeComp-pos {n = n} {m = m} {k = k} {l = l} f g = PT.rec2 goalIsProp aux (isConnectedSphereBouquet (f (inl tt)))
                                                    (isConnectedSphereBouquet (g (inl tt)))
  where
    isSetAbGroupHom : (m : ℕ) (k : ℕ) → isSet (AbGroupHom (FreeAbGroup (Fin m)) (FreeAbGroup (Fin k)))
    isSetAbGroupHom m k = isSetGroupHom

    goalIsProp : isProp (bouquetDegree (f ∘ g) ≡ compGroupHom (bouquetDegree g) (bouquetDegree f))
    goalIsProp = isSetAbGroupHom l k _ _

    aux : f (inl tt) ≡ inl tt → g (inl tt) ≡ inl tt
      → bouquetDegree (f ∘ g) ≡ compGroupHom (bouquetDegree g) (bouquetDegree f)
    aux Hf Hg = degreeComp∙ (f , Hf) (g , Hg)

degreeConst : (n a b : ℕ) → bouquetDegree {n} {a} {b} (λ _ → inl tt) ≡ 0hom {G = ℤ[Fin a ]} {H = ℤ[Fin b ]}
degreeConst n a b = GroupHom≡ ((λ i r x → sumFin (λ a → r a ·ℤ (degree.degree-const n i)))
                              ∙∙ (λ i r x → sumFin (λ a → ·Comm (r a) (pos 0) i))
                              ∙∙ λ i r x → sumFin0 a i)

degreeSusp₀ : {m k : ℕ}
  → (f : SphereBouquet zero (Fin m) → SphereBouquet zero (Fin k))
  → bouquetDegree f ≡ bouquetDegree (bouquetSusp→ f)
degreeSusp₀ {m = m} {k = zero} f =
  subst (λ f → bouquetDegree f ≡ bouquetDegree (bouquetSusp→ f))
        f-const
        (degreeConst zero _ _
      ∙ sym (degreeConst (suc zero) _ _)
      ∙ cong bouquetDegree lem₂)
  where
  f-const : (λ _ → inl tt) ≡ f
  f-const = funExt (λ x → isContrSphereBouquetZero 0 .snd (f x))
  lem₂ : (λ _ → inl tt) ≡ bouquetSusp→ {n = zero} (λ _ → inl tt)
  lem₂ = funExt (λ x
    → isContrSphereBouquetZero 1 .snd (bouquetSusp→ (λ _ → inl tt) x))
degreeSusp₀ {m = m} {k = suc k} f =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt λ r → funExt λ a → sumFinId m λ y → cong (r y ·ℤ_)
              (degree-susp 0 (λ x → chooseS a (f (inr (y , x))))
              ∙ λ i → degree 1 (λ z → help y a z i)))
    where
    help : (y : _) (a : _) (z : _)
      → suspFunS∙ (λ x → chooseS a (f (inr (y , x)))) .fst z
       ≡ chooseS a (bouquetSusp→ f (inr (y , z)))
    help y a base = refl
    help y a (loop i) j = help' j i
      where
      main : (ft ff : SphereBouquet zero (Fin (suc k)))
           → cong SuspBool→S¹ (merid (chooseS a ff))
           ∙ cong SuspBool→S¹ (sym (merid (chooseS a ft)))
           ≡ cong (chooseS a) (cong sphereBouquetSuspFun (merid ff)
           ∙ sym (cong sphereBouquetSuspFun (merid ft)))
      main =
        SphereBouquet→Prop 0 fzero (λ _ → isPropΠ λ _ → isGroupoidS¹ _ _ _ _)
             λ x y → SphereBouquet→Prop 0 fzero (λ _ → isGroupoidS¹ _ _ _ _)
               λ x' y'
           → (cong₂ _∙_ (final y' x') (cong sym (final y x))
            ∙ sym (cong-∙ (chooseS a)
                  (merid-lem x' y' i1) (sym (merid-lem x y i1))))
            ∙ λ i → cong (chooseS a)
                  ((merid-lem x' y' (~ i) ∙ sym (merid-lem x y (~ i))))
        where
        merid-lem : (x : Fin (suc k)) (y : Bool)
          → cong (sphereBouquetSuspIso .Iso.fun) (merid (inr (x , y)))
           ≡ push x ∙∙ (λ i → inr (x , SuspBool→S¹ (merid y i))) ∙∙ sym (push x)
        merid-lem x y = cong-∙∙ (Iso.fun sphereBouquetSuspIso₀)
                                (push x)
                                (λ i → inr (x , (merid y ∙ sym (merid true)) i))
                                (sym (push x))
          ∙ cong (push x ∙∙_∙∙ sym (push x))
              (cong-∙ (λ z → Iso.fun sphereBouquetSuspIso₀ (inr (x , z)))
                                       (merid y) (sym (merid true))
              ∙ sym (rUnit _))

        pre-final : (y : Bool) (x : Fin (suc k))
          → cong SuspBool→S¹ (merid (chooseS a (inr (x , y))))
          ≡ cong (chooseS a) (push x)
          ∙∙ cong (chooseS a) (λ i → inr (x , SuspBool→S¹ (merid y i)))
          ∙∙ cong (chooseS a) (sym (push x))
        pre-final y x with (fst a ≟ fst x)
        ... | lt x₁ = rUnit refl
        ... | eq x₁ = rUnit _
        ... | gt x₁ = rUnit refl

        final : (y : Bool) (x : Fin (suc k))
          → cong SuspBool→S¹ (merid (chooseS a (inr (x , y))))
          ≡ cong (chooseS a) ((push x)
                           ∙∙ (λ i → inr (x , SuspBool→S¹ (merid y i)))
                           ∙∙ sym (push x))
        final y x =
            pre-final y x
          ∙ cong-∙∙ (chooseS a) (push x) (λ i → inr (x , SuspBool→S¹ (merid y i)))
           (sym (push x))

      help' : cong (suspFunS∙ (λ x → chooseS a (f (inr (y , x)))) .fst) loop
           ≡ cong (chooseS a) λ i → bouquetSusp→ f (inr (y , loop i))
      help' =
          (λ j i → Iso.inv S¹IsoSuspBool
                    (cong-∙ (suspFun λ x
                  → chooseS a (f (inr (y , x)))) (merid false) (sym (merid true)) j i))
        ∙ cong-∙ (Iso.inv S¹IsoSuspBool)
                 (merid (chooseS a (f (inr (y , false)))))
                 (sym (merid (chooseS a (f (inr (y , true))))))
        ∙ main (f (inr (y , true))) ((f (inr (y , false))))
        ∙ cong (cong (chooseS a)) (refl
             ∙ (sym  (cong-∙ sphereBouquetSuspFun
                     (merid (f (inr (y , false)))) (sym (merid (f (inr (y , true)))))))
             ∙ cong (cong sphereBouquetSuspFun)
               (sym (cong-∙ (suspFun f)
                      (merid (inr (y , false))) (sym (merid (inr (y , true)))))
             ∙ cong (cong (suspFun f))
                 (sym (cong-∙ (λ x → Iso.inv (Iso-SuspBouquet-Bouquet _ _)
                              (inr (y , x))) (merid false) (sym (merid true))))))
        ∙ λ j i → chooseS a (sphereBouquetSuspFun
                    (suspFun f (Iso.inv (Iso-SuspBouquet-Bouquet _ _)
                      (inr (y , (merid false ∙ sym (merid true)) i)))))

degreeSusp : {n m k : ℕ}
  → (f : SphereBouquet n (Fin m) → SphereBouquet n (Fin k))
  → bouquetDegree f ≡ bouquetDegree (bouquetSusp→ f)
degreeSusp {n = zero} = degreeSusp₀
degreeSusp {n = suc n} {m = m} {k = k} f =
  EqHoms λ (x : Fin m)
    → funExt λ (b : Fin k) → sumFinId m
      λ z → cong (generator x z ·ℤ_)
             (degree-susp (suc n) (λ x₁ → chooseS b (f (inr (z , x₁))))
           ∙ cong (Iso.fun (Hⁿ-Sⁿ≅ℤ (suc n) .fst))
                (cong ∣_∣₂ (funExt λ x → help b z x)))
  where
  f₁ : (b : Fin k) → (SphereBouquet (suc n) (Fin k) , inl tt) →∙ coHomK-ptd (suc n)
  fst (f₁ b) x = ∣ chooseS b x ∣ₕ
  snd (f₁ b) = refl

  f₂ : (b : Fin k) → (SphereBouquet (suc n) (Fin k) , inl tt) →∙ coHomK-ptd (suc n)
  fst (f₂ b) x = ΩKn+1→Kn (suc n)
                  λ i → ∣ chooseS b (Bouquet→ΩBouquetSusp (Fin k) (λ _ → S₊∙ (suc n)) x i) ∣
  snd (f₂ b) = ΩKn+1→Kn-refl (suc n)

  f₁≡f₂ : (b : Fin k) (x : _) → f₁ b .fst x ≡ f₂ b .fst x
  f₁≡f₂ b = Bouquet→KnEq (suc n) (f₁ b) (f₂ b) (uncurry main)
    where
    main : (x : Fin k) (y : S₊ (suc n))
      → f₁ b .fst (inr (x , y)) ≡ f₂ b .fst (inr (x , y))
    main x y =
      main'
      ∙ cong (ΩKn+1→Kn (suc n))
           (cong (cong ∣_∣ₕ)
             (sym (cong-∙∙ (chooseS {n = 2 +ℕ n} b)
             (push x) (λ i → inr (x , σ (suc n) y i)) (sym (push x)))))
      where
      main' : f₁ b .fst (inr (x , y))
            ≡ ΩKn+1→Kn (suc n)
               (cong ∣_∣ₕ (cong (chooseS {n = 2 +ℕ n} b) (push x)
                      ∙∙ (λ i → chooseS {n = 2 +ℕ n} b (inr (x , σ (suc n) y i)))
                      ∙∙ cong (chooseS {n = 2 +ℕ n} b) (sym (push x)) ))
      main' with (fst b ≟ fst x)
      ... | lt x = sym (cong (ΩKn+1→Kn (suc n)) (sym (rUnit refl)) ∙ ΩKn+1→Kn-refl (suc n))
      ... | eq x = sym (cong (ΩKn+1→Kn (suc n)) (cong (cong ∣_∣ₕ) (sym (rUnit (σ (suc n) y))))
                 ∙ Iso.leftInv (Iso-Kn-ΩKn+1 (suc n)) ∣ y ∣)
      ... | gt x = sym (cong (ΩKn+1→Kn (suc n)) (sym (rUnit refl)) ∙ ΩKn+1→Kn-refl (suc n))

  help : (b : Fin k) (z : Fin m) (t : _)
    → Path (coHomK (2 +ℕ n))
            (∣ suspFun (λ x₁ → chooseS b (f (inr (z , x₁)))) t ∣ₕ)
             ∣ chooseS b (bouquetSusp→ f (inr (z , t))) ∣ₕ
  help b z north = refl
  help b z south = cong ∣_∣ₕ (sym (merid (ptSn (suc n))))
  help b z (merid a i) j =
    hcomp (λ r
     → λ {(i = i0) → ∣ north ∣
         ; (i = i1) → ∣ merid (ptSn (suc n)) (~ j ∧ r) ∣
         ; (j = i0) → ∣ compPath-filler
                         (merid (chooseS b (f (inr (z , a)))))
                         (sym (merid (ptSn (suc n)))) (~ r) i ∣ₕ
         ; (j = i1) → (cong (Kn→ΩKn+1 (suc n)) (f₁≡f₂ b (f (inr (z , a))))
                     ∙ Iso.rightInv (Iso-Kn-ΩKn+1 (suc n))
                        (λ i → ∣ chooseS b (bouquetSusp→ f
                                  (inr (z , merid a i))) ∣)) r i})
          (Kn→ΩKn+1 (suc n) ∣ chooseS b (f (inr (z , a))) ∣ i)

degreeComp : {n m k l : ℕ}
  → (f : SphereBouquet n (Fin m) → SphereBouquet n (Fin k))
  → (g : SphereBouquet n (Fin l) → SphereBouquet n (Fin m))
  → bouquetDegree (f ∘ g) ≡ compGroupHom (bouquetDegree g) (bouquetDegree f)
degreeComp {n = zero} f g =
     degreeSusp (f ∘ g)
  ∙∙ Σ≡Prop (λ _ → isPropIsGroupHom _ _)
      ((λ i → bouquetDegree (bouquetSusp→∘ g f (~ i)) .fst)
    ∙ cong fst (degreeComp-pos (bouquetSusp→ f) (bouquetSusp→ g)))
  ∙∙ sym (cong₂ compGroupHom (degreeSusp g) (degreeSusp f))
degreeComp {n = suc n} f g = degreeComp-pos f g

------------------
-- Equivalence between Bouquet of spheres and the cofibre
-- Dunno where to place this.

preBTC : {Cₙ Cₙ₊₁ : Type} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → (x : Fin mₙ)
    → S₊∙ n →∙ (Pushout (terminal Cₙ) (invEq e ∘ inl) , inl tt)
fst (preBTC zero mₙ αₙ e x) false = inr (invEq e (inr x))
fst (preBTC zero mₙ αₙ e x) true = inl tt
fst (preBTC (suc zero) mₙ αₙ e x) base = inl tt
fst (preBTC (suc zero) mₙ αₙ e x) (loop i) =
    (push (αₙ (x , false))
  ∙∙ (λ j → inr (invEq e ((push (x , false) ∙ sym (push (x , true))) j)))
  ∙∙ sym (push (αₙ (x , true)))) i
fst (preBTC (suc (suc n)) mₙ αₙ e x) north = inl tt
fst (preBTC (suc (suc n)) mₙ αₙ e x) south = inl tt
fst (preBTC (suc (suc n)) mₙ αₙ e x) (merid a i) =
  (push (αₙ (x , a))
  ∙∙ (λ j → inr (invEq e ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) j )))
  ∙∙ sym (push (αₙ (x , ptSn (suc n))))) i
snd (preBTC zero mₙ αₙ e x) = refl
snd (preBTC (suc zero) mₙ αₙ e x) = refl
snd (preBTC (suc (suc n)) mₙ αₙ e x) = refl

ptSnInv : (n : ℕ) → S₊ n
ptSnInv zero = false
ptSnInv (suc n) = ptSn (suc n)

σ⁻ : (n : ℕ) → S⁻ n → typ (Ω (S₊ n , ptSnInv n))
σ⁻ (suc n) = σ n

module _  where
  Pushout→Bouquet : {Cₙ Cₙ₊₁ : Type} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → Pushout αₙ fst → SphereBouquet n (Fin mₙ)
  Pushout→Bouquet n mₙ αₙ e (inl x) = inl tt
  Pushout→Bouquet zero mₙ αₙ e (inr x) = inr (x , false)
  Pushout→Bouquet (suc n) mₙ αₙ e (inr x) = inr (x , ptSn (suc n))
  Pushout→Bouquet (suc n) mₙ αₙ e (push a i) = (push (a .fst) ∙ λ i → inr (a .fst , σ n (a .snd) i)) i

module BouquetFuns {Cₙ Cₙ₊₁ : Type} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where
  CTB : Pushout (terminal Cₙ) (invEq e ∘ inl) → SphereBouquet n (Fin mₙ)
  CTB (inl x) = inl tt
  CTB (inr x) = Pushout→Bouquet n mₙ αₙ e (fst e x)
  CTB (push a i) = Pushout→Bouquet n mₙ αₙ e (secEq e (inl a) (~ i))

  BTC : SphereBouquet n (Fin mₙ) → Pushout (terminal Cₙ) (invEq e ∘ inl)
  BTC (inl x) = inl tt
  BTC (inr x) = preBTC n mₙ αₙ e (fst x) .fst (snd x)
  BTC (push a i) = preBTC n mₙ αₙ e a .snd (~ i)

CTB-BTC-cancel : {Cₙ Cₙ₊₁ : Type} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → section (BouquetFuns.CTB n mₙ αₙ e) (BouquetFuns.BTC n mₙ αₙ e)
     × retract (BouquetFuns.CTB n mₙ αₙ e) (BouquetFuns.BTC n mₙ αₙ e)
CTB-BTC-cancel {Cₙ = Cₙ} n mₙ αₙ =
    EquivJ (λ C₊ e →
      section (BouquetFuns.CTB n mₙ αₙ e)
      (BouquetFuns.BTC n mₙ αₙ e)
      ×
      retract (BouquetFuns.CTB n mₙ αₙ e)
      (BouquetFuns.BTC n mₙ αₙ e))
     (retr-main n αₙ , section-main n αₙ)
  where
  module S (n : ℕ) (αₙ : Fin mₙ × S⁻ n → Cₙ) where
    module T = BouquetFuns n mₙ αₙ (idEquiv _)
    open T public

  retr-inr : (n : ℕ) (αₙ : Fin mₙ × S⁻ n → Cₙ) (a : _) (b : _)
    → S.CTB n αₙ (S.BTC n αₙ (inr (a , b))) ≡ inr (a , b)
  retr-inr zero aₙ a false = refl
  retr-inr zero aₙ a true = push a
  retr-inr (suc zero) αₙ a base = push a
  retr-inr (suc zero) αₙ  a (loop i) j =
    hcomp (λ r → λ {(i = i0) → push a j
                   ; (i = i1) → push a j
                   ; (j = i0) → S.CTB (suc zero) αₙ
                                  (doubleCompPath-filler
                                    (push (αₙ (a , false)))
                                    (λ j → inr ((push (a , false)
                                               ∙ sym (push (a , true))) j))
                                    (sym (push (αₙ (a , true)))) r i)
                   ; (j = i1) → inr (a , loop i)})
     (hcomp (λ r → λ {(i = i0) → push a j
                   ; (i = i1) → compPath-filler' (push a) refl (~ j) (~ r)
                   ; (j = i0) → S.CTB (suc zero) αₙ
                                  (inr (compPath-filler
                                          (push (a , false))
                                          (sym (push (a , true))) r i))
                   ; (j = i1) → inr (a , loop i)})
       (hcomp (λ r → λ {(i = i0) → push a (j ∨ ~ r)
              ; (i = i1) → inr (a , base)
              ; (j = i0) → compPath-filler' (push a) (λ j → inr (a , loop j)) r i
              ; (j = i1) → inr (a , loop i)})
                  (inr (a , loop i))))
  retr-inr (suc (suc n)) αₙ a north = push a
  retr-inr (suc (suc n)) αₙ a south = push a ∙ λ j → inr (a , merid (ptSn (suc n)) j)
  retr-inr (suc (suc n)) αₙ a (merid a₁ i) j =
    hcomp (λ r → λ {(i = i0) → push a j
                   ; (i = i1) → compPath-filler
                                  (push a)
                                  (λ j₁ → inr (a , merid (ptSn (suc n)) j₁)) r j
                   ; (j = i0) → S.CTB (suc (suc n)) αₙ
                                   (doubleCompPath-filler
                                    (push (αₙ (a , a₁)))
                                    (λ i → inr ((push (a , a₁)
                                               ∙ sym (push (a , ptSn (suc n)))) i))
                                    (sym (push (αₙ (a , ptSn (suc n))))) r i)
                   ; (j = i1) → inr (a , compPath-filler (merid a₁)
                                           (sym (merid (ptSn (suc n)))) (~ r) i)})
    (hcomp (λ r → λ {(i = i0) → push a j
                    ; (i = i1) → compPath-filler' (push a)
                                   (λ i → inr (a , σ _ (ptSn (suc n)) i)) (~ j) (~ r)
                    ; (j = i0) → S.CTB (suc (suc n)) αₙ
                                    (inr (compPath-filler (push (a , a₁))
                                          (sym (push (a , ptSn (suc n)))) r i) )
                    ; (j = i1) → inr (a , help r i)})
        (hcomp (λ r → λ {(i = i0) → push a (j ∨ ~ r)
                      ; (i = i1) → inr (a , north)
                      ; (j = i0) → compPath-filler'
                                     (push a) (λ i → inr (a , σ _ a₁ i)) r i
                      ; (j = i1) → inr (a , σ _ a₁ i)})
               (inr (a , σ _ a₁ i))))
    where
    help : Square (σ _ a₁) (σ _ a₁) refl (sym (σ _ (ptSn (suc n))))
    help = flipSquare ((λ i _ → σ _ a₁ i)
         ▷ λ i → sym (rCancel (merid (ptSn (suc n))) (~ i)))

  retr-main : (n : _) (αₙ : _) → section (S.CTB n αₙ) (S.BTC n αₙ)
  retr-main n αₙ (inl x) = refl
  retr-main n αₙ (inr (a , b)) = retr-inr n αₙ a b
  retr-main zero αₙ (push a i) j = push a (i ∧ j)
  retr-main (suc zero) αₙ (push a i) j = push a (i ∧ j)
  retr-main (suc (suc n)) αₙ (push a i) j = push a (i ∧ j)

  section-main : (n : _) (αₙ : _) → retract (S.CTB n αₙ) (S.BTC n αₙ)
  section-main n αₙ (inl x) = refl
  section-main n αₙ (inr (inl x)) = push x
  section-main zero αₙ (inr (inr x)) = refl
  section-main (suc zero) αₙ (inr (inr x)) =
    push (αₙ (x , true)) ∙ λ i → inr (push (x , true) i)
  section-main (suc (suc n)) αₙ (inr (inr x)) =
    push (αₙ (x , ptSn (suc n))) ∙ λ i → inr (push (x , ptSn (suc n)) i)
  section-main (suc zero) αₙ (inr (push (a , false) i)) j =
    hcomp (λ r → λ {(i = i0) → push (αₙ (a , false)) j
                   ; (i = i1) → compPath-filler (push (αₙ (a , true)))
                                  (λ i₁ → inr (push (a , true) i₁)) i1 j
                   ; (j = i0) →
                      S.BTC (suc zero) αₙ
                         (compPath-filler'
                           (push a)
                           (λ i → inr (a , σ zero false i)) r i)
                   ; (j = i1) → inr (push (a , false) i)})
       (hcomp (λ r → λ {(i = i0) → push (αₙ (a , false)) (j ∨ ~ r)
                   ; (i = i1) →
                          compPath-filler'
                            (push (αₙ (a , true)))
                            (λ i → inr (push (a , true) i)) r j
                   ; (j = i1) → inr (push (a , false) i)})
              (inr (compPath-filler
                     (push (a , false))
                     (sym (push (a , true))) (~ j) i)))
  section-main (suc zero) αₙ (inr (push (a , true) i)) j =
    hcomp (λ r → λ {(i = i0) → push (αₙ (a , true)) j
                   ; (i = i1) → compPath-filler (push (αₙ (a , true)))
                                  (λ i₁ → inr (push (a , true) i₁)) r j
                   ; (j = i0) → S.BTC (suc zero) αₙ
                                  (compPath-filler'
                                   (push a)
                                   (λ i → inr (a , σ zero true i)) r i)
                   ; (j = i1) → inr (push (a , true) (i ∧ r))})
            (push (αₙ (a , true)) j)
  section-main (suc (suc n)) αₙ (inr (push a i)) j =
    hcomp (λ r → λ {(i = i0) → push (αₙ a) j
                   ; (i = i1) → compPath-filler (push (αₙ (fst a , ptSn (suc n))))
                                  (λ i₁ → inr (push (fst a , ptSn (suc n)) i₁)) i1 j
                   ; (j = i0) → S.BTC (suc (suc n)) αₙ
                                  (compPath-filler' (push (fst a))
                                    (λ i → inr (fst a , σ (suc n) (snd a) i)) r i)
                   ; (j = i1) → inr (push a i)})
    (hcomp (λ r → λ {(i = i0) → doubleCompPath-filler (push (αₙ a))
                                   (λ j → inr ((push a ∙ sym (push (fst a , ptSn (suc n)))) j))
                                   (sym (push (αₙ (fst a , ptSn (suc n))))) (~ j) (~ r)
                 ; (i = i1) → compPath-filler (push (αₙ (fst a , ptSn (suc n))))
                                               (λ i → inr (push (fst a , ptSn (suc n)) i)) r j
                 ; (j = i0) → S.BTC (suc (suc n)) αₙ (inr (fst a
                             , compPath-filler' (merid (snd a)) (sym (merid (ptSn (suc n)))) r i ))
                 ; (j = i1) → inr (compPath-filler'
                                    (push a)
                                    (sym (push (fst a , ptSn (suc n)))) (~ i) (~ r))})
    (hcomp (λ r → λ {(i = i0) → push (αₙ (fst a , ptSn (suc n))) (j ∨ ~ r)
                 ; (i = i1) → push (αₙ (fst a , ptSn (suc n))) (j ∨ ~ r)
                 ; (j = i1) → inr (inl (αₙ (fst a , ptSn (suc n))))})
          (inr (ugh (push (fst a , ptSn (suc n))) j i))))
    where
    ugh : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙' sym p ≡ refl
    ugh p = sym (compPath≡compPath' p (sym p)) ∙ rCancel p
  section-main n αₙ (push a i) j = push a (i ∧ j)

module _ {Cₙ Cₙ₊₁ : Type} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where

  open BouquetFuns n mₙ αₙ e

  BouquetIso-gen : Iso (Pushout (terminal Cₙ) (invEq e ∘ inl)) (SphereBouquet n (Fin mₙ))
  Iso.fun BouquetIso-gen = CTB
  Iso.inv BouquetIso-gen = BTC
  Iso.rightInv BouquetIso-gen = CTB-BTC-cancel n mₙ αₙ e .fst
  Iso.leftInv BouquetIso-gen = CTB-BTC-cancel n mₙ αₙ e .snd

  Bouquet≃-gen : Pushout (terminal Cₙ) (invEq e ∘ inl)
               ≃ SphereBouquet n (Fin mₙ)
  Bouquet≃-gen = isoToEquiv BouquetIso-gen

degreeCompFull : {n m k l : ℕ}
  → (f : (SphereBouquet n (Fin m) , inl tt) →∙ (SphereBouquet n (Fin k) , inl tt))
  → (g : (SphereBouquet n (Fin l) , inl tt) →∙ (SphereBouquet n (Fin m) , inl tt))
  → bouquetDegree ((fst f) ∘ (fst g)) ≡ compGroupHom (bouquetDegree (fst g)) (bouquetDegree (fst f))
degreeCompFull {n = zero} {m} {k = k} {l = l} f g = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (cong fst (degreeSusp (fst f ∘ fst g))
  ∙ sym (cong (fst ∘ bouquetDegree) (bouquetSusp→∘ (fst g) (fst f)))
  ∙ cong fst (degreeComp∙ (bouquetSusp→ (fst f) , refl) (bouquetSusp→ (fst g) , refl))
  ∙ cong fst (cong₂ compGroupHom (sym (degreeSusp (fst g))) (sym (degreeSusp (fst f)))))
degreeCompFull {n = suc n} = degreeComp∙
