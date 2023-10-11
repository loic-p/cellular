{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool hiding (_≤_ ;  _≟_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetTruncation as ST

open import Cubical.Relation.Nullary
open import Cubical.Homotopy.Loopspace
open import Cubical.ZCohomology.Groups.Sn


open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.QuotientGroup renaming (_/_ to _//_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.AbGroup

open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence

open import Cubical.Foundations.Function
open import Cubical.HITs.S1
open import Cubical.Foundations.Path

open import prelude
open import freeabgroup

module spherebouquet where

--terminal map from any type to Unit
terminal : (A : Type) → A → Unit
terminal A x = tt

--
suspFunS∙ : {n : ℕ} → (S₊ n → S₊ n) → S₊∙ (suc n) →∙ S₊∙ (suc n)
suspFunS∙ {n = zero} f with (f true)
... | false = invLooper , refl
... | true = idfun S¹ , refl
suspFunS∙ {n = suc n} f = suspFun f , refl

--a sphere bouquet is the wedge sum of A n-dimensional spheres
SphereBouquet : (n : ℕ) (A : Type) → Pointed₀
SphereBouquet n A = Pushout (terminal A) ((λ a → (a , ptSn n))) , inl tt

Bouquet : (A : Type) (B : A → Pointed₀) → Pointed₀
Bouquet A B = Pushout (terminal A) (λ a → a , pt (B a)) , inl tt

Bouquet→ΩBouquetSusp-filler : (A : Type) (B : A → Pointed₀)
  → (a : _) → (i j k : I) → Bouquet A (λ a → Susp∙ (fst (B a))) .fst
Bouquet→ΩBouquetSusp-filler A B a i j k =
  hfill (λ k → λ {(i = i0) → inl tt
                 ; (i = i1) → doubleCompPath-filler
                                (push a)
                                (λ i → inr (a , rCancel' (merid (snd (B a))) (~ k) i))
                                (sym (push a)) k j
                 ; (j = i0) → push a (~ k ∧ i)
                 ; (j = i1) → push a (~ k ∧ i)})
        (inS (push a i))
        k

Bouquet→ΩBouquetSusp : (A : Type) (B : A → Pointed₀)
  → Bouquet A B .fst
  → Ω (Bouquet A λ a → Susp∙ (fst (B a))) .fst
Bouquet→ΩBouquetSusp A B (inl x) = refl
Bouquet→ΩBouquetSusp A B (inr (a , b)) =
  (push a ∙∙ (λ i → inr (a , toSusp (B a) b i)) ∙∙ sym (push a))
Bouquet→ΩBouquetSusp A B (push a i) j = Bouquet→ΩBouquetSusp-filler A B a i j i1

SuspBouquet→Bouquet : (A : Type) (B : A → Pointed₀)
  → Susp (Bouquet A B .fst) → Bouquet A (λ a → Susp∙ (fst (B a))) .fst
SuspBouquet→Bouquet A B north = inl tt
SuspBouquet→Bouquet A B south = inl tt
SuspBouquet→Bouquet A B (merid a i) = Bouquet→ΩBouquetSusp A B a i

Bouquet→SuspBouquet : (A : Type) (B : A → Pointed₀)
  → Bouquet A (λ a → Susp∙ (fst (B a))) .fst → Susp (Bouquet A B .fst)
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
    sec (inr (a , south)) = (push a) ∙∙ (λ i → inr (a , merid (pt (B a)) i)) ∙∙ (λ i → inr (a , south))
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
      ret-fill₁ : I →  Susp (Bouquet A B .fst)
      ret-fill₁ k =
        hfill (λ k → λ {(j = i0) → north
                       ; (j = i1) → merid (inr (a , pt (B a))) ((~ k) ∨ i)
                       ; (i = i0) → Bouquet→SuspBouquet A B (inr (a , compPath-filler (merid b)
                            (sym (merid (pt (B a)))) k j))
                       ; (i = i1) → merid (inr (a , b)) j})
              (inS (merid (inr (a , b)) j)) k

      ret-fill₂ : I → Susp (Bouquet A B .fst)
      ret-fill₂ k =
        hfill (λ k → λ {(j = i0) → north
                     ; (j = i1) → merid (push a (~ k)) i
                     ; (i = i0) → Bouquet→SuspBouquet A B (doubleCompPath-filler (push a)
                          (λ i → inr (a , toSusp (B a) b i)) (sym (push a)) k j)
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
         side : Cube {A = Susp (Bouquet A B .fst)}
                   (λ i j → merid (inr (a , pt (B a))) (i ∧ j))
                   (λ i j → ret-fill₂ a (pt (B a)) i j i1)
                   (λ r j → Bouquet→SuspBouquet A B
                              (Bouquet→ΩBouquetSusp-filler A B a i1 j r))
                   (λ r j → merid (inr (a , (pt (B a)))) j)
                   (λ r i → north)
                   λ r i → merid (push a (~ r)) i
         side r i j =
           hcomp (λ k → λ {(r = i0) → Bouquet→SuspBouquet A B
                                        (inr (a , rCancel-filler' (merid (pt (B a))) i k j))
                     ; (r = i1) →  ret-fill₂ a (pt (B a)) i j k
                     ; (i = i0) → Bouquet→SuspBouquet A B
                                    (doubleCompPath-filler
                                      (push a) (λ j → inr (a , rCancel' (merid (pt (B a))) (~ r ∧ k) j))
                                      (sym (push a)) (r ∧ k) j)
                     ; (i = i1) → merid (inr (a , snd (B a))) j
                     ; (j = i0) → north
                     ; (j = i1) → merid (push a (~ r ∨ ~ k)) i})
             (hcomp (λ k → λ {(r = i0) → Bouquet→SuspBouquet A B
                                           (inr (a , rCancel-filler' (merid (pt (B a))) (~ k ∨ i) i0 j))
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
  → Iso (Susp (Bouquet A B .fst)) (Bouquet A (λ a → Susp∙ (fst (B a))) .fst)
Iso.fun (Iso-SuspBouquet-Bouquet A B) = SuspBouquet→Bouquet A B
Iso.inv (Iso-SuspBouquet-Bouquet A B) = Bouquet→SuspBouquet A B
Iso.rightInv (Iso-SuspBouquet-Bouquet A B) = SuspBouquet-Bouquet-cancel A B .fst
Iso.leftInv (Iso-SuspBouquet-Bouquet A B) = SuspBouquet-Bouquet-cancel A B .snd

SuspBouquet≃∙Bouquet : (A : Type) (B : A → Pointed₀)
  → Susp∙ (Bouquet A B .fst) ≃∙ Bouquet A (λ a → Susp∙ (fst (B a)))
fst (SuspBouquet≃∙Bouquet A B) = isoToEquiv (Iso-SuspBouquet-Bouquet A B)
snd (SuspBouquet≃∙Bouquet A B) = refl

sphereBouquetSuspIso : {A : Type} {n : ℕ}
  → Iso (Susp (SphereBouquet n A .fst)) (SphereBouquet (suc n) A .fst)
sphereBouquetSuspIso {A = A} {n = zero} =
  compIso (Iso-SuspBouquet-Bouquet A λ _ → S₊∙ zero)
    (subst (λ P → Iso (Bouquet A (λ a → P) .fst) (SphereBouquet 1 A .fst))
      (ua∙ (isoToEquiv (IsoSucSphereSusp zero)) refl)
      idIso) 
sphereBouquetSuspIso {A = A} {n = suc n} = Iso-SuspBouquet-Bouquet A λ _ → S₊∙ (suc n)

sphereBouquet≃∙Susp : {A : Type} {n : ℕ}
  → Susp∙ (SphereBouquet n A .fst) ≃∙ SphereBouquet (suc n) A
fst sphereBouquet≃∙Susp = isoToEquiv (sphereBouquetSuspIso)
snd (sphereBouquet≃∙Susp {n = zero}) = refl
snd (sphereBouquet≃∙Susp {n = suc n}) = refl

sphereBouquetSuspFun : {A : Type} {n : ℕ}
  → Susp (SphereBouquet n A .fst) → SphereBouquet (suc n) A .fst
sphereBouquetSuspFun {A = A} {n = n} = sphereBouquetSuspIso .Iso.fun

sphereBouquetSuspFun∙ : {A : Type} {n : ℕ}
  → Susp∙ (SphereBouquet n A .fst) →∙ SphereBouquet (suc n) A
sphereBouquetSuspFun∙ {A = A} {n = n} = ≃∙map (sphereBouquet≃∙Susp)

sphereBouquetSuspInvFun∙ : {A : Type} {n : ℕ}
  → SphereBouquet (suc n) A →∙ Susp∙ (SphereBouquet n A .fst)
sphereBouquetSuspInvFun∙ {A = A} {n = n} = ≃∙map (invEquiv∙ (sphereBouquet≃∙Susp))

suspFun∙ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
       → Susp∙ A →∙ Susp∙ B
fst (suspFun∙ f) = suspFun f
snd (suspFun∙ f) = refl

--the suspension of a n-dimensional bouquet is a (n+1)-dimensional bouquet
--here is the action of suspension on morphisms
bouquetSusp→ : {n : ℕ} {A B : Type}
  → (SphereBouquet n A →∙ SphereBouquet n B)
  → (SphereBouquet (suc n) A →∙ SphereBouquet (suc n) B)
bouquetSusp→ {n = n} {A} {B} f =
     sphereBouquetSuspFun∙ ∘∙ (suspFun∙ (fst f) ∘∙ sphereBouquetSuspInvFun∙)

-- bullshit
private
  bouquetSusp→' : {n : ℕ} {A B : Type}
    → (SphereBouquet n A →∙ SphereBouquet n B)
    → (SphereBouquet (suc n) A →∙ SphereBouquet (suc n) B)
  fst (bouquetSusp→' {n} f) = sphereBouquetSuspFun ∘ suspFun (fst f) ∘ Iso.inv sphereBouquetSuspIso
  snd (bouquetSusp→' {zero} f) = refl
  snd (bouquetSusp→' {suc n} f) = refl

  -- fill if need be
  bouquetSusp→≡ : {n : ℕ} {A B : Type} (f : SphereBouquet n A →∙ SphereBouquet n B)
    → bouquetSusp→ f ≡ bouquetSusp→' f
  bouquetSusp→≡ {n = n} f = {!!}

degree : (n : ℕ) → (S₊ n → S₊ n) → ℤ
degree zero f = 0
degree (suc n) f = Iso.fun ((Hⁿ-Sⁿ≅ℤ n) .fst) ∣ (λ x → ∣ f x ∣) ∣₂

chooseS : {n k : ℕ} (b : Fin k)
  → fst (SphereBouquet n (Fin k)) → S₊ n
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
bouquetDegree : {n m k : ℕ} → (SphereBouquet n (Fin m) →∙ SphereBouquet n (Fin k))
                             → (AbGroupHom (FreeAbGroup (Fin m)) (FreeAbGroup (Fin k)))
fst (bouquetDegree {m = m} {k = k} f) r x =
  sumFin λ (a : Fin m) → r a ·ℤ (degree _ (chooseS x ∘ f .fst ∘ inr ∘ (a ,_)))
snd (bouquetDegree {n = n} f) =
  makeIsGroupHom λ x y
    → funExt λ a'
      → (λ j → sumFin (λ a → ·DistL+ (x a) (y a) (degree _ (chooseS a' ∘ f .fst ∘ inr ∘ (a ,_))) j))
      ∙ sumFin-hom (λ a → x a ·ℤ (degree _ (chooseS a' ∘ f .fst ∘ inr ∘ (a ,_))))
                              λ a → y a ·ℤ (degree _ (chooseS a' ∘ f .fst ∘ inr ∘ (a ,_)))

--degree is compatible with composition

-- degreeComp : {n : ℕ} {A B C : Type} → (f : SphereBouquet n ? →∙ SphereBouquet n C)
--                                     → (g : SphereBouquet n A →∙ SphereBouquet n B)
--                                     → bouquetDegree (f ∘∙ g) ≡ compGroupHom (bouquetDegree g) (bouquetDegree f)
-- degreeComp f g = {!!}

--the degree of a suspension is the same as the original degree
--in fact, ℤ[ A ] is basically the infinite suspension of a bouquet
-- degreeSusp : {n : ℕ} {A B : Type} → (f : SphereBouquet n A →∙ SphereBouquet n B)
--                                   → bouquetDegree f ≡ bouquetDegree (bouquetSusp→ f)
-- degreeSusp f = {!!}


------------------
-- Equivalence between Bouquet of spheres and the cofibre
-- Dunno where to place this.



preBTC : {Cₙ Cₙ₊₁ : Type} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S₊ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → (x : Fin mₙ)
    → S₊∙ (suc n) →∙ (Pushout (terminal Cₙ) (invEq e ∘ inl) , inl tt)
fst (preBTC zero mₙ αₙ e x) base = inl tt
fst (preBTC zero mₙ αₙ e x) (loop i) =
  (push (αₙ (x , false))
  ∙∙ (λ j → inr (invEq e ((push (x , false) ∙ sym (push (x , true))) j)))
  ∙∙ sym (push (αₙ (x , true)))) i
fst (preBTC (suc n) mₙ αₙ e x) north = inl tt
fst (preBTC (suc n) mₙ αₙ e x) south = inl tt
fst (preBTC (suc n) mₙ αₙ e x) (merid a i) =
  (push (αₙ (x , a))
  ∙∙ (λ j → inr (invEq e ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) j )))
  ∙∙ sym (push (αₙ (x , ptSn (suc n))))) i
snd (preBTC zero mₙ αₙ e x) = refl
snd (preBTC (suc n) mₙ αₙ e x) = refl

module BouquetFuns {Cₙ Cₙ₊₁ : Type} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S₊ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where
  Pushout→Bouquet : Pushout αₙ fst → SphereBouquet (suc n) (Fin mₙ) .fst
  Pushout→Bouquet (inl x) = inl tt
  Pushout→Bouquet (inr x) = inr (x , ptSn (suc n))
  Pushout→Bouquet (push a i) = (push (a .fst) ∙ λ i → inr (a .fst , σ n (a .snd) i)) i

  CTB : Pushout (terminal Cₙ) (invEq e ∘ inl) → SphereBouquet (suc n) (Fin mₙ) .fst
  CTB (inl x) = inl tt
  CTB (inr x) = Pushout→Bouquet (fst e x)
  CTB (push a i) = Pushout→Bouquet (secEq e (inl a) (~ i))

  BTC : SphereBouquet (suc n) (Fin mₙ) .fst → Pushout (terminal Cₙ) (invEq e ∘ inl)
  BTC (inl x) = inl tt
  BTC (inr x) = preBTC n mₙ αₙ e (fst x) .fst (snd x)
  BTC (push a i) = preBTC n mₙ αₙ e a .snd (~ i)

CTB-BTC-cancel : {Cₙ Cₙ₊₁ : Type} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S₊ n → Cₙ)
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
  module S (n : ℕ) (αₙ : Fin mₙ × S₊ n → Cₙ) where
    module T = BouquetFuns n mₙ αₙ (idEquiv _)
    open T public

  retr-inr : (n : _) (αₙ : _) (a : _) (b : _)
    → S.CTB n αₙ (S.BTC n αₙ (inr (a , b))) ≡ inr (a , b)
  retr-inr zero αₙ a base = push a
  retr-inr zero αₙ  a (loop i) j =
    hcomp (λ r → λ {(i = i0) → push a j
                   ; (i = i1) → push a j
                   ; (j = i0) → S.CTB zero αₙ
                                  (doubleCompPath-filler
                                    (push (αₙ (a , false)))
                                    (λ j → inr ((push (a , false)
                                               ∙ sym (push (a , true))) j))
                                    (sym (push (αₙ (a , true)))) r i)
                   ; (j = i1) → inr (a , loop i)})
     (hcomp (λ r → λ {(i = i0) → push a j
                   ; (i = i1) → compPath-filler' (push a) refl (~ j) (~ r)
                   ; (j = i0) → S.CTB zero αₙ
                                  (inr (compPath-filler
                                          (push (a , false))
                                          (sym (push (a , true))) r i))
                   ; (j = i1) → inr (a , loop i)})
       (hcomp (λ r → λ {(i = i0) → push a (j ∨ ~ r)
              ; (i = i1) → inr (a , base)
              ; (j = i0) → compPath-filler' (push a) (λ j → inr (a , loop j)) r i
              ; (j = i1) → inr (a , loop i)})
                  (inr (a , loop i))))
  retr-inr (suc n) αₙ a north = push a
  retr-inr (suc n) αₙ a south = push a ∙ λ j → inr (a , merid (ptSn (suc n)) j)
  retr-inr (suc n) αₙ a (merid a₁ i) j =
    hcomp (λ r → λ {(i = i0) → push a j
                   ; (i = i1) → compPath-filler
                                  (push a)
                                  (λ j₁ → inr (a , merid (ptSn (suc n)) j₁)) r j
                   ; (j = i0) → S.CTB (suc n) αₙ
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
                    ; (j = i0) → S.CTB (suc n) αₙ
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
  retr-main n αₙ (inr (a , b)) i = retr-inr n αₙ a b i
  retr-main zero αₙ (push a i) j = push a (i ∧ j)
  retr-main (suc n) αₙ (push a i) j = push a (i ∧ j)


  section-main : (n : _) (αₙ : _) → retract (S.CTB n αₙ) (S.BTC n αₙ)
  section-main n αₙ (inl x) = refl
  section-main n αₙ (inr (inl x)) = push x
  section-main zero αₙ (inr (inr x)) =
    push (αₙ (x , true)) ∙ λ i → inr (push (x , true) i)
  section-main (suc n) αₙ (inr (inr x)) =
    push (αₙ (x , ptSn (suc n))) ∙ λ i → inr (push (x , ptSn (suc n)) i)
  section-main zero αₙ (inr (push (a , false) i)) j =
    hcomp (λ r → λ {(i = i0) → push (αₙ (a , false)) j
                   ; (i = i1) → compPath-filler (push (αₙ (a , true)))
                                  (λ i₁ → inr (push (a , true) i₁)) i1 j
                   ; (j = i0) →
                      S.BTC zero αₙ
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
  section-main zero αₙ (inr (push (a , true) i)) j =
    hcomp (λ r → λ {(i = i0) → push (αₙ (a , true)) j
                   ; (i = i1) → compPath-filler (push (αₙ (a , true)))
                                  (λ i₁ → inr (push (a , true) i₁)) r j
                   ; (j = i0) → S.BTC zero αₙ
                                  (compPath-filler'
                                   (push a)
                                   (λ i → inr (a , σ zero true i)) r i)
                   ; (j = i1) → inr (push (a , true) (i ∧ r))})
            (push (αₙ (a , true)) j)
  section-main (suc n) αₙ (inr (push a i)) j =
    hcomp (λ r → λ {(i = i0) → push (αₙ a) j
                   ; (i = i1) → compPath-filler (push (αₙ (fst a , ptSn (suc n))))
                                  (λ i₁ → inr (push (fst a , ptSn (suc n)) i₁)) i1 j
                   ; (j = i0) → S.BTC (suc n) αₙ
                                  (compPath-filler' (push (fst a))
                                    (λ i → inr (fst a , σ (suc n) (snd a) i)) r i)
                   ; (j = i1) → inr (push a i)})
    (hcomp (λ r → λ {(i = i0) → doubleCompPath-filler (push (αₙ a))
                                   (λ j → inr ((push a ∙ sym (push (fst a , ptSn (suc n)))) j))
                                   (sym (push (αₙ (fst a , ptSn (suc n))))) (~ j) (~ r)
                 ; (i = i1) → compPath-filler (push (αₙ (fst a , ptSn (suc n))))
                                               (λ i → inr (push (fst a , ptSn (suc n)) i)) r j
                 ; (j = i0) → S.BTC (suc n) αₙ (inr (fst a
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
    (αₙ : Fin mₙ × S₊ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where

  open BouquetFuns n mₙ αₙ e

  BouquetIso-gen : Iso (Pushout (terminal Cₙ) (invEq e ∘ inl)) (SphereBouquet (suc n) (Fin mₙ) .fst)
  Iso.fun BouquetIso-gen = CTB
  Iso.inv BouquetIso-gen = BTC
  Iso.rightInv BouquetIso-gen = CTB-BTC-cancel n mₙ αₙ e .fst
  Iso.leftInv BouquetIso-gen = CTB-BTC-cancel n mₙ αₙ e .snd

  Bouquet≃∙-gen : Pushout (terminal Cₙ) (invEq e ∘ inl) , inl tt
               ≃∙ SphereBouquet (suc n) (Fin mₙ)
  fst Bouquet≃∙-gen = isoToEquiv BouquetIso-gen
  snd Bouquet≃∙-gen = refl
