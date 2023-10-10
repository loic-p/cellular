{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool hiding (_≤_)
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

open import prelude
open import freeabgroup

module spherebouquet where

--terminal map from any type to Unit
terminal : (A : Type) → A → Unit
terminal A x = tt

--a sphere bouquet is the wedge sum of A n-dimensional spheres
SphereBouquet : (n : ℕ) (A : Type) → Pointed₀
SphereBouquet n A = Pushout (terminal A) ((λ a → (a , ptSn n))) , inl tt

--the suspension of a n-dimensional bouquet is a (n+1)-dimensional bouquet
--here is the action of suspension on morphisms
bouquetSusp→ : {n : ℕ} {A B : Type} → (SphereBouquet n A →∙ SphereBouquet n B)
                                    → (SphereBouquet (suc n) A →∙ SphereBouquet (suc n) B)
bouquetSusp→ {n} {A} {B} f = {!!} , {!!}

--a morphisms between bouquets gives a morphisms of free abelian groups by taking degrees
bouquetDegree : {n : ℕ} {A B : Type} → (SphereBouquet n A →∙ SphereBouquet n B)
                                     → (AbGroupHom ℤ[ A ] ℤ[ B ])
bouquetDegree f = {!!}

--degree is compatible with composition
degreeComp : {n : ℕ} {A B C : Type} → (f : SphereBouquet n B →∙ SphereBouquet n C)
                                    → (g : SphereBouquet n A →∙ SphereBouquet n B)
                                    → bouquetDegree (f ∘∙ g) ≡ compGroupHom (bouquetDegree g) (bouquetDegree f)
degreeComp f g = {!!}

--the degree of a suspension is the same as the original degree
--in fact, ℤ[ A ] is basically the infinite suspension of a bouquet
degreeSusp : {n : ℕ} {A B : Type} → (f : SphereBouquet n A →∙ SphereBouquet n B)
                                  → bouquetDegree f ≡ bouquetDegree (bouquetSusp→ f)
degreeSusp f = {!!}


------------------
-- Equivalence between Bouquet of spheres and the cofibre
-- Dunno where to place this.

open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence

open import Cubical.Foundations.Function
open import Cubical.HITs.S1
open import Cubical.Foundations.Path

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
