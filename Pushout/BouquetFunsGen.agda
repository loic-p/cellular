{-# OPTIONS --cubical --lossy-unification --allow-unsolved-metas #-}
module Pushout.BouquetFunsGen where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.CW.Base
open import Cubical.CW.Map

open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
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

open import Cubical.Data.Nat

open import Cubical.CW.Properties
open import Cubical.Algebra.ChainComplex
open import Cubical.CW.ChainComplex
open import Cubical.CW.Homology
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Foundations.Pointed
open import Cubical.HITs.Wedge

open import Hurewicz.random
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Path


open import Pushout.Attempt5

private
  variable
    ℓ ℓ' : Level
preBTCGen : {A : Type ℓ'} {Cₙ Cₙ₊₁ : Type ℓ} (n : ℕ)
    (αₙ : A × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → (x : A)
    → S₊∙ n →∙ (cofib (invEq e ∘ inl) , inl tt)
fst (preBTCGen zero αₙ e x) false = inr (invEq e (inr x))
fst (preBTCGen zero αₙ e x) true = inl tt
fst (preBTCGen (suc zero) αₙ e x) base = inl tt
fst (preBTCGen (suc zero) αₙ e x) (loop i) =
    (push (αₙ (x , false))
  ∙∙ (λ j → inr (invEq e ((push (x , false) ∙ sym (push (x , true))) j)))
  ∙∙ sym (push (αₙ (x , true)))) i
fst (preBTCGen (suc (suc n)) αₙ e x) north = inl tt
fst (preBTCGen (suc (suc n)) αₙ e x) south = inl tt
fst (preBTCGen (suc (suc n)) αₙ e x) (merid a i) =
  (push (αₙ (x , a))
  ∙∙ (λ j → inr (invEq e ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) j)))
  ∙∙ sym (push (αₙ (x , ptSn (suc n))))) i
snd (preBTCGen zero αₙ e x) = refl
snd (preBTCGen (suc zero) αₙ e x) = refl
snd (preBTCGen (suc (suc n)) αₙ e x) = refl

module _  where
  Pushout→BouquetGen : {A : Type ℓ'} {Cₙ Cₙ₊₁ : Type ℓ} (n : ℕ)
    (αₙ : A × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → Pushout αₙ fst → SphereBouquet n A
  Pushout→BouquetGen n αₙ e (inl x) = inl tt
  Pushout→BouquetGen zero αₙ e (inr x) = inr (x , false)
  Pushout→BouquetGen (suc n) αₙ e (inr x) = inr (x , ptSn (suc n))
  Pushout→BouquetGen (suc n) αₙ e (push a i) =
    (push (a .fst) ∙ λ i → inr (a .fst , σSn n (a .snd) i)) i

-- Maps back and forth
module BouquetFunsGen {A : Type ℓ'} {Cₙ Cₙ₊₁ : Type ℓ} (n : ℕ)
    (αₙ : A × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where
  CTB : cofib (invEq e ∘ inl) → SphereBouquet n A
  CTB (inl x) = inl tt
  CTB (inr x) = Pushout→BouquetGen n αₙ e (fst e x)
  CTB (push a i) = Pushout→BouquetGen n αₙ e (secEq e (inl a) (~ i))

  BTC : SphereBouquet n A → cofib (invEq e ∘ inl)
  BTC (inl x) = inl tt
  BTC (inr x) = preBTCGen n αₙ e (fst x) .fst (snd x)
  BTC (push a i) = preBTCGen n αₙ e a .snd (~ i)

-- CTB≡ : ∀ {ℓ ℓ'} {A : Type ℓ'} {Cₙ Cₙ₊₁ : Type ℓ} (n : ℕ)
--     (αₙ : A × S⁻ n → Cₙ)
--     (e : Cₙ₊₁ ≃ Pushout αₙ fst) → {!(x : f) → ? ≡ ?!} → {!!}
-- CTB≡ = {!!}


open import Cubical.Foundations.Univalence
-- Maps cancel out
Gen-CTB-BTC-cancel : {A : Type ℓ} {Cₙ Cₙ₊₁ : Type ℓ} (n : ℕ)
    (αₙ : A × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → section (BouquetFunsGen.CTB n αₙ e) (BouquetFunsGen.BTC n αₙ e)
     × retract (BouquetFunsGen.CTB n αₙ e) (BouquetFunsGen.BTC n αₙ e)
Gen-CTB-BTC-cancel {A = A} {Cₙ = Cₙ} n αₙ =
    EquivJ (λ C₊ e →
      section (BouquetFunsGen.CTB n αₙ e)
      (BouquetFunsGen.BTC n αₙ e)
      ×
      retract (BouquetFunsGen.CTB n αₙ e)
      (BouquetFunsGen.BTC n αₙ e))
     (retr-main n αₙ , section-main n αₙ)
  where
  module S (n : ℕ) (αₙ : A × S⁻ n → Cₙ) where
    module T = BouquetFunsGen n αₙ (idEquiv _)
    open T public

  retr-inr : (n : ℕ) (αₙ : A × S⁻ n → Cₙ) (a : _) (b : _)
    → S.CTB n αₙ (S.BTC n αₙ (inr (a , b))) ≡ inr (a , b)
  retr-inr zero aₙ a false = refl
  retr-inr zero aₙ a true = push a
  retr-inr (suc zero) αₙ a base = push a
  retr-inr (suc zero) αₙ  a (loop i) j =
    hcomp (λ r →
      λ {(i = i0) → push a j
       ; (i = i1) → push a j
       ; (j = i0) → S.CTB (suc zero) αₙ
                      (doubleCompPath-filler
                        (push (αₙ (a , false)))
                        (λ j → inr ((push (a , false)
                                   ∙ sym (push (a , true))) j))
                        (sym (push (αₙ (a , true)))) r i)
       ; (j = i1) → inr (a , loop i)})
     (hcomp (λ r →
       λ {(i = i0) → push a j
        ; (i = i1) → compPath-filler' (push a) refl (~ j) (~ r)
        ; (j = i0) → S.CTB (suc zero) αₙ
                       (inr (compPath-filler
                               (push (a , false))
                               (sym (push (a , true))) r i))
        ; (j = i1) → inr (a , loop i)})
       (hcomp (λ r →
         λ {(i = i0) → push a (j ∨ ~ r)
          ; (i = i1) → inr (a , base)
          ; (j = i0) → compPath-filler' (push a) (λ j → inr (a , loop j)) r i
          ; (j = i1) → inr (a , loop i)})
        (inr (a , loop i))))
  retr-inr (suc (suc n)) αₙ a north = push a
  retr-inr (suc (suc n)) αₙ a south =
    push a ∙ λ j → inr (a , merid (ptSn (suc n)) j)
  retr-inr (suc (suc n)) αₙ a (merid a₁ i) j =
    hcomp (λ r →
      λ {(i = i0) → push a j
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
    (hcomp (λ r →
      λ {(i = i0) → push a j
       ; (i = i1) → compPath-filler' (push a)
                      (λ i → inr (a , σSn _ (ptSn (suc n)) i)) (~ j) (~ r)
       ; (j = i0) → S.CTB (suc (suc n)) αₙ
                       (inr (compPath-filler (push (a , a₁))
                             (sym (push (a , ptSn (suc n)))) r i) )
       ; (j = i1) → inr (a , help r i)})
        (hcomp (λ r → λ {(i = i0) → push a (j ∨ ~ r)
                      ; (i = i1) → inr (a , north)
                      ; (j = i0) → compPath-filler'
                                     (push a) (λ i → inr (a , σSn _ a₁ i)) r i
                      ; (j = i1) → inr (a , σSn _ a₁ i)})
               (inr (a , σSn _ a₁ i))))
    where
    help : Square (σSn _ a₁) (σSn _ a₁) refl (sym (σSn _ (ptSn (suc n))))
    help = flipSquare ((λ i _ → σSn _ a₁ i)
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
                           (λ i → inr (a , σSn zero false i)) r i)
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
                                   (λ i → inr (a , σSn zero true i)) r i)
                   ; (j = i1) → inr (push (a , true) (i ∧ r))})
            (push (αₙ (a , true)) j)
  section-main (suc (suc n)) αₙ (inr (push a i)) j =
    hcomp (λ r →
    λ {(i = i0) → push (αₙ a) j
     ; (i = i1) → (push (αₙ (fst a , ptSn (suc n)))
                ∙ (λ i₁ → inr (push (fst a , ptSn (suc n)) i₁))) j
     ; (j = i0) → S.BTC (suc (suc n)) αₙ
                    (compPath-filler' (push (fst a))
                      (λ i → inr (fst a , σSn (suc n) (snd a) i)) r i)
     ; (j = i1) → inr (push a i)})
    (hcomp (λ r →
      λ {(i = i0) → doubleCompPath-filler (push (αₙ a))
                    (λ j → inr ((push a ∙ sym (push (fst a , ptSn (suc n)))) j))
                    (sym (push (αₙ (fst a , ptSn (suc n))))) (~ j) (~ r)
       ; (i = i1) → compPath-filler (push (αₙ (fst a , ptSn (suc n))))
                        (λ i → inr (push (fst a , ptSn (suc n)) i)) r j
       ; (j = i0) → S.BTC (suc (suc n)) αₙ (inr (fst a
                   , compPath-filler' (merid (snd a))
                                      (sym (merid (ptSn (suc n)))) r i))
       ; (j = i1) → inr (compPath-filler'
                          (push a)
                          (sym (push (fst a , ptSn (suc n)))) (~ i) (~ r))})
    (hcomp (λ r
    → λ {(i = i0) → push (αₙ (fst a , ptSn (suc n))) (j ∨ ~ r)
        ; (i = i1) → push (αₙ (fst a , ptSn (suc n))) (j ∨ ~ r)
        ; (j = i1) → inr (inl (αₙ (fst a , ptSn (suc n))))})
       (inr (ugh (push (fst a , ptSn (suc n))) j i))))
    where
    ugh : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → p ∙' sym p ≡ refl
    ugh p = sym (compPath≡compPath' p (sym p)) ∙ rCancel p
  section-main n αₙ (push a i) j = push a (i ∧ j)


-- main theorem
module BouquetIso {A : Type ℓ} {Cₙ Cₙ₊₁ : Type ℓ} (n : ℕ)
    (αₙ : A × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where

  open BouquetFunsGen n αₙ e

  theIso : Iso (cofib (invEq e ∘ inl)) (SphereBouquet n (A))
  Iso.fun theIso = CTB
  Iso.inv theIso = BTC
  Iso.rightInv theIso = Gen-CTB-BTC-cancel n αₙ e .fst
  Iso.leftInv theIso = Gen-CTB-BTC-cancel n αₙ e .snd

  theEquiv : cofib (invEq e ∘ inl) ≃ SphereBouquet n (A)
  theEquiv = isoToEquiv theIso
