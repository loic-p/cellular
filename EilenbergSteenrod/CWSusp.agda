{-# OPTIONS --cubical #-}
module EilenbergSteenrod.CWSusp where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.CW.Base

open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ : Level


module _ (ℓ : Level) (C : CWskel ℓ) where
  open CWskel-fields

  suspA : (ℕ → Type ℓ) → ℕ → Type ℓ
  suspA A zero = A zero
  suspA A (suc n) = Susp (A n)

  suspCells : (ℕ → ℕ) → ℕ → ℕ
  suspCells a zero = 2
  suspCells a (suc n) = a n

  -- suspMap is split in several functions because of the ad-hoc definition of S⁻
  suspMap₀ : Fin (suspCells (card C) 0) × (S⁻ 0) → suspA (fst C) 0
  suspMap₀ ()

  suspMap₁ : Fin (suspCells (card C) 1) × (S⁻ 1) → suspA (fst C) 1
  suspMap₁ (a , false) = north
  suspMap₁ (a , true) = south

  suspMapₛ : (n : ℕ) → Fin (suspCells (card C) (suc n)) × (Susp (S⁻ n)) → suspA (fst C) (suc n)
  suspMapₛ n (a , north) = north
  suspMapₛ n (a , south) = south
  suspMapₛ n (a , merid x i) = merid (α C n (a , x)) i

  suspMap : (n : ℕ) → Fin (suspCells (card C) n) × (S⁻ n) → suspA (fst C) n
  suspMap zero = suspMap₀
  suspMap 1 (a , x) = suspMapₛ 0 (a , Iso.fun BoolIsoSusp⊥ x)
  suspMap (suc (suc n)) (a , x) = suspMapₛ (suc n) (a , Iso.fun (IsoSucSphereSusp n) x)

  -- same for suspIso
  suspIso₀ : Iso (Susp (fst C 0)) (Pushout (suspMap₀) fst)
  Iso.fun suspIso₀ north = inr fzero
  Iso.fun suspIso₀ south = inr (fsuc fzero)
  Iso.fun suspIso₀ (merid a i) with (C .snd .snd .snd .fst a)
  Iso.fun suspIso₀ (merid a i) | ()
  Iso.inv suspIso₀ (inl a) with (C .snd .snd .snd .fst a)
  Iso.inv suspIso₀ (inl a) | ()
  Iso.inv suspIso₀ (inr (zero , xe)) = north
  Iso.inv suspIso₀ (inr (suc zero , xe)) = south
  Iso.rightInv suspIso₀ (inl a) with (C .snd .snd .snd .fst a)
  Iso.rightInv suspIso₀ (inl a) | ()
  Iso.rightInv suspIso₀ (inr (zero , tt)) = refl
  Iso.rightInv suspIso₀ (inr (suc zero , tt)) = refl
  Iso.leftInv suspIso₀ north = refl
  Iso.leftInv suspIso₀ south = refl
  Iso.leftInv suspIso₀ (merid a i) with (C .snd .snd .snd .fst a)
  Iso.leftInv suspIso₀ (merid a i) | ()

  suspEquiv₀ : Susp (fst C 0) ≃ Pushout (suspMap₀) fst
  suspEquiv₀ = isoToEquiv suspIso₀

  suspIsoₛ-fun : (n : ℕ) → (Susp (Pushout (α C n) fst)) → (Pushout (suspMapₛ n) fst)
  suspIsoₛ-fun n north = inl north
  suspIsoₛ-fun n south = inl south
  suspIsoₛ-fun n (merid (inl x) i) = inl (merid x i)
  suspIsoₛ-fun n (merid (inr a) i) = ((push (a , north)) ∙∙ refl ∙∙ (sym (push (a , south)))) i
  suspIsoₛ-fun n (merid (push (a , x) j) i) =
    hcomp (λ k → λ { (i = i0) → push (a , north) (j ∧ (~ k))
                   ; (i = i1) → push (a , south) (j ∧ (~ k))
                   ; (j = i0) → inl (merid (α C n (a , x)) i)
                   ; (j = i1) → doubleCompPath-filler (push (a , north)) refl (sym (push (a , south))) k i })
          (push (a , merid x i) j)

  suspIsoₛ-inv : (n : ℕ) → (Pushout (suspMapₛ n) fst) → (Susp (Pushout (α C n) fst))
  suspIsoₛ-inv n (inl north) = north
  suspIsoₛ-inv n (inl south) = south
  suspIsoₛ-inv n (inl (merid x i)) = merid (inl x) i
  suspIsoₛ-inv n (inr a) = south
  suspIsoₛ-inv n (push (a , north) i) = merid (inr a) i
  suspIsoₛ-inv n (push (a , south) i) = south
  suspIsoₛ-inv n (push (a , merid x j) i) =
    hcomp (λ k → λ { (i = i0) → merid (inl (α C n (a , x))) j
                   ; (i = i1) → merid (inr a) (j ∨ k)
                   ; (j = i0) → merid (inr a) (i ∧ k)
                   ; (j = i1) → south })
          (merid (push (a , x) i) j)

  suspIsoₛ-rightInv : (n : ℕ) → (x : Pushout (suspMapₛ n) fst) → suspIsoₛ-fun n (suspIsoₛ-inv n x) ≡ x
  suspIsoₛ-rightInv n (inl north) = refl
  suspIsoₛ-rightInv n (inl south) = refl
  suspIsoₛ-rightInv n (inl (merid a i)) = refl
  suspIsoₛ-rightInv n (inr a) t = push (a , south) t
  suspIsoₛ-rightInv n (push (a , north) i) t =
    hcomp (λ k → λ { (i = i0) → inl north
                   ; (i = i1) → doubleCompPath-filler (push (a , north)) refl (sym (push (a , south))) (~ t) k
                   ; (t = i0) → ((push (a , north)) ∙∙ refl ∙∙ (sym (push (a , south)))) (i ∧ k)
                   ; (t = i1) → push (a , north) i })
          (push (a , north) (t ∧ i))
  suspIsoₛ-rightInv n (push (a , south) i) t = push (a , south) (i ∧ t)
  suspIsoₛ-rightInv n (push (a , merid x j) i) t =
    hcomp (λ k → λ { (i = i0) → inl (merid (α C n (a , x)) j)
                   ; (i = i1) → doubleCompPath-filler (push (a , north)) refl (sym (push (a , south))) (~ t) (k ∨ j)
                   ; (j = i0) →
                        hfill (λ j → λ { (i = i0) → inl north
                                       ; (i = i1) → doubleCompPath-filler (push (a , north)) refl (sym (push (a , south))) (~ t) j
                                       ; (t = i0) → ((push (a , north)) ∙∙ refl ∙∙ (sym (push (a , south)))) (i ∧ j)
                                       ; (t = i1) → push (a , north) i })
                              (inS (push (a , north) (t ∧ i))) k
                   ; (j = i1) → push (a , south) (i ∧ t)
                   ; (t = i0) →
                        suspIsoₛ-fun n (hfill (λ t → λ { (i = i0) → merid (inl (α C n (a , x))) j
                                                       ; (i = i1) → merid (inr a) (j ∨ t)
                                                       ; (j = i0) → merid (inr a) (i ∧ t)
                                                       ; (j = i1) → south })
                                              (inS (merid (push (a , x) i) j)) k)
                   ; (t = i1) → push (a , merid x j) i })
          (hfill (λ k → λ { (i = i0) → inl (merid (α C n (a , x)) j)
                          ; (i = i1) → doubleCompPath-filler (push (a , north)) refl (sym (push (a , south))) k j
                          ; (j = i0) → push (a , north) (i ∧ (~ k))
                          ; (j = i1) → push (a , south) (i ∧ (~ k)) })
                 (inS (push (a , merid x j) i)) (~ t))

  suspIsoₛ-leftInv : (n : ℕ) → (x : Susp (Pushout (α C n) fst)) → suspIsoₛ-inv n (suspIsoₛ-fun n x) ≡ x
  suspIsoₛ-leftInv n north = refl
  suspIsoₛ-leftInv n south = refl
  suspIsoₛ-leftInv n (merid (inl x) i) = refl
  suspIsoₛ-leftInv n (merid (inr a) i) t =
    hcomp (λ j → λ { (t = i0) → suspIsoₛ-inv n (doubleCompPath-filler (push (a , north)) refl (sym (push (a , south))) j i)
                                ; (i = i1) → south
                                ; (i = i0) → merid (inr a) (~ t ∧ ~ j)
                                ; (t = i1) → merid (inr a) i })
                        (merid (inr a) (i ∨ ~ t))
  suspIsoₛ-leftInv n (merid (push (a , x) j) i) t =
    hcomp (λ k → λ { (i = i0) → merid (inr a) (j ∧ (~ t) ∧ (~ k))
                   ; (i = i1) → south
                   ; (j = i0) → merid (inl (α C n (a , x))) i
                   ; (j = i1) →
                      hfill (λ j → λ { (t = i0) → suspIsoₛ-inv n (doubleCompPath-filler (push (a , north)) refl
                                                                                                     (sym (push (a , south))) j i)
                                                  ; (i = i1) → south
                                                  ; (i = i0) → merid (inr a) (~ t ∧ ~ j)
                                                  ; (t = i1) → merid (inr a) i })
                                         (inS (merid (inr a) (i ∨ ~ t))) k
                   ; (t = i0) → suspIsoₛ-inv n (hfill (λ t → λ { (i = i0) → push (a , north) (j ∧ (~ t))
                                 ; (i = i1) → push (a , south) (j ∧ (~ t))
                                 ; (j = i0) → inl (merid (α C n (a , x)) i)
                                 ; (j = i1) → doubleCompPath-filler (push (a , north)) refl (sym (push (a , south))) t i })
                        (inS (push (a , merid x i) j)) k)
                   ; (t = i1) → merid (push (a , x) j) i })
          (hfill (λ k → λ { (j = i0) → merid (inl (α C n (a , x))) i
                          ; (j = i1) → merid (inr a) (i ∨ k)
                          ; (i = i0) → merid (inr a) (j ∧ k)
                          ; (i = i1) → south })
                (inS (merid (push (a , x) j) i)) (~ t))

  suspIsoₛ : (n : ℕ) → Iso (Susp (Pushout (α C n) fst)) (Pushout (suspMapₛ n) fst)
  suspIsoₛ n = iso (suspIsoₛ-fun n) (suspIsoₛ-inv n) (suspIsoₛ-rightInv n) (suspIsoₛ-leftInv n)

  suspEquivₛ : (n : ℕ) → Susp (fst C (suc n)) ≃ Pushout (suspMapₛ n) fst
  suspEquivₛ n = compEquiv (cong≃ Susp (e C n)) (isoToEquiv (suspIsoₛ n))

  -- here we want to conclude by saying that equivalent spans result in equivalent pushouts
  -- unfortunately I cant get Agda to infer the correct universe levels, ugh
  suspEquiv : (n : ℕ) → Susp (fst C n) ≃ Pushout (suspMap n) fst
  suspEquiv zero = suspEquiv₀
  suspEquiv (suc zero) = compEquiv (suspEquivₛ 0) {!!}
  suspEquiv (suc (suc n)) = compEquiv (suspEquivₛ (suc n)) {!!}

  suspSkel : CWskel ℓ
  suspSkel = suspA (fst C) , (suspCells (card C) , suspMap , (C .snd .snd .snd .fst) , suspEquiv)
