{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.SphereBouquetCofib2 where

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

open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.HITs.Wedge


open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Hurewicz.random


{-
File contains : a direct description of cell structure for cofibre
of a map α : ⋁ₐ Sⁿ → ⋁ₑ Sⁿ and a proof that Hₙ₊₁(cofib α) ≅ ℤ[e]/Im(deg α)
-}

SphereBouquetMap : (c1 c2 : ℕ) (n : ℕ) → Type
SphereBouquetMap c1 c2 n = SphereBouquet (suc n) (Fin c1) → SphereBouquet (suc n) (Fin c2)

private
  isContrLem* : (c1 : ℕ) (n m : ℕ) (x : suc n ≡ m)
    → isContr (Pushout  {A = Fin c1 × S₊ m} {B = SphereBouquet (suc n) (Fin c1)}
                         (λ x₂ → inr (fst x₂ , subst S₊ (sym x) (snd x₂))) fst)
  isContrLem* c1 n =
    J> subst isContr (λ i → Pushout {B = SphereBouquet (suc n) (Fin c1)}
                       (λ x₂ → inr (fst x₂ , transportRefl (snd x₂) (~ i))) fst)
       main
     where
     main : isContr (Pushout inr fst)
     fst main = inl (inl tt)
     snd main (inl (inl x)) = refl
     snd main (inl (inr x)) =
       (λ i → inl (push (fst x) i))
        ∙ push (fst x , ptSn (suc n))
        ∙ sym (push x)
     snd main (inl (push a i)) j = lem i j
       where
       lem : Square refl ((λ i₁ → inl (push a i₁))
                        ∙ push (a , ptSn (suc n))
                        ∙ sym (push (a , ptSn (suc n))))
                    refl λ i → inl (push a i)
       lem = (λ i j → inl (push a (i ∧ j)))
          ▷ (rUnit _
           ∙ cong ((λ i₁ → inl (push a i₁)) ∙_)
                  (sym (rCancel (push (a , ptSn (suc n))))))
     snd main (inr x) = (λ i → inl (push x i)) ∙ push (x , ptSn (suc n))
     snd main (push a i) j =
       ((λ i₁ → inl (push (fst a) i₁))
       ∙ compPath-filler (push (fst a , ptSn (suc n))) (sym (push a)) (~ i)) j

module _ (c1 c2 : ℕ) {n : ℕ} where
  SphereBouquet/Fam* : (α : SphereBouquetMap c1 c2 n)
    → (m : ℕ) → Trichotomyᵗ m (suc (suc n)) → Type
  SphereBouquet/Fam* a zero p = ⊥
  SphereBouquet/Fam* a (suc m) (lt x) = Unit
  SphereBouquet/Fam*  a (suc m) (eq x) = SphereBouquet (suc n) (Fin c2)
  SphereBouquet/Fam* a (suc m) (gt x) = cofib a

  SphereBouquet/Card* : (m : ℕ)
    → Trichotomyᵗ m (suc n) → Trichotomyᵗ m (suc (suc n)) → ℕ
  SphereBouquet/Card* zero p q = 1
  SphereBouquet/Card* (suc m) (lt x) q = 0
  SphereBouquet/Card* (suc m) (eq x) q = c2
  SphereBouquet/Card* (suc m) (gt x) (lt x₁) = 0
  SphereBouquet/Card* (suc m) (gt x) (eq x₁) = c1
  SphereBouquet/Card* (suc m) (gt x) (gt x₁) = 0

  SphereBouquet/α* : (α : SphereBouquetMap c1 c2 n) (m : ℕ)
    (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
    → Fin (SphereBouquet/Card* m p q) × S⁻ m → SphereBouquet/Fam* α m q
  SphereBouquet/α* a (suc m) p (lt x₁) x = tt
  SphereBouquet/α* a (suc m) (eq x₂) (eq x₁) x = inl tt
  SphereBouquet/α* a (suc m) (gt x₂) (eq x₁) x = a (inr (fst x , subst S₊ (cong predℕ x₁) (snd x)))
  SphereBouquet/α* a (suc m) p (gt x₁) x = inl tt
  

  SphereBouquet/EqContr* : (α : SphereBouquetMap c1 c2 n) (m : ℕ) (m< : m <ᵗ suc n)
    (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
    → isContr (Pushout (SphereBouquet/α* α m p q) fst)
  SphereBouquet/EqContr* a zero m< (lt x) (lt x₁) =
    (inr fzero) , λ { (inr (zero , tt)) → refl}
  SphereBouquet/EqContr* a zero m< (lt x) (eq x₁) = ⊥.rec (snotz (sym x₁))
  SphereBouquet/EqContr* a zero m< (eq x) q = ⊥.rec (snotz (sym x))
  SphereBouquet/EqContr* a (suc m) m< (lt x₁) (lt x) = (inl tt) , (λ {(inl tt) → refl})
  SphereBouquet/EqContr* a (suc m) m< (eq x₁) (lt x) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) x₁ m<))
  SphereBouquet/EqContr* a (suc m) m< (gt x₁) (lt x) = ⊥.rec (¬m<ᵗm (<ᵗ-trans m< x₁))
  SphereBouquet/EqContr* a (suc m) m< p (eq x) =
    ⊥.rec (falseDichotomies.lt-eq (m< , (cong predℕ x)))
  SphereBouquet/EqContr* a (suc m) m< p (gt x) = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x m<))
  


  SphereBouquet/EqBottomMain* : (α : SphereBouquetMap c1 c2 n)
    → SphereBouquet (suc n) (Fin c2)
     ≃ cofib {A = Fin c2 × S₊ n} {B = Fin c2} fst
  SphereBouquet/EqBottomMain* α =
    isoToEquiv 
      (compIso (pushoutIso _ _ _ _ (idEquiv _) (idEquiv Unit)
                  (Σ-cong-equiv-snd (λ a → isoToEquiv (IsoSucSphereSusp n)))
                  refl
                  (funExt (λ a → ΣPathP (refl , IsoSucSphereSusp∙' n))))
               (invIso (Iso-cofibFst-⋁ λ _ → S₊∙ n)))

  SphereBouquet/EqBottom* : (α : SphereBouquetMap c1 c2 n) (m : ℕ) → (m ≡ suc n) →
      (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
    → SphereBouquet (suc n) (Fin c2) ≃ Pushout (SphereBouquet/α* α m p q) fst
  SphereBouquet/EqBottom* a m m< (lt x) q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) m< x))
  SphereBouquet/EqBottom* a zero m< (eq x) (lt x₁) = ⊥.rec (snotz (sym x))
  SphereBouquet/EqBottom* a (suc m) m< (eq x) (lt x₁) =
    compEquiv (SphereBouquet/EqBottomMain* a)
              (pathToEquiv λ i → cofib {A = Fin c2 × S₊ (predℕ (m< (~ i)))} {B = Fin c2} fst)
  SphereBouquet/EqBottom* a m m< (eq x) (eq x₁) = ⊥.rec (falseDichotomies.eq-eq (x , x₁))
  SphereBouquet/EqBottom* a m m< (eq x) (gt x₁) = ⊥.rec (falseDichotomies.eq-gt (x , x₁))
  SphereBouquet/EqBottom* a m m< (gt x) q = ⊥.rec (¬m<ᵗm (subst (suc n <ᵗ_) m< x))

  SphereBouquet/EqTop** : (m : ℕ) (α : SphereBouquetMap c1 c2 n) (p : m ≡ suc n)
    → cofib α ≃ Pushout (α ∘ (λ x → inr (fst x , subst S₊ p (snd x)))) fst
  SphereBouquet/EqTop** m a p =
    compEquiv (compEquiv (symPushout _ _)
              (pushoutEquiv _ _ _ _ (idEquiv _) (idEquiv _)
                (invEquiv (isContr→≃Unit (isContrLem* c1 n m (sym p))))
                (λ i x → a x)
                λ i x → isContrLem* c1 n m (sym p) .snd (inl x) i))
              (invEquiv (isoToEquiv
                (Iso-PushoutComp-IteratedPushout
                (λ x → inr (fst x , subst S₊ p (snd x))) a)))

  SphereBouquet/EqTop* : (m : ℕ) (α : SphereBouquetMap c1 c2 n)
    → suc n <ᵗ m → (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
    → cofib α ≃ Pushout (SphereBouquet/α* α m p q) fst
  SphereBouquet/EqTop* (suc m) a m< (lt x) q = ⊥.rec (¬m<ᵗm (<ᵗ-trans m< x))
  SphereBouquet/EqTop* (suc m) a m< (eq x) q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc m) (sym x) m<))
  SphereBouquet/EqTop* (suc m) a m< (gt x) (lt x₁) = ⊥.rec (¬squeeze (x₁ , x))
  SphereBouquet/EqTop* (suc m) a m< (gt x) (eq x₁) = SphereBouquet/EqTop** m a (cong predℕ x₁)
  SphereBouquet/EqTop* (suc m) a m< (gt x) (gt x₁) = isoToEquiv (PushoutEmptyFam (λ()) λ())

  SphereBouquet/Eq* : (m : ℕ) (α : SphereBouquetMap c1 c2 n)
       (p : Trichotomyᵗ (suc m) (suc (suc n)))
       (q : Trichotomyᵗ m (suc n)) (q' : Trichotomyᵗ m (suc (suc n)))
    → (SphereBouquet/Fam* α (suc m) p) ≃ Pushout (SphereBouquet/α* α m q q') fst
  SphereBouquet/Eq* m a (lt x) q q' =
    invEquiv (isContr→≃Unit (SphereBouquet/EqContr* a m x q q'))
  SphereBouquet/Eq* m a (eq x) q q' = SphereBouquet/EqBottom* a m (cong predℕ x) q q'
  SphereBouquet/Eq* m a (gt x) q q' = SphereBouquet/EqTop* m a x q q'

  ¬SphereBouquet/Card* : (k : ℕ) (ineq : suc (suc n) <ᵗ k) (p : _) (q : _)
    → ¬ (Fin (SphereBouquet/Card* k p q))
  ¬SphereBouquet/Card* (suc k) ineq (eq x) q c = falseDichotomies.eq-gt (x , ineq)
  ¬SphereBouquet/Card* (suc k) ineq (gt x) (eq x₁) c =
    ¬m<ᵗm (subst (suc n <ᵗ_) (cong predℕ x₁) ineq)

  SphereBouquet/ˢᵏᵉˡConverges : (k : ℕ) (α : SphereBouquetMap c1 c2 n)
    → suc (suc n) <ᵗ k 
    → (p : _) (q : _)
    → isEquiv {B = Pushout (SphereBouquet/α* α k p q) fst} inl
  SphereBouquet/ˢᵏᵉˡConverges k a ineq p q =
    isoToIsEquiv (PushoutEmptyFam (¬SphereBouquet/Card* k ineq p q ∘ fst)
                                  (¬SphereBouquet/Card* k ineq p q))

  SphereBouquet/FamTopElement* : (k : ℕ) (α : SphereBouquetMap c1 c2 n)
    → suc (suc n) <ᵗ k → (p : _)
    → cofib α ≃ (SphereBouquet/Fam* α k p)
  SphereBouquet/FamTopElement* (suc k) α ineq (lt x) = ⊥.rec (¬m<ᵗm (<ᵗ-trans x ineq))
  SphereBouquet/FamTopElement* (suc k) α ineq (eq x) =
    ⊥.rec (¬m<ᵗm (subst (_<ᵗ k) (cong predℕ (sym x)) ineq))
  SphereBouquet/FamTopElement* (suc k) α ineq (gt x) = idEquiv _

SphereBouquet/EqBottomMain*Lem : {C : Type} {c1 c2 : ℕ} (n : ℕ)
     (α : SphereBouquetMap c1 c2 n) {e : C ≃ _}
  → (a : _) → Pushout→Bouquet (suc n) c2 (λ _ → tt) e
                  (fst (SphereBouquet/EqBottomMain* c1 c2 α) a)
            ≡ a
SphereBouquet/EqBottomMain*Lem n α (inl x) = refl
SphereBouquet/EqBottomMain*Lem zero α (inr (a , base)) = push a
SphereBouquet/EqBottomMain*Lem {c1 = c1} {c2} zero α {e = e} (inr (a , loop i)) j = main j i
  where
  main : Square (cong (Pushout→Bouquet 1 c2 (λ _ → tt) e)
                     λ i → fst (SphereBouquet/EqBottomMain* c1 c2 α) (inr (a , loop i)))
                (λ i → inr (a , loop i))
                (push a) (push a)
  main = (cong-∙ (λ t → Pushout→Bouquet 1 c2 (λ _ → tt) e
                          (⋁→cofibFst (λ _ → Bool , true) (inr (a , t))))
                 (merid false)
                 (sym (merid true))
       ∙ cong₂ _∙_ refl (sym (rUnit _))
       ∙ sym (assoc _ _ _)
       ∙ sym (doubleCompPath≡compPath _ _ _))
       ◁ symP (doubleCompPath-filler (push a) (λ i → inr (a , loop i)) (sym (push a)))
SphereBouquet/EqBottomMain*Lem (suc n) α (inr (a , north)) = push a
SphereBouquet/EqBottomMain*Lem (suc n) α (inr (a , south)) = λ i → inr (a , merid (ptSn (suc n)) i)
SphereBouquet/EqBottomMain*Lem {c1 = c1} {c2} (suc n) α {e = e} (inr (a , merid x i)) j = main j i
  where
  main : Square (cong (Pushout→Bouquet (suc (suc n)) c2 (λ _ → tt) e)
                     λ i → fst (SphereBouquet/EqBottomMain* c1 c2 α) (inr (a , merid x i)))
                (λ i → inr (a , merid x i))
                (push a) λ i → inr (a , merid (ptSn (suc n)) i)
  main = (cong (push a ∙_) (cong-∙ (inr ∘ (a ,_)) (merid x) (sym (merid (ptSn (suc n)))))
        ∙ sym (doubleCompPath≡compPath _ _ _))
       ◁ symP (doubleCompPath-filler
              (push a)
              (λ i → inr (a , merid x i))
              λ i → inr (a , merid (ptSn (suc n)) (~ i)))
SphereBouquet/EqBottomMain*Lem {c1 = c1} {c2} zero α {e = e} (push a i) j = lem j i
  where
  lem : Square (cong (Pushout→Bouquet (suc zero) c2 (λ _ → tt) e)
                 (cong (fst (SphereBouquet/EqBottomMain* c1 c2 α))
                   (push a)))
               (push a) refl (push a) 
  lem = cong (cong (Pushout→Bouquet (suc zero) c2 (λ _ → tt) e))
              (cong (cong (Iso.inv (Iso-cofibFst-⋁ λ _ → S₊∙ zero)))
                (sym (lUnit _)))
      ◁ λ i j → push a (i ∧ j)
SphereBouquet/EqBottomMain*Lem {c1 = c1} {c2} (suc n) α {e = e} (push a i) j = lem j i
  where
  lem : Square (cong (Pushout→Bouquet (suc (suc n)) c2 (λ _ → tt) e)
                 (cong (fst (SphereBouquet/EqBottomMain* c1 c2 α))
                   (push a)))
               (push a) refl (push a) 
  lem = cong (cong (Pushout→Bouquet (suc (suc n)) c2 (λ _ → tt) e))
              (cong (cong (Iso.inv (Iso-cofibFst-⋁ λ _ → S₊∙ (suc n))))
                (sym (lUnit _)))
      ◁ λ i j → push a (i ∧ j)

module _ {c1 c2 : ℕ} {n : ℕ} (α : SphereBouquetMap c1 c2 n) where
  private
    α∙ : ∥ α (inl tt) ≡ inl tt ∥₁
    α∙ = isConnectedSphereBouquet _

  SphereBouquet/ˢᵏᵉˡ : CWskel ℓ-zero
  fst SphereBouquet/ˢᵏᵉˡ m = SphereBouquet/Fam* c1 c2 α m (m ≟ᵗ (suc (suc n)))
  fst (snd SphereBouquet/ˢᵏᵉˡ) m =
    SphereBouquet/Card* c1 c2 m (m ≟ᵗ suc n) (m ≟ᵗ suc (suc n))
  fst (snd (snd SphereBouquet/ˢᵏᵉˡ)) m =
    SphereBouquet/α* c1 c2 α m (m ≟ᵗ suc n) (m ≟ᵗ suc (suc n))
  fst (snd (snd (snd SphereBouquet/ˢᵏᵉˡ))) ()
  snd (snd (snd (snd SphereBouquet/ˢᵏᵉˡ))) m =
    SphereBouquet/Eq* c1 c2 m α (suc m ≟ᵗ suc (suc n)) (m ≟ᵗ suc n) (m ≟ᵗ suc (suc n))

  isCWSphereBouquet/ : isCW (cofib α)
  fst isCWSphereBouquet/ = SphereBouquet/ˢᵏᵉˡ
  snd isCWSphereBouquet/ = 
    compEquiv (SphereBouquet/FamTopElement* c1 c2 (suc (suc (suc n))) α <ᵗsucm
              ((suc (suc (suc n))) ≟ᵗ (suc (suc n))))
      (isoToEquiv (converges→ColimIso (suc (suc (suc n)))
      λ k → compEquiv (inl , SphereBouquet/ˢᵏᵉˡConverges c1 c2 (k +ℕ suc (suc (suc n))) α
                               (<→<ᵗ (k , refl))
                               ((k +ℕ suc (suc (suc n))) ≟ᵗ suc n)
                               ((k +ℕ suc (suc (suc n))) ≟ᵗ suc (suc n)))
        (invEquiv (SphereBouquet/Eq* c1 c2 (k +ℕ suc (suc (suc n)))
                  α
                  ((suc (k +ℕ suc (suc (suc n)))) ≟ᵗ suc (suc n))
                  ((k +ℕ suc (suc (suc n))) ≟ᵗ suc n) _)) .snd))

  SphereBouquet/ᶜʷ : CW ℓ-zero
  fst SphereBouquet/ᶜʷ = cofib α
  snd SphereBouquet/ᶜʷ = ∣ isCWSphereBouquet/ ∣₁

  open import Cubical.Algebra.Group.Subgroup
  ℤ[]/ImSphereMap : Group₀
  ℤ[]/ImSphereMap = (AbGroup→Group ℤ[Fin c2 ])
                  / (imSubgroup (bouquetDegree α)
                  , isNormalIm (bouquetDegree α)
                    λ _ _ → AbGroupStr.+Comm (snd ℤ[Fin c2 ]) _ _)

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv' :
    (p : Trichotomyᵗ (suc n) (suc n)) (q :  Trichotomyᵗ (suc n) (suc (suc n)))
    → ℤ[Fin c2 ] .fst → (Fin (SphereBouquet/Card* c1 c2 (suc n) p q) → ℤ)
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv' (lt x) q = λ _ _ → 0
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv' (eq x) (lt x₁) = λ f → f
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv' (eq x) (eq x₁) = λ f → f
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv' (eq x) (gt x₁) = λ f → f
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv' (gt x) q = λ _ _ → 0

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' :
    (p : Trichotomyᵗ (suc n) (suc n)) (q :  Trichotomyᵗ (suc n) (suc (suc n)))
    → (Fin (SphereBouquet/Card* c1 c2 (suc n) p q) → ℤ) → ℤ[Fin c2 ] .fst
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (lt x) q = λ _ _ → 0
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (eq x) (lt x₁) = λ f → f
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (eq x) (eq x₁) = λ f → f
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (eq x) (gt x₁) = λ f → f
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (gt x) q = λ _ _ → 0

  Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre :
    (p : Trichotomyᵗ (suc n) (suc n)) (q :  Trichotomyᵗ (suc n) (suc (suc n)))
    → Iso (Fin (SphereBouquet/Card* c1 c2 (suc n) p q) → ℤ) (ℤ[Fin c2 ] .fst)
  Iso.fun (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre p q) =
    HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' p q
  Iso.inv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre p q) =
    HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv' p q
  Iso.rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (lt x) q) f = ⊥.rec (¬m<ᵗm x)
  Iso.rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (lt x₁)) f = refl
  Iso.rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (eq x₁)) f = refl
  Iso.rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (gt x₁)) f = refl
  Iso.rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (gt x) q) f = ⊥.rec (¬m<ᵗm x)
  Iso.leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (lt x) q) f = ⊥.rec (¬m<ᵗm x)
  Iso.leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (lt x₁)) f = refl
  Iso.leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (eq x₁)) f = refl
  Iso.leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (gt x₁)) f = refl
  Iso.leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (gt x) q) f = ⊥.rec (¬m<ᵗm x)

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'-hom :
    (p : Trichotomyᵗ (suc n) (suc n)) (q :  Trichotomyᵗ (suc n) (suc (suc n)))
    (x y : Fin (SphereBouquet/Card* c1 c2 (suc n) p q) → ℤ)
    → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' p q (λ z → x z + y z)
    ≡ λ z → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' p q x z
           + HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' p q y z
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'-hom (lt x₁) q x y = refl
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'-hom (eq x₁) (lt x₂) x y = refl
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'-hom (eq x₁) (eq x₂) x y = refl
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'-hom (eq x₁) (gt x₂) x y = refl
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'-hom (gt x₁) q x y = refl

  module AHA (a b : Fin c2 → ℤ) where
    module _ (x : n ≡ n) where
      EQ = compEquiv (SphereBouquet/EqBottomMain* c1 c2 α)
                      (pathToEquiv (λ i → cofib {A = Fin c2 × S₊ (x (~ i))} fst))

      FIs : Iso _ _
      FIs = BouquetIso-gen (suc n) c2 (λ _ → tt) EQ

      F2' = Iso.fun FIs

      F2** = Pushout→Bouquet (suc n) c2 (λ _ → tt) EQ

      F1 = Iso.fun (sphereBouquetSuspIso {A = Fin c2} {n = (suc n)})
      F2 = suspFun F2'
      F3 : Susp (SphereBouquet (suc n) (Fin c2)) → Susp (cofib (invEq EQ ∘ inl))
      F3 = suspFun inr
      F4 = δ-pre ((invEq (SphereBouquet/EqTop** c1 c2 (suc n) α (cong suc x)) ∘ inl))
      F5 = F1 ∘ F2 ∘ F3 ∘ F4
      F5' = F1 ∘ F2 ∘ F3

    F2'≡id : (a : _) → F2' refl (inr a) ≡ a
    F2'≡id a = cong (Pushout→Bouquet (suc n) c2 (λ _ → tt)
                    (compEquiv (SphereBouquet/EqBottomMain* c1 c2 α)
                    (pathToEquiv (λ i → cofib {A = Fin c2 × S₊ n} fst))))
                      (transportRefl (fst (SphereBouquet/EqBottomMain* c1 c2 α) a))
             ∙ SphereBouquet/EqBottomMain*Lem n α
                 {e = EQ refl} a

    MaIn : (α (inl tt) ≡ inl tt) → (x : Fin c1) (a : S₊ (suc n))
      → cong (F5 refl)
             (push (α (inr (x , transport refl a)))
             ∙∙ (λ i → inr (invEq (SphereBouquet/EqTop** c1 c2 (suc n) α refl)
                         ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) i)))
             ∙∙ sym (push (α (inr (x , transport refl (ptSn (suc n)))))))
             ≡ Bouquet→ΩBouquetSusp (Fin c2) (λ _ → S₊∙ (suc n)) (α (inr (x , a)))
    MaIn apt x a = cong-∙∙ (F5 refl) _ _ _
             ∙ cong₃ _∙∙_∙∙_
                     (λ i → Bouquet→ΩBouquetSusp (Fin c2) (λ _ → S₊∙ (suc n))
                               (F2' refl (inr (α (inr (x , transportRefl a i))))))
                     refl
                     ((λ j i → F5 refl (push (((cong α ((λ j → inr (x , transportRefl (ptSn (suc n)) j))
                                                       ∙  sym (push x)) ∙ apt) j)) (~ i))))
                    ∙ (sym (compPath≡compPath' _ _) ∙ sym (rUnit _))
             ∙ cong (Bouquet→ΩBouquetSusp (Fin c2) (λ _ → S₊∙ (suc n)))
                    (F2'≡id (α (inr (x , a))))

    M : (α (inl tt) ≡ inl tt) → (x : _) → refl ≡ x
      → F1 x ∘ F2 x ∘ F3 x ∘ F4 x
      ∘ Iso.inv (BouquetIso-gen (suc (suc n)) c1 (λ x₃ → α (inr (fst x₃ , subst (S₊ ∘ suc) x (snd x₃))))
          (SphereBouquet/EqTop** c1 c2 (suc n) α (cong suc x)))
      ≡ bouquetSusp→ α 
    M αpt =
      J> funExt λ { (inl x) → refl
                    ; (inr (x , north)) → refl
                    ; (inr (x , south)) → refl
                    ; (inr (x , merid a i)) j → MaIn αpt x a j i
                    ; (push a i) → refl}


  module _ (a b : Fin (SphereBouquet/Card* c1 c2 (suc n) (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n))) → ℤ)
           (ak : ∂ SphereBouquet/ˢᵏᵉˡ n .fst a ≡ (λ _ → 0)) (bk : ∂ SphereBouquet/ˢᵏᵉˡ n .fst b ≡ (λ _ → 0))
           (r : Σ[ t ∈ (Fin (SphereBouquet/Card* c1 c2 (suc (suc n)) (suc (suc n) ≟ᵗ suc n) (suc (suc n) ≟ᵗ suc (suc n))) → ℤ) ]
                  ∂ SphereBouquet/ˢᵏᵉˡ (suc n) .fst t ≡ λ q → a q - b q) where

    main : Path (ℤ[]/ImSphereMap .fst)
             [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) a ]
            [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) b ]
    main  with (n ≟ᵗ n) | (n ≟ᵗ suc n) | (suc n ≟ᵗ n)
    ... | lt x | st | ah = ⊥.rec (¬m<ᵗm x)
    ... | eq x | lt x₁ | lt x₂ = ⊥.rec (¬-suc-n<ᵗn x₂)
    ... | eq x | lt x₁ | eq x₂ = ⊥.rec (falseDichotomies.eq-eq (x , sym x₂))
    ... | eq x | lt x₁ | gt x₂ = PT.rec (squash/ _ _) (λ apt →
      eq/ _ _ ∣ (fst r) , ((λ i → bouquetDegree α .fst (fst r))
                        ∙ funExt⁻ (cong fst (bouquetDegreeSusp α)) (fst r)
                        ∙ λ i → bouquetDegree (M apt x (isSetℕ _ _ refl x) (~ i)) .fst (fst r)) ∙ snd r ∣₁) α∙
      where
      module _ (x : n ≡ n) where
        EQ = compEquiv (SphereBouquet/EqBottomMain* c1 c2 α)
                        (pathToEquiv (λ i → cofib {A = Fin c2 × S₊ (x (~ i))} fst))

        FIs : Iso _ _
        FIs = BouquetIso-gen (suc n) c2 (λ _ → tt) EQ

        F2' = Iso.fun FIs

        F2** = Pushout→Bouquet (suc n) c2 (λ _ → tt) EQ

        F1 = Iso.fun sphereBouquetSuspIso
        F2 = suspFun F2'
        F3 = suspFun inr
        F4 = δ-pre ((invEq (SphereBouquet/EqTop** c1 c2 (suc n) α (cong suc x)) ∘ inl))
        F5 = F1 ∘ F2 ∘ F3 ∘ F4
        F5' = F1 ∘ F2 ∘ F3

      F2'≡id : (a : _) → F2' refl (inr a) ≡ a
      F2'≡id a = cong (Pushout→Bouquet (suc n) c2 (λ _ → tt)
                      (compEquiv (SphereBouquet/EqBottomMain* c1 c2 α)
                      (pathToEquiv (λ i → cofib {A = Fin c2 × S₊ n} fst))))
                        (transportRefl (fst (SphereBouquet/EqBottomMain* c1 c2 α) a))
               ∙ SphereBouquet/EqBottomMain*Lem n α
                   {e = EQ refl} a

      MaIn : (α (inl tt) ≡ inl tt) → (x : Fin c1) (a : S₊ (suc n))
        → cong (F5 refl)
               (push (α (inr (x , transport refl a)))
               ∙∙ (λ i → inr (invEq (SphereBouquet/EqTop** c1 c2 (suc n) α refl)
                           ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) i)))
               ∙∙ sym (push (α (inr (x , transport refl (ptSn (suc n)))))))
               ≡ Bouquet→ΩBouquetSusp (Fin c2) (λ _ → S₊∙ (suc n)) (α (inr (x , a)))
      MaIn apt x a = cong-∙∙ (F5 refl) _ _ _
               ∙ cong₃ _∙∙_∙∙_
                       (λ i → Bouquet→ΩBouquetSusp (Fin c2) (λ _ → S₊∙ (suc n))
                                 (F2' refl (inr (α (inr (x , transportRefl a i))))))
                       refl
                       ((λ j i → F5 refl (push (((cong α ((λ j → inr (x , transportRefl (ptSn (suc n)) j))
                                                         ∙  sym (push x)) ∙ apt) j)) (~ i))))
                      ∙ (sym (compPath≡compPath' _ _) ∙ sym (rUnit _))
               ∙ cong (Bouquet→ΩBouquetSusp (Fin c2) (λ _ → S₊∙ (suc n)))
                      (F2'≡id (α (inr (x , a))))

      M : (α (inl tt) ≡ inl tt) → (x : _) → refl ≡ x
        → F1 x ∘ F2 x ∘ F3 x ∘ F4 x
        ∘ Iso.inv (BouquetIso-gen (suc (suc n)) c1 (λ x₃ → α (inr (fst x₃ , subst (S₊ ∘ suc) x (snd x₃))))
            (SphereBouquet/EqTop** c1 c2 (suc n) α (cong suc x)))
        ≡ bouquetSusp→ α 
      M αpt =
        J> funExt λ { (inl x) → refl
                      ; (inr (x , north)) → refl
                      ; (inr (x , south)) → refl
                      ; (inr (x , merid a i)) j → MaIn αpt x a j i
                      ; (push a i) → refl}

    ... | eq x | eq x₁ | ah = ⊥.rec (falseDichotomies.eq-eq (x , x₁))
    ... | eq x | gt x₁ | ah = ⊥.rec (¬-suc-n<ᵗn x₁)
    ... | gt x | st | ah = refl


  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap : Hˢᵏᵉˡ SphereBouquet/ˢᵏᵉˡ n .fst → ℤ[]/ImSphereMap .fst
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap =
    SQ.rec squash/
      (λ f → [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) (fst f) ])
      λ {(a , ak) (b , bk) → PT.elim (λ _ → squash/ _ _) λ {(t , s) → main a b ak bk (t , cong fst s)}}

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-hom : (x y : Hˢᵏᵉˡ SphereBouquet/ˢᵏᵉˡ n .fst)
    → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap (GroupStr._·_ (Hˢᵏᵉˡ SphereBouquet/ˢᵏᵉˡ n .snd) x y)
    ≡ GroupStr._·_ (ℤ[]/ImSphereMap .snd)
                   (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap x)
                   (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap y)
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-hom = SQ.elimProp2
    (λ _ _ → squash/ _ _)
    λ f g → cong [_] (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'-hom _ _ (fst f) (fst g))

  ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/ : ℤ[]/ImSphereMap .fst → Hˢᵏᵉˡ SphereBouquet/ˢᵏᵉˡ n .fst
  ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/ =
    SQ.rec squash/
      (λ a → [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv'
                 (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) a
             , canc a ])
      λ {a b → PT.elim (λ _ → squash/ _ _)
        λ {(r , k) → PT.rec (squash/ _ _)
              (λ apt → eq/ _ _
                ∣ och apt a b r k .fst
               , Σ≡Prop (λ _ → isOfHLevelPath' 1 (isSetΠ (λ _ → isSetℤ)) _ _)
                        (och apt a b r k .snd ) ∣₁) α∙}}
    where
    och : (apt : α (inl tt) ≡ inl tt) (a b : Fin c2 → ℤ) (r : Fin c1 → ℤ)
       → bouquetDegree α .fst r ≡ (λ x → a x + - b x)
       → Σ[ w ∈ (Fin (SphereBouquet/Card* c1 c2 (suc (suc n))
                       (Trichotomyᵗ-suc (suc n ≟ᵗ n))
                       ((Trichotomyᵗ-suc (Trichotomyᵗ-suc (n ≟ᵗ n))))) → ℤ) ]
           ∂ SphereBouquet/ˢᵏᵉˡ (suc n) .fst w
           ≡ λ x → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv'
                      (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) a x
                - HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv'
                      (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) b x
    och apt a b r q with (n ≟ᵗ n) | (n ≟ᵗ suc n) | (suc n ≟ᵗ n)
    ... | lt x | d | e = ⊥.rec (¬m<ᵗm x)
    ... | eq x | lt x₁ | lt x₂ = ⊥.rec (¬-suc-n<ᵗn x₂)
    ... | eq x | lt x₁ | eq x₂ = ⊥.rec (falseDichotomies.eq-eq (refl , sym x₂))
    ... | eq x | lt x₁ | gt x₂ =
      r , ((funExt⁻ (cong fst (cong bouquetDegree (AHA.M a b apt x (isSetℕ _ _ refl x))
         ∙ sym (bouquetDegreeSusp α))) r) ∙ q)
    ... | eq x | eq x₁ | e = ⊥.rec (falseDichotomies.eq-eq (refl , x₁))
    ... | eq x | gt x₁ | e = ⊥.rec (⊥.rec (¬-suc-n<ᵗn x₁))
    ... | gt x | d | e = ⊥.rec (¬m<ᵗm x)

    bah : (x : _) → preboundary.pre∂ SphereBouquet/ˢᵏᵉˡ zero x ≡ inl tt
    bah (inl x) = refl
    bah (inr (x , base)) = refl
    bah (inr (x , loop i)) j = help j i
      where
      help : cong (preboundary.isoSuspBouquet SphereBouquet/ˢᵏᵉˡ zero)
               (cong (suspFun (preboundary.isoCofBouquet SphereBouquet/ˢᵏᵉˡ zero))
                 (cong (suspFun inr) (cong (δ 1 SphereBouquet/ˢᵏᵉˡ)
                  (cong (preboundary.isoCofBouquetInv↑ SphereBouquet/ˢᵏᵉˡ zero)
                    (λ i → inr (x , loop i))))))
           ≡ refl {x = inl tt}
      help = cong-∙∙ (preboundary.isoSuspBouquet SphereBouquet/ˢᵏᵉˡ zero
                    ∘ suspFun (preboundary.isoCofBouquet SphereBouquet/ˢᵏᵉˡ zero)
                    ∘ suspFun inr ∘  δ 1 SphereBouquet/ˢᵏᵉˡ)
                    _ _ _
           ∙ ∙∙lCancel (sym (cong (preboundary.isoSuspBouquet SphereBouquet/ˢᵏᵉˡ zero)
                                  (merid (inr (fzero , false)))))
    bah (push a i) = refl

    ∂-zero : ∂ SphereBouquet/ˢᵏᵉˡ zero ≡ trivGroupHom
    ∂-zero = cong bouquetDegree (funExt bah) ∙ bouquetDegreeConst _ _ _

    ∂-vanish : (m : ℕ) → m <ᵗ suc n → ∂ SphereBouquet/ˢᵏᵉˡ m ≡ trivGroupHom
    ∂-vanish zero p = ∂-zero
    ∂-vanish (suc m) p = Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt λ x → funExt λ y → ⊥.rec (negg _ _ y))
      where
      negg : (p : _)(q : _) →  ¬ Fin (SphereBouquet/Card* c1 c2 (suc m) p q)
      negg (lt x) q = ¬Fin0
      negg (eq x) q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (cong predℕ x) p))
      negg (gt x) q = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))

    canc : (a : Fin c2 → ℤ)
      → ∂ SphereBouquet/ˢᵏᵉˡ n .fst
           ((HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv' (suc n ≟ᵗ suc n)
            (suc n ≟ᵗ suc (suc n)) a))
       ≡ (λ _ → 0)
    canc a = funExt⁻ (cong fst (∂-vanish n <ᵗsucm))
                     (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv'
                       (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) a)

  GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap : GroupIso (Hˢᵏᵉˡ SphereBouquet/ˢᵏᵉˡ n) ℤ[]/ImSphereMap
  Iso.fun (fst GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap) = HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap
  Iso.inv (fst GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap) = ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/
  Iso.rightInv (fst GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap) =
    SQ.elimProp (λ _ → squash/ _ _)
      λ f → cong [_] (Iso.rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre
                        (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n))) f)
  Iso.leftInv (fst GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap) =
    SQ.elimProp (λ _ → squash/ _ _)
      λ f → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
                      (Iso.leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre
                        (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n))) (fst f)))
  snd GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap =
    makeIsGroupHom HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-hom
