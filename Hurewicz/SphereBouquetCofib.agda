{-# OPTIONS --cubical #-}
module Hurewicz.SphereBouquetCofib where

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
open import Cubical.CW.Homology.Base
open import Cubical.CW.Subcomplex
open import Cubical.CW.Instances.SphereBouquetMap


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

open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.ChainComplex

open import Cubical.HITs.Sn.Degree
open import Cubical.Data.Int renaming (_·_ to _*_)

open Iso

-- open import Hurewicz.random


{-
File contains : a direct description of cell structure for cofibre
of a map α : ⋁ₐ Sⁿ → ⋁ₑ Sⁿ and a proof that Hₙ₊₁(cofib α) ≅ ℤ[e]/Im(deg α)
-}

-- -- Move to ShereBouqet
-- FinSphereBouquetMap : (c1 c2 : ℕ) (n : ℕ) → Type
-- FinSphereBouquetMap c1 c2 n =
--   SphereBouquet (suc n) (Fin c1) → SphereBouquet (suc n) (Fin c2)

-- -- Explicit definition of CW structure on the cofibre of a map of
-- -- (finite) sphere bouquets
-- module _ (c1 c2 : ℕ) {n : ℕ} where
--   SphereBouquet/FamGen : (α : FinSphereBouquetMap c1 c2 n)
--     → (m : ℕ) → Trichotomyᵗ m (suc (suc n)) → Type
--   SphereBouquet/FamGen a zero p = ⊥
--   SphereBouquet/FamGen a (suc m) (lt x) = Unit
--   SphereBouquet/FamGen  a (suc m) (eq x) = SphereBouquet (suc n) (Fin c2)
--   SphereBouquet/FamGen a (suc m) (gt x) = cofib a

--   SphereBouquet/CardGen : (m : ℕ)
--     → Trichotomyᵗ m (suc n) → Trichotomyᵗ m (suc (suc n)) → ℕ
--   SphereBouquet/CardGen zero p q = 1
--   SphereBouquet/CardGen (suc m) (lt x) q = 0
--   SphereBouquet/CardGen (suc m) (eq x) q = c2
--   SphereBouquet/CardGen (suc m) (gt x) (lt y) = 0
--   SphereBouquet/CardGen (suc m) (gt x) (eq y) = c1
--   SphereBouquet/CardGen (suc m) (gt x) (gt y) = 0

--   SphereBouquet/αGen : (α : FinSphereBouquetMap c1 c2 n) (m : ℕ)
--     (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
--     → Fin (SphereBouquet/CardGen m p q) × S⁻ m → SphereBouquet/FamGen α m q
--   SphereBouquet/αGen a (suc m) p (lt y) x = tt
--   SphereBouquet/αGen a (suc m) (eq x₂) (eq y) x = inl tt
--   SphereBouquet/αGen a (suc m) (gt x₂) (eq y) x =
--     a (inr (fst x , subst S₊ (cong predℕ y) (snd x)))
--   SphereBouquet/αGen a (suc m) p (gt y) x = inl tt

--   SphereBouquet/EqContrGen : (α : FinSphereBouquetMap c1 c2 n)
--     (m : ℕ) (m< : m <ᵗ suc n)
--     (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
--     → isContr (Pushout (SphereBouquet/αGen α m p q) fst)
--   SphereBouquet/EqContrGen a zero m< (lt x) (lt y) =
--     (inr fzero) , λ { (inr (zero , tt)) → refl}
--   SphereBouquet/EqContrGen a zero m< (lt x) (eq y) = ⊥.rec (snotz (sym y))
--   SphereBouquet/EqContrGen a zero m< (eq x) q = ⊥.rec (snotz (sym x))
--   SphereBouquet/EqContrGen a (suc m) m< (lt y) (lt x) =
--     (inl tt) , (λ {(inl tt) → refl})
--   SphereBouquet/EqContrGen a (suc m) m< (eq y) (lt x) =
--     ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) y m<))
--   SphereBouquet/EqContrGen a (suc m) m< (gt y) (lt x) =
--     ⊥.rec (¬m<ᵗm (<ᵗ-trans m< y))
--   SphereBouquet/EqContrGen a (suc m) m< p (eq x) =
--     ⊥.rec (falseDichotomies.lt-eq (m< , (cong predℕ x)))
--   SphereBouquet/EqContrGen a (suc m) m< p (gt x) =
--     ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x m<))

--   SphereBouquet/EqBottomMainGen : (α : FinSphereBouquetMap c1 c2 n)
--     → SphereBouquet (suc n) (Fin c2)
--      ≃ cofib {A = Fin c2 × S₊ n} {B = Fin c2} fst
--   SphereBouquet/EqBottomMainGen α = isoToEquiv
--       (compIso (pushoutIso _ _ _ _ (idEquiv _) (idEquiv Unit)
--                   (Σ-cong-equiv-snd (λ a → isoToEquiv (IsoSucSphereSusp n)))
--                   refl
--                   (funExt (λ a → ΣPathP (refl , IsoSucSphereSusp∙' n))))
--                (invIso (Iso-cofibFst-⋁ λ _ → S₊∙ n)))

--   SphereBouquet/EqBottomGen : (α : FinSphereBouquetMap c1 c2 n) (m : ℕ)
--     (r : m ≡ suc n) (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
--     → SphereBouquet (suc n) (Fin c2) ≃ Pushout (SphereBouquet/αGen α m p q) fst
--   SphereBouquet/EqBottomGen a m m< (lt x) q =
--     ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) m< x))
--   SphereBouquet/EqBottomGen a zero m< (eq x) (lt y) = ⊥.rec (snotz (sym x))
--   SphereBouquet/EqBottomGen a (suc m) m< (eq x) (lt y) =
--     compEquiv (SphereBouquet/EqBottomMainGen a)
--               (pathToEquiv λ i → cofib {A = Fin c2 × S₊ (predℕ (m< (~ i)))}
--                                         {B = Fin c2} fst)
--   SphereBouquet/EqBottomGen a m m< (eq x) (eq y) =
--     ⊥.rec (falseDichotomies.eq-eq (x , y))
--   SphereBouquet/EqBottomGen a m m< (eq x) (gt y) =
--     ⊥.rec (falseDichotomies.eq-gt (x , y))
--   SphereBouquet/EqBottomGen a m m< (gt x) q =
--     ⊥.rec (¬m<ᵗm (subst (suc n <ᵗ_) m< x))

--   SphereBouquet/EqTopGen' : (m : ℕ) (α : FinSphereBouquetMap c1 c2 n)
--     (p : m ≡ suc n)
--     → cofib α ≃ Pushout (α ∘ (λ x → inr (fst x , subst S₊ p (snd x)))) fst
--   SphereBouquet/EqTopGen' m a p =
--     compEquiv (compEquiv (symPushout _ _)
--               (pushoutEquiv _ _ _ _ (idEquiv _) (idEquiv _)
--                 (invEquiv (isContr→≃Unit (isContrLem c1 n m (sym p))))
--                 (λ i x → a x)
--                 λ i x → isContrLem c1 n m (sym p) .snd (inl x) i))
--               (invEquiv (isoToEquiv
--                 (Iso-PushoutComp-IteratedPushout
--                 (λ x → inr (fst x , subst S₊ p (snd x))) a)))
--     where
--     isContrLem : (c1 : ℕ) (n m : ℕ) (x : suc n ≡ m)
--      → isContr (Pushout {A = Fin c1 × S₊ m} {B = SphereBouquet (suc n) (Fin c1)}
--                          (λ x₂ → inr (fst x₂ , subst S₊ (sym x) (snd x₂))) fst)
--     isContrLem c1 n =
--       J> subst isContr
--         (λ i → Pushout {B = SphereBouquet (suc n) (Fin c1)}
--                        (λ x₂ → inr (fst x₂ , transportRefl (snd x₂) (~ i))) fst)
--          main
--        where
--        main : isContr (Pushout inr fst)
--        fst main = inl (inl tt)
--        snd main (inl (inl x)) = refl
--        snd main (inl (inr x)) =
--          (λ i → inl (push (fst x) i))
--           ∙ push (fst x , ptSn (suc n))
--           ∙ sym (push x)
--        snd main (inl (push a i)) j = lem i j
--          where
--          lem : Square refl ((λ i₁ → inl (push a i₁))
--                           ∙ push (a , ptSn (suc n))
--                           ∙ sym (push (a , ptSn (suc n))))
--                       refl λ i → inl (push a i)
--          lem = (λ i j → inl (push a (i ∧ j)))
--             ▷ (rUnit _
--              ∙ cong ((λ i₁ → inl (push a i₁)) ∙_)
--                     (sym (rCancel (push (a , ptSn (suc n))))))
--        snd main (inr x) = (λ i → inl (push x i)) ∙ push (x , ptSn (suc n))
--        snd main (push a i) j =
--          ((λ i₁ → inl (push (fst a) i₁))
--          ∙ compPath-filler (push (fst a , ptSn (suc n))) (sym (push a)) (~ i)) j

--   SphereBouquet/EqTopGen : (m : ℕ) (α : FinSphereBouquetMap c1 c2 n)
--     → suc n <ᵗ m → (p : Trichotomyᵗ m (suc n)) (q : Trichotomyᵗ m (suc (suc n)))
--     → cofib α ≃ Pushout (SphereBouquet/αGen α m p q) fst
--   SphereBouquet/EqTopGen (suc m) a m< (lt x) q = ⊥.rec (¬m<ᵗm (<ᵗ-trans m< x))
--   SphereBouquet/EqTopGen (suc m) a m< (eq x) q =
--     ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc m) (sym x) m<))
--   SphereBouquet/EqTopGen (suc m) a m< (gt x) (lt y) = ⊥.rec (¬squeeze (y , x))
--   SphereBouquet/EqTopGen (suc m) a m< (gt x) (eq y) =
--     SphereBouquet/EqTopGen' m a (cong predℕ y)
--   SphereBouquet/EqTopGen (suc m) a m< (gt x) (gt y) =
--     isoToEquiv (PushoutEmptyFam (λ()) λ())

--   SphereBouquet/EqGen : (m : ℕ) (α : FinSphereBouquetMap c1 c2 n)
--        (p : Trichotomyᵗ (suc m) (suc (suc n)))
--        (q : Trichotomyᵗ m (suc n)) (q' : Trichotomyᵗ m (suc (suc n)))
--     → (SphereBouquet/FamGen α (suc m) p)
--      ≃ Pushout (SphereBouquet/αGen α m q q') fst
--   SphereBouquet/EqGen m a (lt x) q q' =
--     invEquiv (isContr→≃Unit (SphereBouquet/EqContrGen a m x q q'))
--   SphereBouquet/EqGen m a (eq x) q q' =
--     SphereBouquet/EqBottomGen a m (cong predℕ x) q q'
--   SphereBouquet/EqGen m a (gt x) q q' = SphereBouquet/EqTopGen m a x q q'

--   ¬SphereBouquet/CardGen : (k : ℕ) (ineq : suc (suc n) <ᵗ k) (p : _) (q : _)
--     → ¬ (Fin (SphereBouquet/CardGen k p q))
--   ¬SphereBouquet/CardGen (suc k) ineq (eq x) q c =
--     falseDichotomies.eq-gt (x , ineq)
--   ¬SphereBouquet/CardGen (suc k) ineq (gt x) (eq y) c =
--     ¬m<ᵗm (subst (suc n <ᵗ_) (cong predℕ y) ineq)

--   SphereBouquet/ˢᵏᵉˡConverges : (k : ℕ) (α : FinSphereBouquetMap c1 c2 n)
--     → suc (suc n) <ᵗ k
--     → (p : _) (q : _)
--     → isEquiv {B = Pushout (SphereBouquet/αGen α k p q) fst} inl
--   SphereBouquet/ˢᵏᵉˡConverges k a ineq p q =
--     isoToIsEquiv (PushoutEmptyFam (¬SphereBouquet/CardGen k ineq p q ∘ fst)
--                                   (¬SphereBouquet/CardGen k ineq p q))

--   SphereBouquet/FamMidElementGen :
--     (k : ℕ) (α : FinSphereBouquetMap c1 c2 n)
--     → suc (suc n) ≡ k → (p : _)
--     → SphereBouquet (suc n) (Fin c2) ≃ (SphereBouquet/FamGen α k p)
--   SphereBouquet/FamMidElementGen k q s (lt x) =
--     ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) (sym s) x))
--   SphereBouquet/FamMidElementGen zero q s (eq x) = ⊥.rec (snotz (sym x))
--   SphereBouquet/FamMidElementGen (suc k) q s (eq x) = idEquiv _
--   SphereBouquet/FamMidElementGen k q s (gt x) =
--     ⊥.rec (¬m<ᵗm (subst (_<ᵗ k) s x))

--   SphereBouquet/FamTopElementGen : (k : ℕ) (α : FinSphereBouquetMap c1 c2 n)
--     → suc (suc n) <ᵗ k → (p : _)
--     → cofib α ≃ (SphereBouquet/FamGen α k p)
--   SphereBouquet/FamTopElementGen (suc k) α ineq (lt x) =
--     ⊥.rec (¬m<ᵗm (<ᵗ-trans x ineq))
--   SphereBouquet/FamTopElementGen (suc k) α ineq (eq x) =
--     ⊥.rec (¬m<ᵗm (subst (_<ᵗ k) (cong predℕ (sym x)) ineq))
--   SphereBouquet/FamTopElementGen (suc k) α ineq (gt x) = idEquiv _

-- SphereBouquet/EqBottomMainGenLem : {C : Type} {c1 c2 : ℕ} (n : ℕ)
--      (α : FinSphereBouquetMap c1 c2 n) {e : C ≃ _}
--   → (a : _) → Pushout→Bouquet (suc n) c2 (λ _ → tt) e
--                   (fst (SphereBouquet/EqBottomMainGen c1 c2 α) a)
--             ≡ a
-- SphereBouquet/EqBottomMainGenLem n α (inl x) = refl
-- SphereBouquet/EqBottomMainGenLem zero α (inr (a , base)) = push a
-- SphereBouquet/EqBottomMainGenLem {c1 = c1} {c2} zero α
--   {e = e} (inr (a , loop i)) j = main j i
--   where
--   main : Square (cong (Pushout→Bouquet 1 c2 (λ _ → tt) e)
--                      λ i → fst (SphereBouquet/EqBottomMainGen c1 c2 α)
--                                 (inr (a , loop i)))
--                 (λ i → inr (a , loop i))
--                 (push a) (push a)
--   main = cong-∙ (λ t → Pushout→Bouquet 1 c2 (λ _ → tt) e
--                           (⋁→cofibFst (λ _ → Bool , true) (inr (a , t))))
--                  (merid false)
--                  (sym (merid true))
--        ∙ cong₂ _∙_ refl (sym (rUnit _))
--        ∙ sym (assoc _ _ _)
--        ∙ sym (doubleCompPath≡compPath _ _ _)
--        ◁ symP (doubleCompPath-filler
--                 (push a) (λ i → inr (a , loop i)) (sym (push a)))
-- SphereBouquet/EqBottomMainGenLem (suc n) α (inr (a , north)) = push a
-- SphereBouquet/EqBottomMainGenLem (suc n) α (inr (a , south)) =
--   λ i → inr (a , merid (ptSn (suc n)) i)
-- SphereBouquet/EqBottomMainGenLem {c1 = c1} {c2} (suc n) α
--   {e = e} (inr (a , merid x i)) j = main j i
--   where
--   main : Square (cong (Pushout→Bouquet (suc (suc n)) c2 (λ _ → tt) e)
--                      λ i → fst (SphereBouquet/EqBottomMainGen c1 c2 α)
--                                 (inr (a , merid x i)))
--                 (λ i → inr (a , merid x i))
--                 (push a) λ i → inr (a , merid (ptSn (suc n)) i)
--   main =
--     (cong (push a ∙_)
--          (cong-∙ (inr ∘ (a ,_)) (merid x) (sym (merid (ptSn (suc n)))))
--         ∙ sym (doubleCompPath≡compPath _ _ _))
--        ◁ symP (doubleCompPath-filler
--               (push a)
--               (λ i → inr (a , merid x i))
--               λ i → inr (a , merid (ptSn (suc n)) (~ i)))
-- SphereBouquet/EqBottomMainGenLem {c1 = c1} {c2} zero α
--   {e = e} (push a i) j = lem j i
--   where
--   lem : Square (cong (Pushout→Bouquet (suc zero) c2 (λ _ → tt) e)
--                  (cong (fst (SphereBouquet/EqBottomMainGen c1 c2 α))
--                    (push a)))
--                (push a) refl (push a)
--   lem = cong (cong (Pushout→Bouquet (suc zero) c2 (λ _ → tt) e))
--               (cong (cong (inv (Iso-cofibFst-⋁ λ _ → S₊∙ zero)))
--                 (sym (lUnit _)))
--       ◁ λ i j → push a (i ∧ j)
-- SphereBouquet/EqBottomMainGenLem {c1 = c1} {c2} (suc n) α
--   {e = e} (push a i) j = lem j i
--   where
--   lem : Square (cong (Pushout→Bouquet (suc (suc n)) c2 (λ _ → tt) e)
--                  (cong (fst (SphereBouquet/EqBottomMainGen c1 c2 α))
--                    (push a)))
--                (push a) refl (push a)
--   lem = cong (cong (Pushout→Bouquet (suc (suc n)) c2 (λ _ → tt) e))
--               (cong (cong (inv (Iso-cofibFst-⋁ λ _ → S₊∙ (suc n))))
--                 (sym (lUnit _)))
--       ◁ λ i j → push a (i ∧ j)

-- -- Final product
-- module _ {c1 c2 : ℕ} {n : ℕ} (α : FinSphereBouquetMap c1 c2 n) where
--   private
--     α∙ : ∥ α (inl tt) ≡ inl tt ∥₁
--     α∙ = isConnectedSphereBouquet _

--   SphereBouquet/ˢᵏᵉˡ : CWskel ℓ-zero
--   fst SphereBouquet/ˢᵏᵉˡ m = SphereBouquet/FamGen c1 c2 α m (m ≟ᵗ (suc (suc n)))
--   fst (snd SphereBouquet/ˢᵏᵉˡ) m =
--     SphereBouquet/CardGen c1 c2 m (m ≟ᵗ suc n) (m ≟ᵗ suc (suc n))
--   fst (snd (snd SphereBouquet/ˢᵏᵉˡ)) m =
--     SphereBouquet/αGen c1 c2 α m (m ≟ᵗ suc n) (m ≟ᵗ suc (suc n))
--   fst (snd (snd (snd SphereBouquet/ˢᵏᵉˡ))) ()
--   snd (snd (snd (snd SphereBouquet/ˢᵏᵉˡ))) m =
--     SphereBouquet/EqGen c1 c2 m α
--       (suc m ≟ᵗ suc (suc n)) (m ≟ᵗ suc n) (m ≟ᵗ suc (suc n))

--   isCWSphereBouquet/ : isCW (cofib α)
--   fst isCWSphereBouquet/ = SphereBouquet/ˢᵏᵉˡ
--   snd isCWSphereBouquet/ =
--     compEquiv (SphereBouquet/FamTopElementGen c1 c2 (suc (suc (suc n))) α <ᵗsucm
--               ((suc (suc (suc n))) ≟ᵗ (suc (suc n))))
--       (isoToEquiv (converges→ColimIso (suc (suc (suc n)))
--       λ k → compEquiv (inl
--         , SphereBouquet/ˢᵏᵉˡConverges c1 c2 (k +ℕ suc (suc (suc n))) α
--            (<→<ᵗ (k , refl))
--            ((k +ℕ suc (suc (suc n))) ≟ᵗ suc n)
--            ((k +ℕ suc (suc (suc n))) ≟ᵗ suc (suc n)))
--         (invEquiv (SphereBouquet/EqGen c1 c2 (k +ℕ suc (suc (suc n)))
--                   α
--                   ((suc (k +ℕ suc (suc (suc n)))) ≟ᵗ suc (suc n))
--                   ((k +ℕ suc (suc (suc n))) ≟ᵗ suc n) _)) .snd))

--   SphereBouquet/ᶜʷ : CW ℓ-zero
--   fst SphereBouquet/ᶜʷ = cofib α
--   snd SphereBouquet/ᶜʷ = ∣ isCWSphereBouquet/ ∣₁

-- module _ {c1 c2 : ℕ} {n : ℕ} (α : FinSphereBouquetMap c1 c2 n) where
--   private
--     α∙ : ∥ α (inl tt) ≡ inl tt ∥₁
--     α∙ = isConnectedSphereBouquet _

--   ℤ[]/ImSphereMap : Group₀
--   ℤ[]/ImSphereMap = (AbGroup→Group ℤ[Fin c2 ])
--                   / (imSubgroup (bouquetDegree α)
--                   , isNormalIm (bouquetDegree α)
--                     λ _ _ → AbGroupStr.+Comm (snd ℤ[Fin c2 ]) _ _)

--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv :
--     (p : Trichotomyᵗ (suc n) (suc n)) (q :  Trichotomyᵗ (suc n) (suc (suc n)))
--     → ℤ[Fin c2 ] .fst → (Fin (SphereBouquet/CardGen c1 c2 (suc n) p q) → ℤ)
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv (lt x) q = λ _ _ → 0
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv (eq x) (lt y) = λ f → f
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv (eq x) (eq y) = λ f → f
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv (eq x) (gt y) = λ f → f
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv (gt x) q = λ _ _ → 0

--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun :
--     (p : Trichotomyᵗ (suc n) (suc n)) (q :  Trichotomyᵗ (suc n) (suc (suc n)))
--     → (Fin (SphereBouquet/CardGen c1 c2 (suc n) p q) → ℤ) → ℤ[Fin c2 ] .fst
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun (lt x) q = λ _ _ → 0
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun (eq x) (lt y) = λ f → f
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun (eq x) (eq y) = λ f → f
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun (eq x) (gt y) = λ f → f
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun (gt x) q = λ _ _ → 0

--   Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre :
--     (p : Trichotomyᵗ (suc n) (suc n)) (q :  Trichotomyᵗ (suc n) (suc (suc n)))
--     → Iso (Fin (SphereBouquet/CardGen c1 c2 (suc n) p q) → ℤ) (ℤ[Fin c2 ] .fst)
--   fun (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre p q) =
--     HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun p q
--   inv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre p q) =
--     HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv p q
--   rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (lt x) q) f =
--     ⊥.rec (¬m<ᵗm x)
--   rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (lt y)) f = refl
--   rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (eq y)) f = refl
--   rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (gt y)) f = refl
--   rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (gt x) q) f =
--     ⊥.rec (¬m<ᵗm x)
--   leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (lt x) q) f =
--     ⊥.rec (¬m<ᵗm x)
--   leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (lt y)) f = refl
--   leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (eq y)) f = refl
--   leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (eq x) (gt y)) f = refl
--   leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre (gt x) q) f =
--     ⊥.rec (¬m<ᵗm x)

--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun-hom :
--     (p : Trichotomyᵗ (suc n) (suc n)) (q :  Trichotomyᵗ (suc n) (suc (suc n)))
--     (x y : Fin (SphereBouquet/CardGen c1 c2 (suc n) p q) → ℤ)
--     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun p q (λ z → x z + y z)
--     ≡ λ z → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun p q x z
--            + HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun p q y z
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun-hom (lt _) _ _ _ = refl
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun-hom (eq _) (lt _) _ _ = refl
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun-hom (eq _) (eq _) _ _ = refl
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun-hom (eq _) (gt _) _ _ = refl
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun-hom (gt _) _ _ _ = refl

--   private
--     module _ (x : n ≡ n) where
--       EQ = compEquiv (SphereBouquet/EqBottomMainGen c1 c2 α)
--                      (pathToEquiv (λ i → cofib {A = Fin c2 × S₊ (x (~ i))} fst))

--       FIs : Iso _ _
--       FIs = BouquetIso-gen (suc n) c2 (λ _ → tt) EQ

--       F1 = fun (sphereBouquetSuspIso {A = Fin c2} {n = (suc n)})
--       F2' = fun FIs
--       F2 = suspFun F2'
--       F3 : Susp (SphereBouquet (suc n) (Fin c2)) → Susp (cofib (invEq EQ ∘ inl))
--       F3 = suspFun inr
--       F4 = δ-pre (invEq (SphereBouquet/EqTopGen' c1 c2 (suc n) α (cong suc x))
--                 ∘ inl)
--       F5 = F1 ∘ F2 ∘ F3 ∘ F4
--       F5' = F1 ∘ F2 ∘ F3

--   bouquetSusp→Charac : (a b : Fin c2 → ℤ) (t : α (inl tt) ≡ inl tt)
--     (x : _) → refl ≡ x
--     → F1 x ∘ F2 x ∘ F3 x ∘ F4 x
--     ∘ inv (BouquetIso-gen (suc (suc n)) c1
--            (λ w → α (inr (fst w , subst (S₊ ∘ suc) x (snd w))))
--            (SphereBouquet/EqTopGen' c1 c2 (suc n) α (cong suc x)))
--     ≡ bouquetSusp→ α
--   bouquetSusp→Charac a b αpt =
--     J> funExt λ { (inl x) → refl
--                   ; (inr (x , north)) → refl
--                   ; (inr (x , south)) → refl
--                   ; (inr (x , merid a i)) j → main αpt x a j i
--                   ; (push a i) → refl}
--     where
--     F2'≡id : (a : _) → F2' refl (inr a) ≡ a
--     F2'≡id a =
--       cong (Pushout→Bouquet (suc n) c2 (λ _ → tt)
--             (compEquiv (SphereBouquet/EqBottomMainGen c1 c2 α)
--             (pathToEquiv (λ i → cofib {A = Fin c2 × S₊ n} fst))))
--               (transportRefl (fst (SphereBouquet/EqBottomMainGen c1 c2 α) a))
--      ∙ SphereBouquet/EqBottomMainGenLem n α {e = EQ refl} a

--     main : (α (inl tt) ≡ inl tt) → (x : Fin c1) (a : S₊ (suc n))
--       → cong (F5 refl)
--              (push (α (inr (x , transport refl a)))
--              ∙∙ (λ i → inr (invEq (SphereBouquet/EqTopGen' c1 c2 (suc n) α refl)
--                          ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) i)))
--              ∙∙ sym (push (α (inr (x , transport refl (ptSn (suc n)))))))
--        ≡ Bouquet→ΩBouquetSusp (Fin c2) (λ _ → S₊∙ (suc n)) (α (inr (x , a)))
--     main apt x a =
--          cong-∙∙ (F5 refl) _ _ _
--        ∙ cong₃ _∙∙_∙∙_
--                (λ i → Bouquet→ΩBouquetSusp (Fin c2) (λ _ → S₊∙ (suc n))
--                          (F2' refl (inr (α (inr (x , transportRefl a i))))))
--                refl
--                ((λ j i
--                → F5 refl (push ((cong α
--                                ((λ j → inr (x , transportRefl (ptSn (suc n)) j))
--                             ∙  sym (push x)) ∙ apt) j) (~ i))))
--               ∙ (sym (compPath≡compPath' _ _) ∙ sym (rUnit _))
--        ∙ cong (Bouquet→ΩBouquetSusp (Fin c2) (λ _ → S₊∙ (suc n)))
--               (F2'≡id (α (inr (x , a))))

--   module _
--    (a b : Fin (SphereBouquet/CardGen c1 c2 (suc n)
--                  (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n))) → ℤ)
--    (ak : ∂ (SphereBouquet/ˢᵏᵉˡ α) n .fst a ≡ (λ _ → 0))
--    (bk : ∂ (SphereBouquet/ˢᵏᵉˡ α) n .fst b ≡ (λ _ → 0))
--    (r : Σ[ t ∈ (Fin (SphereBouquet/CardGen c1 c2 (suc (suc n))
--                      (suc (suc n) ≟ᵗ suc n) (suc (suc n) ≟ᵗ suc (suc n))) → ℤ) ]
--           ∂ (SphereBouquet/ˢᵏᵉˡ α) (suc n) .fst t ≡ λ q → a q - b q) where

--     pathlemma : Path (ℤ[]/ImSphereMap .fst)
--       [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun
--           (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) a ]
--       [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun
--           (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) b ]
--     pathlemma  with (n ≟ᵗ n) | (n ≟ᵗ suc n) | (suc n ≟ᵗ n)
--     ... | lt x | st | ah = ⊥.rec (¬m<ᵗm x)
--     ... | eq x | lt y | lt z = ⊥.rec (¬-suc-n<ᵗn z)
--     ... | eq x | lt y | eq z = ⊥.rec (falseDichotomies.eq-eq (x , sym z))
--     ... | eq x | lt y | gt z =
--       PT.rec (squash/ _ _) (λ apt →
--        eq/ _ _ ∣ (fst r)
--        , ((λ i → bouquetDegree α .fst (fst r))
--        ∙ funExt⁻ (cong fst (bouquetDegreeSusp α)) (fst r)
--        ∙ λ i → bouquetDegree (bouquetSusp→Charac a b apt x
--                                (isSetℕ _ _ refl x) (~ i)) .fst (fst r))
--        ∙ snd r ∣₁) α∙
--     ... | eq x | eq y | ah = ⊥.rec (falseDichotomies.eq-eq (x , y))
--     ... | eq x | gt y | ah = ⊥.rec (¬-suc-n<ᵗn y)
--     ... | gt x | st | ah = refl


--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap :
--     H̃ˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ α) (suc n) .fst → ℤ[]/ImSphereMap .fst
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap =
--     SQ.rec squash/
--       (λ f → [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun
--                  (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) (fst f) ])
--       λ {(a , ak) (b , bk) → PT.elim (λ _ → squash/ _ _)
--       λ {(t , s) → pathlemma a b ak bk (t , cong fst s)}}

--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-hom :
--     (x y : H̃ˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ α) (suc n) .fst)
--     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap
--        (GroupStr._·_ (H̃ˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ α) (suc n) .snd) x y)
--     ≡ GroupStr._·_ (ℤ[]/ImSphereMap .snd)
--                    (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap x)
--                    (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap y)
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-hom = SQ.elimProp2
--     (λ _ _ → squash/ _ _)
--     λ f g → cong [_] (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun-hom
--                        _ _ (fst f) (fst g))

--   ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/ :
--     ℤ[]/ImSphereMap .fst → H̃ˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ α) (suc n) .fst
--   ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/ =
--     SQ.rec squash/
--       (λ a → [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv
--                  (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) a
--              , cancel a ])
--       λ {a b → PT.elim (λ _ → squash/ _ _)
--         λ {(r , k) → PT.rec (squash/ _ _)
--               (λ apt → eq/ _ _
--                 ∣ lem apt a b r k .fst
--                , Σ≡Prop (λ _ → isOfHLevelPath' 1 (isSetΠ (λ _ → isSetℤ)) _ _)
--                         (lem apt a b r k .snd ) ∣₁) α∙}}
--     where
--     lem : (apt : α (inl tt) ≡ inl tt) (a b : Fin c2 → ℤ) (r : Fin c1 → ℤ)
--        → bouquetDegree α .fst r ≡ (λ x → a x + - b x)
--        → Σ[ w ∈ (Fin (SphereBouquet/CardGen c1 c2 (suc (suc n))
--                        (Trichotomyᵗ-suc (suc n ≟ᵗ n))
--                        ((Trichotomyᵗ-suc (Trichotomyᵗ-suc (n ≟ᵗ n))))) → ℤ) ]
--            ∂ (SphereBouquet/ˢᵏᵉˡ α) (suc n) .fst w
--            ≡ λ x → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv
--                       (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) a x
--                 - HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv
--                       (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) b x
--     lem apt a b r q with (n ≟ᵗ n) | (n ≟ᵗ suc n) | (suc n ≟ᵗ n)
--     ... | lt x | d | e = ⊥.rec (¬m<ᵗm x)
--     ... | eq x | lt y | lt z = ⊥.rec (¬-suc-n<ᵗn z)
--     ... | eq x | lt y | eq z = ⊥.rec (falseDichotomies.eq-eq (refl , sym z))
--     ... | eq x | lt y | gt z = r
--       , ((funExt⁻ (cong fst
--          (cong bouquetDegree (bouquetSusp→Charac a b apt x (isSetℕ _ _ refl x))
--          ∙ sym (bouquetDegreeSusp α))) r) ∙ q)
--     ... | eq x | eq y | e = ⊥.rec (falseDichotomies.eq-eq (refl , y))
--     ... | eq x | gt y | e = ⊥.rec (⊥.rec (¬-suc-n<ᵗn y))
--     ... | gt x | d | e = ⊥.rec (¬m<ᵗm x)

--     pre∂-vanish : (x : _)
--       → preboundary.pre∂ (SphereBouquet/ˢᵏᵉˡ α) zero x ≡ inl tt
--     pre∂-vanish (inl x) = refl
--     pre∂-vanish (inr (x , base)) = refl
--     pre∂-vanish (inr (x , loop i)) j = help j i
--       where
--       help :
--         cong (preboundary.isoSuspBouquet (SphereBouquet/ˢᵏᵉˡ α) zero)
--          (cong (suspFun (preboundary.isoCofBouquet (SphereBouquet/ˢᵏᵉˡ α) zero))
--           (cong (suspFun inr) (cong (δ 1 (SphereBouquet/ˢᵏᵉˡ α))
--            (cong (preboundary.isoCofBouquetInv↑ (SphereBouquet/ˢᵏᵉˡ α) zero)
--                      (λ i → inr (x , loop i))))))
--        ≡ refl {x = inl tt}
--       help = cong-∙∙
--         (preboundary.isoSuspBouquet (SphereBouquet/ˢᵏᵉˡ α) zero
--          ∘ suspFun (preboundary.isoCofBouquet (SphereBouquet/ˢᵏᵉˡ α) zero)
--          ∘ suspFun inr ∘  δ 1 (SphereBouquet/ˢᵏᵉˡ α)) _ _ _
--        ∙ ∙∙lCancel (sym
--             (cong (preboundary.isoSuspBouquet (SphereBouquet/ˢᵏᵉˡ α) zero)
--                    (merid (inr (fzero , false)))))
--     pre∂-vanish (push a i) = refl

--     ∂-zero : ∂ (SphereBouquet/ˢᵏᵉˡ α) zero ≡ trivGroupHom
--     ∂-zero = cong bouquetDegree (funExt pre∂-vanish) ∙ bouquetDegreeConst _ _ _

--     ∂-vanish : (m : ℕ) → m <ᵗ suc n → ∂ (SphereBouquet/ˢᵏᵉˡ α) m ≡ trivGroupHom
--     ∂-vanish zero p = ∂-zero
--     ∂-vanish (suc m) p = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
--       (funExt λ x → funExt λ y → ⊥.rec (¬bottom _ _ y))
--       where
--       ¬bottom : (p : _)(q : _) → ¬ Fin (SphereBouquet/CardGen c1 c2 (suc m) p q)
--       ¬bottom (lt x) q = ¬Fin0
--       ¬bottom (eq x) q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (cong predℕ x) p))
--       ¬bottom (gt x) q = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))

--     cancel : (a : Fin c2 → ℤ)
--       → ∂ (SphereBouquet/ˢᵏᵉˡ α) n .fst
--            ((HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv (suc n ≟ᵗ suc n)
--             (suc n ≟ᵗ suc (suc n)) a))
--        ≡ (λ _ → 0)
--     cancel a = funExt⁻ (cong fst (∂-vanish n <ᵗsucm))
--                      (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-inv
--                        (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) a)

--   GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap :
--     GroupIso (H̃ˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ α) (suc n)) ℤ[]/ImSphereMap
--   fun (fst GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap) =
--     HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap
--   inv (fst GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap) =
--     ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/
--   rightInv (fst GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap) =
--     SQ.elimProp (λ _ → squash/ _ _)
--       λ f → cong [_] (rightInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre
--                         (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n))) f)
--   leftInv (fst GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap) =
--     SQ.elimProp (λ _ → squash/ _ _)
--       λ f → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
--                       (leftInv (Iso-HₙSphereBouquetⁿ/-ℤ[]/ImSphereMap-pre
--                         (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n))) (fst f)))
--   snd GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap =
--     makeIsGroupHom HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-hom

--   fin→SphereBouquet/Cell : {n : ℕ} (p : _) (q : _)
--     → Fin c2 →  Fin (SphereBouquet/CardGen c1 c2 {n = n} (suc n) p q)
--   fin→SphereBouquet/Cell (lt y) q x = ⊥.rec (¬m<ᵗm y)
--   fin→SphereBouquet/Cell (eq y) q x = x
--   fin→SphereBouquet/Cell (gt y) q x = ⊥.rec (¬m<ᵗm y)

-- opaque
--   inKerGenerator : {c1 c2 : ℕ} {n : ℕ}
--       (α : FinSphereBouquetMap c1 c2 n) (k : Fin c2)
--     → bouquetDegree (preboundary.pre∂ (SphereBouquet/ˢᵏᵉˡ α) n) .fst
--         (ℤFinGenerator (fin→SphereBouquet/Cell α
--           (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) k))
--      ≡ λ _ → 0
--   inKerGenerator {n = n} α k = inKerAll α k _
--     where
--     inKerAll : {c1 c2 : ℕ} {n : ℕ}
--          (α : FinSphereBouquetMap c1 c2 n) (k : Fin c2) (t : _)
--       → bouquetDegree (preboundary.pre∂ (SphereBouquet/ˢᵏᵉˡ α) n) .fst t
--        ≡ (λ _ → 0)
--     inKerAll {c1 = c1} {c2 = c2} {n = n} α k =
--       funExt⁻ (cong fst (agreeOnℤFinGenerator→≡
--         {ϕ = bouquetDegree (preboundary.pre∂ (SphereBouquet/ˢᵏᵉˡ α) n)}
--         {trivGroupHom}
--         (BT n α)))
--         where
--         BT : (n : ℕ) (α : FinSphereBouquetMap c1 c2 n)
--           (x : Fin (preboundary.An+1 (SphereBouquet/ˢᵏᵉˡ α) n)) →
--               fst (bouquetDegree (preboundary.pre∂ (SphereBouquet/ˢᵏᵉˡ α) n))
--               (ℤFinGenerator x)
--             ≡ λ _ → pos zero
--         BT n α with (n ≟ᵗ n) | (n ≟ᵗ suc n)
--         ... | lt x | q = ⊥.rec (¬m<ᵗm x)
--         BT zero α | eq x | lt y =
--           λ q → funExt λ { (zero , snd₁)
--             → sumFinℤId _ (λ r → ·Comm (ℤFinGenerator q r) (pos zero))
--              ∙ sumFinℤ0 _}
--         BT (suc n) α | eq x | lt y = λ q → funExt λ x → ⊥.rec (snd x)
--         ... | eq x | eq y = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) y <ᵗsucm))
--         ... | eq x | gt y = ⊥.rec (¬-suc-n<ᵗn y)
--         ... | gt x | q = ⊥.rec (¬m<ᵗm x)

-- genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ : {c1 c2 n : ℕ}
--   (α : FinSphereBouquetMap c1 c2 n) (k : Fin c2)
--   → H̃ˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ α) (suc n) .fst
-- genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ α k =
--   [ ℤFinGenerator (fin→SphereBouquet/Cell α _ _ k)
--   , inKerGenerator α k ]

-- isGen-genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ : {c1 c2 n : ℕ}
--   (α : FinSphereBouquetMap c1 c2 n) (k : Fin c2)
--   → fun (fst (GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap α))
--              (genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ α k)
--    ≡ [ ℤFinGenerator k ]
-- isGen-genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ {n = n} α k
--   with (suc n ≟ᵗ suc (suc n)) | (n ≟ᵗ n)
-- ... | lt x | lt y = ⊥.rec (¬m<ᵗm y)
-- ... | lt x | eq y = refl
-- ... | lt x | gt y = ⊥.rec (¬m<ᵗm y)
-- ... | eq x | q = ⊥.rec (¬m<ᵗm (subst (suc n <ᵗ_) (sym x) <ᵗsucm))
-- ... | gt x | q = ⊥.rec (¬-suc-n<ᵗn x)
