{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.random where

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
open import Cubical.CW.Homology.Base


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

open import Cubical.Homotopy.Group.LES
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace


open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup


open import Cubical.HITs.Truncation as TR

open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Abelianization.Properties as Abi
open import Cubical.Homotopy.Group.Properties

open import Cubical.Data.AbPath


open import Cubical.CW.Properties
open import Cubical.CW.Instances.Sn
open import Cubical.CW.Homology.Groups.Sn

-- module _ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
--   (f : S₊ n → fst X (suc n))
--   (f₀ : f (ptSn n) ≡ CWskel∙ X x₀ n) where
--   private
--     <ᵗ→0<ᵗ : {n m : ℕ} → n <ᵗ m → 0 <ᵗ m
--     <ᵗ→0<ᵗ {n} {suc m} _ = tt

--   cellMapSˢᵏᵉˡFunGenGen : ∀ k → (p : _) → Sgen.Sfam n k p → fst X k
--   cellMapSˢᵏᵉˡFunGenGen (suc k) (lt x₁) x = CWskel∙ X x₀ k
--   cellMapSˢᵏᵉˡFunGenGen (suc k) (eq x₁) x = subst (fst X) (sym x₁) (f x)
--   cellMapSˢᵏᵉˡFunGenGen (suc k) (gt x₁) x =
--     CW↪ X k (cellMapSˢᵏᵉˡFunGenGen k (k ≟ᵗ suc n) (Sn→SfamGen _ (<ᵗ→0<ᵗ x₁) x))

--   cellMapSˢᵏᵉˡFunGenGen∙ : ∀ k → (p : _)
--     → cellMapSˢᵏᵉˡFunGenGen (suc k) p (Sgen.Sfam∙ n k p) ≡ CWskel∙ X x₀ k
--   cellMapSˢᵏᵉˡFunGenGen∙ k (lt x) = refl
--   cellMapSˢᵏᵉˡFunGenGen∙ k (eq x) =
--     cong₂ (λ p q → subst (fst X) p q) (isSetℕ _ _ _ _) f₀ ∙ H _ (cong predℕ x)
--     where
--     H : (n : ℕ) (x : k ≡ n)
--       → subst (fst X) (cong suc (sym x)) (CWskel∙ X x₀ n) ≡ CWskel∙ X x₀ k
--     H = J> transportRefl _
--   cellMapSˢᵏᵉˡFunGenGen∙ (suc k) (gt x) =
--     cong (CW↪ X (suc k))
--       (cong (cellMapSˢᵏᵉˡFunGenGen (suc k) (Trichotomyᵗ-suc (k ≟ᵗ n)))
--             (Sn→SfamGen∙ (Trichotomyᵗ-suc (k ≟ᵗ n)))
--       ∙ cellMapSˢᵏᵉˡFunGenGen∙ k (suc k ≟ᵗ suc n))

--   cellMapSˢᵏᵉˡFunGenComm : (k : ℕ) (p : _) (q : _) (x : _)
--     → cellMapSˢᵏᵉˡFunGenGen (suc k) p (invEq (SαEqGen n k p q) (inl x))
--     ≡ CW↪ X k (cellMapSˢᵏᵉˡFunGenGen k q x)
--   cellMapSˢᵏᵉˡFunGenComm (suc k) (lt x₁) (lt x₂) x = refl
--   cellMapSˢᵏᵉˡFunGenComm (suc k) (lt x₁) (eq x₂) x =
--     ⊥.rec (¬-suc-n<ᵗn (subst (suc k <ᵗ_) (cong predℕ (sym x₂)) x₁))
--   cellMapSˢᵏᵉˡFunGenComm (suc k) (lt x₁) (gt x₂) x =
--     ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x₁ x₂))
--   cellMapSˢᵏᵉˡFunGenComm (suc k) (eq x₁) (lt x₂) x =
--     cong (subst (fst X) (sym x₁) ∘ f) (invEqSαEqGen∙ n k _ _)
--     ∙ cellMapSˢᵏᵉˡFunGenGen∙ (suc k) (eq x₁)
--   cellMapSˢᵏᵉˡFunGenComm k (eq x₁) (eq x₂) x =
--     ⊥.rec (falseDichotomies.eq-eq (refl , sym (x₁ ∙ sym x₂)))
--   cellMapSˢᵏᵉˡFunGenComm k (eq x₁) (gt x₂) x =
--     ⊥.rec (¬-suc-n<ᵗn {n} (subst (suc (suc n) <ᵗ_) x₁ x₂))
--   cellMapSˢᵏᵉˡFunGenComm k (gt x₁) (lt x₂) x = ⊥.rec (¬squeeze (x₁ , x₂))
--   cellMapSˢᵏᵉˡFunGenComm (suc k) (gt x₁) (eq x₂) x with (k ≟ᵗ n)
--   ... | lt x₃ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (cong predℕ x₂) x₃))
--   ... | eq x₃ = cong (CW↪ X (suc k))
--     (cong (subst (fst X) (cong suc (sym x₃))) (cong f (lem n x x₁ x₂))
--     ∙ cong (λ p → subst (fst X) p (f x))
--       (isSetℕ _ _ (cong suc (sym x₃)) (sym x₂)))
--     where
--     lem : (n : ℕ) (x : _) (x₁ : _) (x₂ : _)
--       → invEq (SαEqGen n (suc k) (gt x₁) (eq x₂)) (inl x) ≡ x
--     lem zero x x₁ x₂ = refl
--     lem (suc n) x x₁ x₂ = refl
--   ... | gt x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) (cong predℕ  x₂) x₃))
--   cellMapSˢᵏᵉˡFunGenComm (suc k) (gt x₁) (gt x₂) x with k ≟ᵗ n
--   ... | lt x₃ = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₂ x₃))
--   ... | eq x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₃ x₂))
--   ... | gt x₃ =
--     cong (CW↪ X (suc k))
--        (cong (CW↪ X k ∘ cellMapSˢᵏᵉˡFunGenGen k (k ≟ᵗ suc n))
--          (cong (λ w → Sn→SfamGen (k ≟ᵗ suc n) (<ᵗ→0<ᵗ w)
--            (invEq (SαEqGen n (suc k) (gt x₁) (gt x₂)) (inl x))) (isProp<ᵗ x₃ x₂)
--        ∙ cong (Sn→SfamGen (k ≟ᵗ suc n) (<ᵗ→0<ᵗ x₂))
--           (lem n k x₁ x₂ x (k ≟ᵗ suc n)))
--       ∙ cellMapSˢᵏᵉˡFunGenComm k (gt x₂) (k ≟ᵗ suc n) _)
--       where
--       lem : (n k : ℕ) (x₁ : _) (x₂ : _) (x : _) (w : _)
--         → invEq (SαEqGen n (suc k) (gt x₁) (gt x₂)) (inl x) ≡
--                          invEq (SαEqGen n k (gt x₂) w)
--                          (inl (Sn→SfamGen w (<ᵗ→0<ᵗ x₂) x))
--       lem n k x₁ x₂ x (lt x₃) = ⊥.rec (¬squeeze (x₂ , x₃))
--       lem zero (suc k) x₁ x₂ x (eq x₃) = refl
--       lem (suc n) (suc k) x₁ x₂ x (eq x₃) = refl
--       lem zero (suc k) x₁ x₂ x (gt x₃) = refl
--       lem (suc n) (suc k) x₁ x₂ x (gt x₃) = refl

--   cellMapSˢᵏᵉˡ : cellMap (Sˢᵏᵉˡ n) X
--   SequenceMap.map cellMapSˢᵏᵉˡ k = cellMapSˢᵏᵉˡFunGenGen k (k ≟ᵗ suc n)
--   SequenceMap.comm cellMapSˢᵏᵉˡ k x =
--     sym (cellMapSˢᵏᵉˡFunGenComm k (suc k ≟ᵗ suc n) (k ≟ᵗ suc n) x)

-- approxSphereMap∙ : ∀ {ℓ} (Xsk : CWskel ℓ) → (x₀ : fst Xsk (suc zero)) (n : ℕ)
--   (f : S₊∙ (suc n) →∙ (realise Xsk , incl x₀))
--   → ∃[ f' ∈ S₊∙ (suc n) →∙ (fst Xsk (suc (suc n)) , CWskel∙ Xsk x₀ (suc n)) ]
--       (incl∙ Xsk x₀ ∘∙ f' ≡ f)
-- approxSphereMap∙ Xsk x₀ n f =
--   PT.rec squash₁
--      (λ F → TR.rec squash₁
--               (λ fp → ∣ ((λ x → F x .fst .fst)
--                        , sym (cong fst fp))
--        , ΣPathP ((funExt (λ x → F x .fst .snd))
--        , (SQ' _ _ _ _ _ _ _ _ (cong snd fp))) ∣₁)
--      (F (ptSn (suc n)) .snd refl))
--      approxSphereMap
--   where
--   SQ' : ∀ {ℓ} {A : Type ℓ} (x y : A) (p : x ≡ y)
--         (z : A) (q : y ≡ z) (w : A) (r : x ≡ w) (t :  w ≡ z)
--     → Square (p ∙ q) t r refl → Square (sym r ∙ p) (sym q) t refl
--   SQ' x = J> (J> (J> λ t s → sym (rUnit refl)
--         ◁ λ i j → (rUnit refl ◁ s) (~ j) i))

--   approxSphereMap : ∥ ((x : S₊ (suc n))
--     → Σ[ fb ∈ fiber (CW↪∞ Xsk (suc (suc n))) (fst f x) ]
--                 ((p : ptSn (suc n) ≡ x)
--               → hLevelTrunc 1 (PathP (λ i
--                 → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
--                   ((CWskel∙ Xsk x₀ (suc n))
--                  , (CWskel∞∙Id Xsk x₀ (suc n) ∙ sym (snd f))) fb))) ∥₁
--   approxSphereMap = sphereToTrunc (suc n)
--     {λ x → Σ[ fb ∈ fiber (CW↪∞ Xsk (suc (suc n))) (fst f x) ]
--                 ((p : ptSn (suc n) ≡ x)
--      → hLevelTrunc 1 (PathP (λ i → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
--                   ((CWskel∙ Xsk x₀ (suc n))
--                  , (CWskel∞∙Id Xsk x₀ (suc n) ∙ sym (snd f))) fb) )}
--       λ a → TR.rec (isOfHLevelTrunc (suc (suc n)))
--       (λ fa → ∣ fa
--       , (λ p → J (λ a p → (fa : fiber (CW↪∞ Xsk (suc (suc n))) (fst f a))
--        → hLevelTrunc 1 (PathP (λ i → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
--            (CWskel∙ Xsk x₀ (suc n)
--            , CWskel∞∙Id Xsk x₀ (suc n) ∙ (λ i → snd f (~ i))) fa))
--                   (λ fa → isConnectedPathP 1 (isConnectedSubtr' n 2
--                            (isConnected-CW↪∞ (suc (suc n))
--                              Xsk (fst f (ptSn (suc n))))) _ _ .fst) p fa) ∣ₕ)
--       (isConnected-CW↪∞ (suc (suc n)) Xsk (fst f a) .fst)

-- module _ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
--   (faprx : S₊∙ n →∙ (fst X (suc n) , CWskel∙ X x₀ n))
--   (f : S₊∙ n →∙ (realise X , incl x₀))
--   (faprx≡ : (x : _) → incl {n = suc n} (fst faprx x) ≡ fst f x) where

--   cellMapSˢᵏᵉˡImproved : cellMap (Sˢᵏᵉˡ n) X
--   cellMapSˢᵏᵉˡImproved = cellMapSˢᵏᵉˡ X n x₀ (fst faprx) (snd faprx)

--   isApproxCellMapSˢᵏᵉˡImproved : realiseSequenceMap cellMapSˢᵏᵉˡImproved
--            ≡ fst f ∘ invEq (isCWSphere n .snd)
--   isApproxCellMapSˢᵏᵉˡImproved =
--     funExt λ x → cong (realiseSequenceMap cellMapSˢᵏᵉˡImproved)
--                        (sym (secEq (isCWSphere n .snd) x))
--                 ∙ lem _
--     where
--     lem : (x : _)
--       → realiseSequenceMap cellMapSˢᵏᵉˡImproved (fst (isCWSphere n .snd) x)
--        ≡ fst f x
--     lem x with (n ≟ᵗ n)
--     ... | lt x₁ = ⊥.rec (¬m<ᵗm x₁)
--     ... | eq x₁ = cong (incl {n = suc n})
--                   (cong (λ p → subst (fst X) p (fst faprx x))
--                    (isSetℕ _ _ _ refl)
--                 ∙ transportRefl (fst faprx x)) ∙ faprx≡ x
--     ... | gt x₁ = ⊥.rec (¬m<ᵗm x₁)

--   finCellApproxSˢᵏᵉˡImproved : (k : ℕ)
--     → finCellApprox (Sˢᵏᵉˡ n) X (fst f ∘ invEq (isCWSphere n .snd)) k
--   FinSequenceMap.fmap (fst (finCellApproxSˢᵏᵉˡImproved k)) =
--     SequenceMap.map cellMapSˢᵏᵉˡImproved ∘ fst
--   FinSequenceMap.fcomm (fst (finCellApproxSˢᵏᵉˡImproved k)) =
--     SequenceMap.comm cellMapSˢᵏᵉˡImproved ∘ fst
--   snd (finCellApproxSˢᵏᵉˡImproved k) = →FinSeqColimHomotopy _ _
--     (funExt⁻ isApproxCellMapSˢᵏᵉˡImproved ∘ FinSeqColim→Colim k ∘ (fincl flast))

open import Cubical.HITs.Sn.Degree

-- ∙Π∘∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
--   (n : ℕ) (f g : S₊∙ (suc n) →∙ A) (h : A →∙ B)
--   → h ∘∙ ∙Π f g ≡ ∙Π (h ∘∙ f) (h ∘∙ g)
-- ∙Π∘∙ {A = A} n f g h =
--      cong (h ∘∙_) (cong₂ ∙Π (sym (Iso.rightInv (sphereFunIso n) f))
--                             (sym (Iso.rightInv (sphereFunIso n) g)))
--   ∙∙ lem2 n (Iso.inv (sphereFunIso n) f) (Iso.inv (sphereFunIso n) g)
--   ∙∙ cong₂ (λ f g → ∙Π (h ∘∙ f) (h ∘∙ g))
--            (Iso.rightInv (sphereFunIso n) f)
--            (Iso.rightInv (sphereFunIso n) g)
--   where
--   lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → Square p refl (refl ∙ p) refl
--   lem p = lUnit p ◁ λ i j → (refl ∙ p) (i ∨ j)

--   mainEq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (a : A) (b : B)
--     (fp : f a ≡ b) (l1 l2 : a ≡ a)
--     → Square (cong f ((l1 ∙ refl) ∙ (l2 ∙ refl)))
--              ((sym (refl ∙ fp) ∙∙ cong f l1 ∙∙ (refl ∙ fp))
--             ∙ (sym (refl ∙ fp) ∙∙ cong f l2 ∙∙ (refl ∙ fp)))
--               fp fp
--   mainEq f a = J> λ l1 l2 → cong-∙ f _ _
--     ∙ cong₂ _∙_ (cong-∙ f l1 refl  ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
--                 (cong-∙ f l2 refl ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))

--   lem2 : (n : ℕ) (f g : S₊∙ n →∙ Ω A)
--     → (h ∘∙ ∙Π (Iso.fun (sphereFunIso n) f) (Iso.fun (sphereFunIso n) g))
--     ≡ ∙Π (h ∘∙ Iso.fun (sphereFunIso n) f) (h ∘∙ Iso.fun (sphereFunIso n) g)
--   fst (lem2 zero f g i) base = snd h i
--   fst (lem2 zero f g i) (loop i₁) =
--     mainEq (fst h) _ _ (snd h) (fst f false) (fst g false) i i₁
--   fst (lem2 (suc n) f g i) north = snd h i
--   fst (lem2 (suc n) f g i) south = snd h i
--   fst (lem2 (suc n) f g i) (merid a i₁) =
--     mainEq (fst h) _ _ (snd h)
--       (cong (Iso.fun (sphereFunIso (suc n)) f .fst) (σS a))
--       (cong (Iso.fun (sphereFunIso (suc n)) g .fst) (σS a)) i i₁
--   snd (lem2 zero f g i) j = lem (snd h) j i
--   snd (lem2 (suc n) f g i) j = lem (snd h) j i

-- cellMapSˢᵏᵉˡ∙Π : ∀ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
--   (faprx gaprx : S₊∙ (suc n) →∙ (fst X (suc (suc n)) , CWskel∙ X x₀ (suc n)))
--   (f : S₊∙ (suc n) →∙ (realise X , incl x₀))
--   (faprx≡ : incl∙ X x₀ ∘∙ faprx ≡ f)
--   (g : S₊∙ (suc n) →∙ (realise X , incl x₀))
--   (gaprx≡ : incl∙ X x₀ ∘∙ gaprx ≡ g)
--   → realiseCellMap (cellMapSˢᵏᵉˡImproved X (suc n) x₀ (∙Π faprx gaprx) (∙Π f g)
--       (λ x → funExt⁻ (cong fst (∙Π∘∙ n faprx gaprx (incl∙ X x₀))) x
--             ∙ λ i → ∙Π (faprx≡ i) (gaprx≡ i) .fst x))
--     ≡ (∙Π f g .fst ∘ invEq (isCWSphere (suc n) .snd))
-- cellMapSˢᵏᵉˡ∙Π X n x₀ faprx gaprx =
--   J> (J> funExt λ x → cong h (sym (secEq (isCWSphere (suc n) .snd) x))
--                      ∙ main _
--                      ∙ cong (∙Π (incl∙ X x₀ ∘∙ faprx) (incl∙ X x₀ ∘∙ gaprx) .fst)
--                          (retEq (SfamTopElement (suc n)) _))
--   where
--   h = realiseCellMap (cellMapSˢᵏᵉˡImproved X (suc n) x₀
--       (∙Π faprx gaprx) (∙Π (incl∙ X x₀ ∘∙ faprx) (incl∙ X x₀ ∘∙ gaprx))
--       (λ x → (funExt⁻ (cong fst (∙Π∘∙ n faprx gaprx (incl∙ X x₀))) x) ∙ refl))

--   main : (x : Sgen.Sfam (suc n) (suc (suc n)) (suc (suc n) ≟ᵗ suc (suc n)))
--        → h (incl {n = suc (suc n)} x)
--        ≡ ∙Π (incl∙ X x₀ ∘∙ faprx) (incl∙ X x₀ ∘∙ gaprx) .fst (invEq (SfamTopElement (suc n)) x)
--   main with (n ≟ᵗ n)
--   ... | lt x = ⊥.rec (¬m<ᵗm x)
--   ... | eq x = λ x
--     → cong (incl {n = suc (suc n)})
--          (cong (λ p → subst (fst X) p (fst (∙Π faprx gaprx) x)) (isSetℕ _ _ _ refl)
--           ∙ transportRefl _)
--       ∙ funExt⁻ (cong fst (∙Π∘∙ n faprx gaprx (incl∙ X x₀))) x
--   ... | gt x = ⊥.rec (¬m<ᵗm x)


--------------------------------------------

-- Cubical.Data.Nat.Order.Inductive
-- isPropTrichotomyᵗ : ∀ {n m : ℕ} → isProp (Trichotomyᵗ n m)
-- isPropTrichotomyᵗ {n = n} {m = m} (lt x) (lt x₁) i = lt (isProp<ᵗ x x₁ i)
-- isPropTrichotomyᵗ {n = n} {m = m} (lt x) (eq x₁) =
--   ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) x₁ x))
-- isPropTrichotomyᵗ {n = n} {m = m} (lt x) (gt x₁) = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ x))
-- isPropTrichotomyᵗ {n = n} {m = m} (eq x) (lt x₁) =
--   ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) x x₁))
-- isPropTrichotomyᵗ {n = n} {m = m} (eq x) (eq x₁) i = eq (isSetℕ n m x x₁ i)
-- isPropTrichotomyᵗ {n = n} {m = m} (eq x) (gt x₁) =
--   ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (sym x) x₁))
-- isPropTrichotomyᵗ {n = n} {m = m} (gt x) (lt x₁) = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ x))
-- isPropTrichotomyᵗ {n = n} {m = m} (gt x) (eq x₁) =
--   ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (sym x₁) x))
-- isPropTrichotomyᵗ {n = n} {m = m} (gt x) (gt x₁) i = gt (isProp<ᵗ x x₁ i)


-- Cubical.CW.Subcomplex
-- CW↪CommSubComplex : ∀ {ℓ} (C : CWskel ℓ) (m k : ℕ) →
--     CW↪ C m ∘ subComplex→map C k m
--   ≡ subComplex→map C k (suc m) ∘ CW↪ (subComplex C k) m
-- CW↪CommSubComplex C m k with (m ≟ᵗ k) | (suc m ≟ᵗ k)
-- ... | lt x | lt y = refl
-- ... | lt x | eq y = refl
-- ... | lt x | gt y = ⊥.rec (¬squeeze (x , y))
-- ... | eq x | lt y = ⊥.rec (¬m<ᵗm (subst (_<ᵗ k) x (<ᵗ-trans <ᵗsucm y)))
-- ... | eq x | eq y = ⊥.rec (¬m<ᵗm (subst (_<ᵗ_ m) (y ∙ (λ i → x (~ i))) <ᵗsucm))
-- ... | eq x | gt y = funExt λ s → help _ _ x y s (suc m ≟ᵗ suc k)
--   where
--   help : (m : ℕ) (k : ℕ) (x : m ≡ k) (y : k <ᵗ suc m) (s : fst C m) (p : _)
--     →  CW↪ C m s ≡ CW↑Gen C k (suc m) p y (transport refl (subst (fst C) x s))
--   help zero = λ k x y s → ⊥.rec (CW₀-empty C s)
--   help (suc m) = J> λ y s
--     → λ { (lt x) → ⊥.rec (¬squeeze (y , x))
--          ; (eq x) → cong (CW↪ C (suc m)) (sym (transportRefl s)
--               ∙ λ i → subst (fst C) (isSetℕ _ _ refl (cong predℕ (sym x)) i)
--                       (transportRefl (transportRefl s (~ i)) (~ i)))
--          ; (gt x) → ⊥.rec (¬m<ᵗm x) }
-- ... | gt x | lt y = ⊥.rec (¬squeeze (y , <ᵗ-trans x (<ᵗ-trans <ᵗsucm <ᵗsucm)))
-- ... | gt x | eq y =
--   ⊥.rec (¬m<ᵗm (transp (λ i → k <ᵗ y i) i0 (<ᵗ-trans x <ᵗsucm)))
-- ... | gt x | gt y = funExt λ a → help _ _ x y (suc m ≟ᵗ suc k) a
--   where
--   help : (m k : ℕ) (x : k <ᵗ m) (y : k <ᵗ suc m) (p : _) (a : _)
--     → CW↪ C m (CW↑Gen C k m  (m ≟ᵗ suc k) x a) ≡ CW↑Gen C k (suc m) p y a
--   help (suc m) zero x y p a = ⊥.rec (C .snd .snd .snd .fst a)
--   help (suc m) (suc k) x y (lt x₂) a = ⊥.rec (¬squeeze (y , x₂))
--   help (suc m) (suc k) x y (eq x₂) a =
--     ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) (sym (cong (predℕ ∘ predℕ) x₂)) x))
--   help (suc m) (suc k) x y (gt x₂) a =
--     cong (CW↪ C (suc m))
--       λ i → CW↑Gen C (suc k) (suc m)
--               (Trichotomyᵗ-suc (m ≟ᵗ suc k)) (isProp<ᵗ x x₂ i) a

-- CW↪SubComplexCharac : ∀ {ℓ} (C : CWskel ℓ) (m k : ℕ) (q : m <ᵗ k) →
--     CW↪ (subComplex C k) m
--   ≡ invEq (subComplex→Equiv C k (suc m) q)
--   ∘ CW↪ C m ∘ subComplex→map C k m
-- CW↪SubComplexCharac C m k q = funExt λ x
--   → sym (retEq (subComplex→Equiv C k (suc m) q) _)
--    ∙ cong (invEq (subComplex→Equiv C k (suc m) q))
--           (funExt⁻ (sym (CW↪CommSubComplex C m k)) x)

-- CW↑GenComm : ∀ {ℓ} (C : CWskel ℓ) (m n k : ℕ)
--   (p : Trichotomyᵗ n (suc m)) (t : m <ᵗ n)
--   → CW↑Gen C m n p t ∘ subComplex→map C k m
--   ≡ subComplex→map C k n ∘ CW↑Gen (subComplex C k) m n p t
-- CW↑GenComm C zero (suc n) k p t =
--   funExt λ x → (⊥.rec (G.subComplex₀-empty C k (0 ≟ᵗ k) x))
-- CW↑GenComm C (suc m) (suc n) k p t =
--   funExt (λ qa → (help n m k p _ t refl qa
--   ∙ cong ((subComplex→map C k (suc n) ∘
--        CW↑Gen (subComplex C k) (suc m) (suc n) p t)) (transportRefl qa)))
--   where
--   help : (n m k : ℕ) (p : _) (s : _) (t : _) (pp : s ≡ (suc m ≟ᵗ k))
--     → (x : G.subComplexFam C k (suc m) s) →
--          CW↑Gen C (suc m) (suc n) p t
--          (subComplexMapGen.subComplex→map' C k (suc m) s x)
--          ≡
--          subComplexMapGen.subComplex→map' C k (suc n) (suc n ≟ᵗ k)
--          (CW↑Gen (subComplex C k) (suc m) (suc n) p t (subst (G.subComplexFam C k (suc m)) pp x))
--   help (suc n) m k (lt y) s t pp x = ⊥.rec (¬squeeze (t , y))
--   help (suc n) m k (eq y) s t pp x = cong (CW↪ C (suc n))
--     (cong (λ p → subst (fst C) p
--       (subComplexMapGen.subComplex→map' C k (suc m) s x)) (isSetℕ _ _ _ _)
--     ∙ lem m (cong predℕ (cong predℕ y)) s (sym pp) x
--     ∙ cong (subComplex→map C k (suc n))
--         (cong (λ p → subst (subComplexFam C k) p
--           (subst (G.subComplexFam C k (suc m)) pp x))
--           (isSetℕ _ _ _ _)))
--     ∙ funExt⁻ (CW↪CommSubComplex C (suc n) k)
--         ((subst (λ m₁ → subComplexFam C k m₁) (cong predℕ (sym y))
--           (subst (G.subComplexFam C k (suc m)) pp x)))
--     where
--     lem : (m : ℕ) (y : n ≡ m) (s : _) (t : (suc m ≟ᵗ k) ≡ s) (x : _)
--       → subst (fst C) (cong suc (sym y)) (subComplexMapGen.subComplex→map' C k (suc m) s x)
--         ≡ subComplex→map C k (suc n)
--            (subst (subComplexFam C k) (cong suc (sym y))
--              (subst (G.subComplexFam C k (suc m)) (sym t) x))
--     lem = J> (J> λ x → transportRefl _ ∙ sym (cong (subComplex→map C k (suc n)) (transportRefl _ ∙ transportRefl x)))
--   help (suc n) m k (gt y) s t pp x =
--     cong (CW↪ C (suc n)) (help n m k (suc n ≟ᵗ suc (suc m)) s y pp x)
--     ∙ funExt⁻ (CW↪CommSubComplex C (suc n) k)
--       (CW↑Gen (subComplex C k) (suc m) (suc n) (suc n ≟ᵗ suc (suc m)) y
--          (subst (G.subComplexFam C k (suc m)) pp x))

-- subComplex→comm : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ)
--     (p : _) (q : _) (x : G.subComplexFam C n m p)
--   → CW↪ C m (subComplexMapGen.subComplex→map' C n m p x)
--   ≡ subComplexMapGen.subComplex→map' C n (suc m) q
--        (SubComplexGen.subComplexCW↪Gen C n m p q x)
-- subComplex→comm C m zero (eq y) s x = ⊥.rec (CW₀-empty C (subst (fst C) y x))
-- subComplex→comm C m zero (gt y) q x = ⊥.rec (CW₀-empty C x)
-- subComplex→comm C m (suc n) (lt y) (lt x₂) x = refl
-- subComplex→comm C m (suc n) (lt y) (eq x₂) x = refl
-- subComplex→comm C m (suc n) (lt y) (gt x₂) x = ⊥.rec (¬squeeze (y , x₂))
-- subComplex→comm C m (suc n) (eq y) (lt x₂) x =
--   ⊥.rec (¬m<ᵗm (transp (λ i → y i <ᵗ suc n) i0 (<ᵗ-trans <ᵗsucm x₂)))
-- subComplex→comm C m (suc n) (eq y) (eq x₂) x =
--   ⊥.rec ( falseDichotomies.eq-eq (sym y , sym x₂))
-- subComplex→comm C m (suc n) (eq y) (gt x₂) x with (m ≟ᵗ suc n)
-- ... | lt x₃ =  ⊥.rec (¬squeeze (x₂ , x₃))
-- ... | eq x₃ = cong (CW↪ C m) (sym (cong (subst (fst C) (sym x₃))
--                 (transportRefl _
--                 ∙ cong (λ p → subst (fst C) p x) (isSetℕ _ _ y x₃))
--                 ∙ subst⁻Subst (fst C) x₃ x))
-- ... | gt x₃ = ⊥.rec (¬m<ᵗm (subst (suc n <ᵗ_) y x₃))
-- subComplex→comm C m (suc n) (gt y) (lt x₂) x =
--   ⊥.rec (¬squeeze (x₂ , <ᵗ-trans y (<ᵗ-trans <ᵗsucm <ᵗsucm)))
-- subComplex→comm C m (suc n) (gt y) (eq x₂) x = (⊥.rec
--        (¬m<ᵗm (transp (λ i → suc n <ᵗ x₂ i) i0 (<ᵗ-trans y <ᵗsucm))))
-- subComplex→comm C (suc m) (suc n) (gt y) (gt x₂) x with m ≟ᵗ n
-- ... | lt x₃ = ⊥.rec (¬squeeze (x₂ , x₃))
-- ... | eq x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₃ y))
-- ... | gt x₃ = cong (CW↪ C (suc m))
--   λ j → CW↑Gen C (suc n) (suc m)
--           (Trichotomyᵗ-suc (m ≟ᵗ suc n)) (isProp<ᵗ y x₃ j) x

-- subComplex→Full : ∀ {ℓ} (C : CWskel ℓ) (m : ℕ) → cellMap (subComplex C m) C
-- SequenceMap.map (subComplex→Full C n) = subComplex→map C n
-- SequenceMap.comm (subComplex→Full C n) m = subComplex→comm C m n _ _

-- subComplex→ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) → finCellMap n (subComplex C m) C
-- FinSequenceMap.fmap (subComplex→ C m n) = subComplex→map C m ∘ fst
-- FinSequenceMap.fcomm (subComplex→ C m n) t = subComplex→comm C (fst t) m _ _

-- subComplexFam↓ : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _)
--   → G.subComplexFam C m (suc m) p → G.subComplexFam C m m q
-- subComplexFam↓ C m (lt x) q = ⊥.rec (¬-suc-n<ᵗn x)
-- subComplexFam↓ C m (eq x) q = ⊥.rec (falseDichotomies.eq-eq(refl , sym x))
-- subComplexFam↓ C m (gt x) (lt y) = ⊥.rec (¬m<ᵗm y)
-- subComplexFam↓ C m (gt x) (eq y) = idfun _
-- subComplexFam↓ C m (gt x) (gt y) = ⊥.rec (¬m<ᵗm y)

-- CW↪subComplexFam↓ : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _) (x : _)
--   → SubComplexGen.subComplexCW↪Gen C m m p q (subComplexFam↓ C m q p x) ≡ x
-- CW↪subComplexFam↓ C m p (lt y) x = ⊥.rec (¬-suc-n<ᵗn y)
-- CW↪subComplexFam↓ C m p (eq y) x = ⊥.rec (falseDichotomies.eq-eq(refl , sym y))
-- CW↪subComplexFam↓ C m (lt x₂) (gt y) x = ⊥.rec (¬m<ᵗm x₂)
-- CW↪subComplexFam↓ C m (eq x₂) (gt y) x =
--   transportRefl _ ∙ cong (λ p → subst (fst C) p x) (isSetℕ _ _ x₂ refl)
--                   ∙ transportRefl x
-- CW↪subComplexFam↓ C m (gt x₂) (gt y) x = ⊥.rec (¬m<ᵗm x₂)

-- subComplex→map'Charac : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _)
--   → subComplexMapGen.subComplex→map' C m (suc m) p
--    ≡ CW↪ C m ∘ subComplexMapGen.subComplex→map' C m m q ∘ subComplexFam↓ C m p q
-- subComplex→map'Charac C m p (lt x) = ⊥.rec (¬m<ᵗm x)
-- subComplex→map'Charac C m (lt y) (eq x) = ⊥.rec (¬-suc-n<ᵗn y)
-- subComplex→map'Charac C m (eq y) (eq x) =
--   ⊥.rec (falseDichotomies.eq-eq (refl , sym y))
-- subComplex→map'Charac C zero (gt y) (eq x) =
--   funExt (λ q → ⊥.rec (C .snd .snd .snd .fst q))
-- subComplex→map'Charac C (suc m) (gt y) (eq x) with (m ≟ᵗ m)
-- ... | lt x₂ =  ⊥.rec (¬m<ᵗm x₂)
-- ... | eq x₂ = funExt λ x
--   → cong (CW↪ C (suc m)) (cong (λ p → subst (fst C) p x) (isSetℕ _ _ _ _)
--     ∙ transportRefl x)
-- ... | gt x₂ =  ⊥.rec (¬m<ᵗm x₂)
-- subComplex→map'Charac C m p (gt x) = ⊥.rec (¬m<ᵗm x)

-- subComplexHomologyEquiv≡ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) (q : suc (suc n) <ᵗ m)
--   → Iso.inv (fst (subComplexHomology C m n q))
--    ≡ H̃ˢᵏᵉˡ→ (suc n) (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
-- subComplexHomologyEquiv≡ C m n q =
--   funExt (SQ.elimProp (λ _ → squash/ _ _)
--     λ a → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
--       (mainGen (suc n ≟ᵗ m) (suc (suc n) ≟ᵗ m) (fst a)
--       ∙ (λ i → bouquetDegree ((BouquetFuns.CTB (suc n) (C .snd .fst (suc n))
--        (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN))
--        ∘
--        f1/f2≡ i ∘
--        BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) (suc n ≟ᵗ m))
--        (G.subComplexα C m (suc n) (suc n ≟ᵗ m))
--        (G.subComplexFam≃Pushout C m (suc n) (suc n ≟ᵗ m)
--         (suc (suc n) ≟ᵗ m)))) .fst (fst a)))))
--     ∙ cong fst (sym (H̃ˢᵏᵉˡ→β (subComplex C m) C (suc n)
--                      {f = (incl ∘ Iso.inv (realiseSubComplex m C))}
--                  (help q)))
--   where
--   help' : (m : _)  (k : _) (q : _) →  finCellApprox (subComplex C m) C
--       (λ x → incl (Iso.inv (realiseSubComplex m C) x)) k
--   fst (help' m k q) = subComplex→ C m k
--   snd (help' m k q) = →FinSeqColimHomotopy _ _
--     λ x → CW↑Gen≡ C k (suc m) (suc m ≟ᵗ suc k) q _
--     ∙ cong (incl {n = suc m})
--            (funExt⁻ (CW↑GenComm C k (suc m) m (suc m ≟ᵗ suc k) q) x
--       ∙ funExt⁻ (subComplex→map'Charac C m (suc m ≟ᵗ m) (m ≟ᵗ m))
--               (CW↑Gen (subComplex C m) k (suc m) (Trichotomyᵗ-suc (m ≟ᵗ k)) q x)
--       ∙ cong (CW↪ C m) (sym (Iso.leftInv ( (realiseSubComplex m C) ) _)
--       ∙ cong (Iso.inv (realiseSubComplex m C))
--         ((push _ ∙ cong (incl {n = suc m})
--            (cong (CW↪ (subComplex C m) m)
--              (secEq (complex≃subcomplex' C m m <ᵗsucm (m ≟ᵗ m)) _)
--           ∙ CW↪subComplexFam↓ C m (m ≟ᵗ m) (suc m ≟ᵗ m) _))
--         ∙ sym (CW↑Gen≡ (subComplex C m) k (suc m) ((suc m) ≟ᵗ (suc k)) q x))))
--     ∙ sym (push _)

--   help : (q : suc (suc n) <ᵗ m) → finCellApprox (subComplex C m) C
--        (λ x → incl (Iso.inv (realiseSubComplex m C) x))
--       (suc (suc (suc (suc n))))
--   fst (help q) = subComplex→ C m (suc (suc (suc (suc n))))
--   snd (help q) with (suc (suc (suc n)) ≟ᵗ m)
--   ... | lt x = help' m (suc (suc (suc (suc n)))) x .snd
--   ... | eq x = funExt (subst (λ m → (x : _)
--     → FinSeqColim→Colim (suc (suc (suc (suc n))))
--          (finCellMap→FinSeqColim (subComplex C m) C
--           (subComplex→ C m (suc (suc (suc (suc n))))) x) ≡ incl
--          (Iso.inv (realiseSubComplex m C)
--           (FinSeqColim→Colim (suc (suc (suc (suc n)))) x))) x
--           (funExt⁻ (→FinSeqColimHomotopy _ _
--             λ w → (cong (incl {n = suc (suc (suc (suc n)))})
--                     (cong (subComplex→map C
--                             (suc (suc (suc n))) (suc (suc (suc (suc n)))))
--                       (sym (secEq (_ , subComplexFin C (suc (suc (suc n)))
--                                          (suc (suc (suc n)) , <ᵗsucm)) w)))
--             ∙ ((cong (incl {n = suc (suc (suc (suc n)))})
--                      (mm (suc (suc (suc n)))
--                        (Trichotomyᵗ-suc (Trichotomyᵗ-suc (Trichotomyᵗ-suc (suc n ≟ᵗ n))))
--                        (Trichotomyᵗ-suc (Trichotomyᵗ-suc (Trichotomyᵗ-suc (n ≟ᵗ n))))
--                        (invEq
--                          (CW↪ (subComplex C (suc (suc (suc n)))) (suc (suc (suc n))) ,
--                          subComplexFin C (suc (suc (suc n))) (suc (suc (suc n)) , <ᵗsucm))
--                        w))
--             ∙ sym (push (FinSequenceMap.fmap
--                           (fst (help' (suc (suc (suc n))) (suc (suc (suc n))) <ᵗsucm))
--                           (suc (suc (suc n)) , <ᵗsucm)
--                           (invEq
--                            (CW↪ (subComplex C (suc (suc (suc n)))) (suc (suc (suc n))) ,
--                             subComplexFin C (suc (suc (suc n))) (suc (suc (suc n)) , <ᵗsucm))
--                            w))))
--                    ∙ funExt⁻ (help' (suc (suc (suc n))) (suc (suc (suc n))) <ᵗsucm .snd)
--                              (fincl (suc (suc (suc n)) , <ᵗsucm)
--                              _)))
--             ∙ cong (incl {n = suc (suc (suc n))})
--                 (refl ∙
--                  (cong (Iso.inv (realiseSubComplex (suc (suc (suc n))) C))
--                    (push _
--                    ∙ cong (incl {n = suc (suc (suc (suc n)))})
--                    (secEq (_ , subComplexFin C (suc (suc (suc n))) (suc (suc (suc n)) , <ᵗsucm)) w)))))))
--     where
--     mmmain : (n : ℕ) (x₂ : _) (x : _)
--       → CW↑Gen C n (suc n) (eq (λ _ → suc n)) x₂ x ≡
--            snd (snd (snd (snd (snd C))) n) .equiv-proof (inl x) .fst .fst
--     mmmain zero x₂ x = ⊥.rec (C .snd .snd .snd .fst x)
--     mmmain (suc n) x₂ x = cong (CW↪ C (suc n)) (transportRefl x)
    
--     mm : (n : ℕ) (P : _) (Q : _) (x : _)
--       → subComplexMapGen.subComplex→map' C n (suc n) P
--           (invEq (G.subComplexFam≃Pushout C n n Q P) (inl x))
--       ≡ CW↪ C n (subComplexMapGen.subComplex→map' C n n Q x)
--     mm n P (lt y) x = ⊥.rec (¬m<ᵗm y)
--     mm n (lt x₂) (eq y) x = ⊥.rec (¬-suc-n<ᵗn x₂)
--     mm n (eq x₂) (eq y) x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) (sym x₂) <ᵗsucm))
--     mm n (gt x₂) (eq y) x = ah
--       where
--       ah :  CW↑Gen C n (suc n) (Trichotomyᵗ-suc (n ≟ᵗ n)) x₂
--          (invEq (G.subComplexFam≃Pushout C n n (eq y) (gt x₂)) (inl x))
--          ≡ CW↪ C n (idfun (fst C n) x)
--       ah with (n ≟ᵗ n)
--       ... | lt x = ⊥.rec (¬m<ᵗm x)
--       ... | eq q = cong₂ (λ p r → CW↑Gen C n (suc n) (eq p) x₂ (transport refl (subst (fst C) r x)))
--                          (isSetℕ _ _ _ refl) (isSetℕ _ _ _ refl)
--                          ∙ cong (CW↑Gen C n (suc n) (eq (λ _ → suc n)) x₂)
--                            (transportRefl _ ∙ transportRefl x)
--                          ∙ mmmain n x₂ x
--       ... | gt x = ⊥.rec (¬m<ᵗm x)
--     mm n P (gt y) x = ⊥.rec (¬m<ᵗm y)
--   ... | gt x = ⊥.rec (¬squeeze (q , x))

--   FIN : Fin (suc (suc (suc n)))
--   fst FIN = suc n
--   snd FIN = <ᵗ-trans {n = suc n} {m = suc (suc n)} {k = suc (suc (suc n))}
--                      <ᵗsucm <ᵗsucm

--   CTB* = BouquetFuns.CTB (suc n) (C .snd .fst (suc n))
--              (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN))

--   BTC* = BouquetFuns.CTB (suc n) (C .snd .fst (suc n))
--              (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN))

--   f1/f2gen :  (q1 : _) (q2 : _)
--     → cofib (invEq (G.subComplexFam≃Pushout C m (suc n) q1 q2) ∘ inl)
--     → Pushout (λ _ → tt) (invEq (C .snd .snd .snd .snd (fst FIN)) ∘ inl)
--   f1/f2gen q1 q2 (inl x) = inl x
--   f1/f2gen q1 q2 (inr x) =
--     inr (subComplexMapGen.subComplex→map' C m (suc (suc n)) q2 x)
--   f1/f2gen q1 q2 (push a i) =
--       (push (subComplexMapGen.subComplex→map' C m (suc n) q1 a)
--     ∙ λ i → inr (subComplex→comm C (suc n) m q1 q2 a i)) i

--   f1/f2≡ :  f1/f2gen (suc n ≟ᵗ m) (suc (suc n) ≟ᵗ m)
--          ≡ prefunctoriality.fn+1/fn (suc (suc (suc (suc n))))
--             (subComplex→ C m (suc (suc (suc (suc n)))))
--               ((suc n , <ᵗ-trans-suc (<ᵗ-trans (snd flast) <ᵗsucm)))
--   f1/f2≡ = funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl}

--   f1/f2genId : (q1 : _) (q2 : _) → f1/f2gen (lt q1) (lt q2) ≡ idfun _
--   f1/f2genId q1 q2 =
--     funExt λ { (inl x) → refl
--              ; (inr x) → refl
--              ; (push a i) j
--     → ((λ i → push a ∙ (λ j → inr (help2 m q1 q2 a i j)))
--                       ∙ sym (rUnit (push a))) j i}
--     where
--     help2 : (m : ℕ) (q1 : _) (q2 : _) (a : _)
--       → subComplex→comm C (suc n) m (lt q1) (lt q2) a ≡ refl
--     help2 (suc m) q1 q2 a = refl

--   mainGen : (q1 : _) (q2 : _) (a : _)
--     → Iso.inv (fst (subChainIsoGen C m (suc n , <ᵗ-trans <ᵗsucm q) q1)) a
--     ≡ bouquetDegree
--       (CTB* ∘ f1/f2gen q1 q2
--       ∘ (BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) q1)
--          (G.subComplexα C m (suc n) q1)
--            (G.subComplexFam≃Pushout C m (suc n) q1 q2))) .fst a
--   mainGen (lt x) (lt y) a =
--     funExt⁻ (sym (cong fst (bouquetDegreeId))) a
--     ∙ λ i → bouquetDegree (cool (~ i)) .fst a
--     where
--     cool : CTB* ∘ f1/f2gen (lt x) (lt y)
--          ∘ BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) (lt x))
--          (G.subComplexα C m (suc n) (lt x))
--            (G.subComplexFam≃Pushout C m (suc n) (lt x) (lt y))
--          ≡ idfun _
--     cool = funExt λ a → cong CTB*
--                   (funExt⁻ (f1/f2genId x y) _)
--                 ∙ CTB-BTC-cancel (suc n) (C .snd .fst (suc n))
--                    (C .snd .snd .fst (suc n))
--                    (C .snd .snd .snd .snd (fst FIN)) .fst _
--   mainGen (lt x) (eq y) a = ⊥.rec (¬m<ᵗm (subst (suc (suc n) <ᵗ_) (sym y) q))
--   mainGen (lt x) (gt y) a = ⊥.rec (¬squeeze (x , y))
--   mainGen (eq x) q2 a =
--     ⊥.rec (¬m<ᵗm  (subst (_<ᵗ_ (suc n)) (sym x) (<ᵗ-trans <ᵗsucm q)))
--   mainGen (gt x) q2 a =
--     ⊥.rec (¬m<ᵗm (<ᵗ-trans x (<ᵗ-trans <ᵗsucm q)))

-- subComplexHomologyEquiv : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (m : ℕ)
--   (p : suc (suc n) <ᵗ m)
--   → GroupEquiv (H̃ˢᵏᵉˡ (subComplex C m) (suc n))
--                 (H̃ˢᵏᵉˡ C (suc n))
-- fst (fst (subComplexHomologyEquiv C n m p)) =
--   H̃ˢᵏᵉˡ→ (suc n) (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
-- snd (fst (subComplexHomologyEquiv C n m p)) =
--   subst isEquiv (subComplexHomologyEquiv≡ C m n p)
--     (isoToIsEquiv (invIso (fst (subComplexHomology C m n p))))
-- snd (subComplexHomologyEquiv C n m p) =
--   H̃ˢᵏᵉˡ→ (suc n) (incl ∘ Iso.inv (realiseSubComplex m C)) .snd

-- -- H̃ᶜʷₙ Cₘ ≅ H̃ᶜʷₙ C∞ for n sufficiently small
-- subComplexHomologyᶜʷEquiv : ∀ {ℓ} (C : CWexplicit ℓ) (n : ℕ) (m : ℕ)
--   (p : suc (suc n) <ᵗ m)
--   → GroupEquiv (H̃ᶜʷ ((fst (fst (snd C))) m
--                        , ∣ subComplex (snd C .fst) m
--                        , isoToEquiv (realiseSubComplex m (snd C .fst)) ∣₁)
--                     (suc n))
--                 (H̃ᶜʷ (realise (snd C .fst)
--                        , ∣ fst (snd C)
--                        , idEquiv _ ∣₁)
--                     (suc n))
-- fst (subComplexHomologyᶜʷEquiv C n m p) =
--   H̃ᶜʷ→ (suc n) (incl {n = m}) .fst
--   , subComplexHomologyEquiv (snd C .fst) n m p .fst .snd
-- snd (subComplexHomologyᶜʷEquiv C n m p) =
--   H̃ᶜʷ→ (suc n) (incl {n = m}) .snd

-- --- bouquetDegreeHom


-- open import Cubical.HITs.Sn.Degree renaming (degreeConst to degree-const)

-- -- pickPetal

-- open import Cubical.ZCohomology.Groups.Sn
-- open import Cubical.ZCohomology.Base
-- open import Cubical.ZCohomology.GroupStructure


-- -- -- Sphere stuff
-- -- module _ {ℓ} (Xsk : CWskel ℓ) (x₀ : fst Xsk 1) where
-- --   fn+1/fn-SGen-inr : (n m : ℕ)
-- --     (f : S₊∙ n →∙ (fst Xsk (suc m) , CWskel∙ Xsk x₀ m))
-- --    → (p : _) → Sgen.Sfam n (suc (suc m)) p → fst Xsk (suc m)
-- --   fn+1/fn-SGen-inr n m f (lt x) = λ _ → CWskel∙ Xsk x₀ m
-- --   fn+1/fn-SGen-inr n m f (eq x) = fst f
-- --   fn+1/fn-SGen-inr n m f (gt x) = fst f

-- --   fn+1/fn-SGenEq : (n m : ℕ)
-- --     (f : S₊∙ n →∙ (fst Xsk (suc (suc m)) , CWskel∙ Xsk x₀ (suc m)))
-- --     (g : S₊∙ n →∙ (fst Xsk (suc m) , CWskel∙ Xsk x₀ m))
-- --     → (q : _) (a : Sgen.Sfam n (suc (suc m)) q)
-- --     →  fst Xsk (suc m)
-- --   fn+1/fn-SGenEq n m f g (lt x) a = CWskel∙ Xsk x₀ m
-- --   fn+1/fn-SGenEq n m f g (eq x) a = g .fst a
-- --   fn+1/fn-SGenEq n m f g (gt x) a = g .fst a
