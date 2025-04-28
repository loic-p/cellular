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

-πᵃᵇinvDistr : ∀ {ℓ} {A : Pointed ℓ} (p q : ∥ Ωᵃᵇ A ∥₂) → -πᵃᵇ {x = pt A} (·πᵃᵇ p q) ≡ ·πᵃᵇ (-πᵃᵇ p) (-πᵃᵇ q)
-πᵃᵇinvDistr {A = A} p q =
  GroupTheory.invDistr (AbGroup→Group (π₁ᵃᵇAbGroup A)) p q
  ∙ ·πᵃᵇcomm _ _


--- Characterisation of maps Sⁿ -> cofib α for α : ⋁Sⁿ → VSⁿ
normalFormCofibFun : ∀ {n m k : ℕ}
  (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
  (f : S₊∙ (suc n) →∙ (cofib (fst α) , inl tt))
  → ∃[ f' ∈ S₊∙ (suc n) →∙ SphereBouquet∙ (suc n) (Fin k) ]
      (((inr , (λ i → inr (α .snd (~ i))) ∙ sym (push (inl tt))) ∘∙ f') ≡ f)
normalFormCofibFun {n = n} {m} {k} α f =
  PT.rec squash₁
    (λ g → TR.rec (isProp→isOfHLevelSuc n squash₁)
      (λ gid → ∣ ((λ x → g x .fst) , (cong fst gid))
               , ΣPathP ((λ i x → g x .snd i)
               , (lem _ _ _ _ _ _ _ _ _ _ (cong snd gid))) ∣₁)
      (isConnectedPath (suc n)
        (help (fst f (ptSn (suc n)))) (g (ptSn (suc n)))
          ((inl tt) , (((λ i → inr (α .snd (~ i))) ∙ sym (push (inl tt))) ∙ sym (snd f))) .fst))
    makefun
  where
  lem : ∀ {ℓ} {A : Type ℓ} (x y : A) (inrgid : x ≡ y) (z : _) (inrα : y ≡ z) (w : _) (pushtt : z ≡ w)
    (t : _) (snf : w ≡ t) (s : x ≡ t)
    → Square s ((inrα ∙ pushtt) ∙ snf) inrgid refl
    → Square (inrgid ∙ inrα ∙ pushtt) (sym snf) s refl
  lem x = J> (J> (J> (J> λ s sq → (sym (lUnit _) ∙ sym (rUnit _))
    ◁ λ i j → (sq ∙ sym (rUnit _) ∙ sym (rUnit _)) j i)))
  cool : (x : S₊ (suc n)) → Type
  cool x =
    Σ[ x' ∈ SphereBouquet (suc n) (Fin k) ]
      Σ[ y ∈ ((ptSn (suc n) ≡ x) → inl tt ≡ x') ]
        Σ[ feq ∈ inr x' ≡ fst f x ]
          ((p : ptSn (suc n) ≡ x)
            → Square ((λ i → inr (snd α (~ i))) ∙ sym (push (inl tt))) (snd f)
                      ((λ i → inr (y p i)) ∙∙ feq ∙∙ cong (fst f) (sym p)) refl)

  inr' : SphereBouquet (suc n) (Fin k) → cofib (fst α)
  inr' = inr

  help : isConnectedFun (suc (suc n)) inr'
  help = inrConnected _ _ _ (isConnected→isConnectedFun _ isConnectedSphereBouquet')

  makefun : ∥ ((x : _) → Σ[ x' ∈ SphereBouquet (suc n) (Fin k) ] inr x' ≡ fst f x) ∥₁
  makefun = sphereToTrunc _ λ x → help (fst f x) .fst

-- -- move to pushout
-- module _ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
--   (f1 : A → B) (f2 : B → C) {g : A → D} where
--   PushoutComp→IteratedPushout : Pushout (f2 ∘ f1) g → Pushout {C = Pushout f1 g} f2 inl
--   PushoutComp→IteratedPushout (inl x) = inl x
--   PushoutComp→IteratedPushout (inr x) = inr (inr x)
--   PushoutComp→IteratedPushout (push a i) = (push (f1 a) ∙ λ i → inr (push a i)) i

--   IteratedPushout→PushoutComp : Pushout {C = Pushout f1 g} f2 inl → Pushout (f2 ∘ f1) g
--   IteratedPushout→PushoutComp (inl x) = inl x
--   IteratedPushout→PushoutComp (inr (inl x)) = inl (f2 x)
--   IteratedPushout→PushoutComp (inr (inr x)) = inr x
--   IteratedPushout→PushoutComp (inr (push a i)) = push a i
--   IteratedPushout→PushoutComp (push a i) = inl (f2 a)

--   Iso-PushoutComp-IteratedPushout : Iso (Pushout (f2 ∘ f1) g) (Pushout {C = Pushout f1 g} f2 inl)
--   Iso.fun Iso-PushoutComp-IteratedPushout = PushoutComp→IteratedPushout
--   Iso.inv Iso-PushoutComp-IteratedPushout = IteratedPushout→PushoutComp
--   Iso.rightInv Iso-PushoutComp-IteratedPushout (inl x) = refl
--   Iso.rightInv Iso-PushoutComp-IteratedPushout (inr (inl x)) = push x
--   Iso.rightInv Iso-PushoutComp-IteratedPushout (inr (inr x)) = refl
--   Iso.rightInv Iso-PushoutComp-IteratedPushout (inr (push a i)) j =
--     compPath-filler' (push (f1 a)) (λ i₁ → inr (push a i₁)) (~ j) i
--   Iso.rightInv Iso-PushoutComp-IteratedPushout (push a i) j = push a (i ∧ j)
--   Iso.leftInv Iso-PushoutComp-IteratedPushout (inl x) = refl
--   Iso.leftInv Iso-PushoutComp-IteratedPushout (inr x) = refl
--   Iso.leftInv Iso-PushoutComp-IteratedPushout (push a i) j = T j i
--     where
--     T = cong-∙ IteratedPushout→PushoutComp (push (f1 a)) (λ i → inr (push a i))
--       ∙ sym (lUnit _)


-- -- move to Wedge.Properties?
-- module _ {ℓ ℓ'} {A : Type ℓ} (B : A → Pointed ℓ')
--   where
--   cofibFst : Type _
--   cofibFst = cofib {A = Σ A (fst ∘ B)} {B = A} fst

--   cofibFst→⋁ : cofibFst → ⋁gen A λ a → Susp∙ (fst (B a))
--   cofibFst→⋁ (inl x) = inl x
--   cofibFst→⋁ (inr a) = inr (a , north)
--   cofibFst→⋁ (push (a , b) i) = (push a ∙ λ i → inr (a , toSusp (B a) b i)) i

--   ⋁→cofibFst : ⋁gen A (λ a → Susp∙ (fst (B a))) → cofibFst
--   ⋁→cofibFst (inl x) = inl x
--   ⋁→cofibFst (inr (x , north)) = inl tt
--   ⋁→cofibFst (inr (x , south)) = inr x
--   ⋁→cofibFst (inr (x , merid a i)) = push (x , a) i
--   ⋁→cofibFst (push a i) = inl tt

--   Iso-cofibFst-⋁ : Iso cofibFst (⋁gen A (λ a → Susp∙ (fst (B a))))
--   Iso.fun Iso-cofibFst-⋁ = cofibFst→⋁
--   Iso.inv Iso-cofibFst-⋁ = ⋁→cofibFst
--   Iso.rightInv Iso-cofibFst-⋁ (inl x) = refl
--   Iso.rightInv Iso-cofibFst-⋁ (inr (x , north)) = push x
--   Iso.rightInv Iso-cofibFst-⋁ (inr (x , south)) i = inr (x , merid (pt (B x)) i)
--   Iso.rightInv Iso-cofibFst-⋁ (inr (x , merid a i)) j =
--     hcomp (λ k → λ {(i = i0) → push x (j ∨ ~ k)
--                    ; (i = i1) → inr (x , merid (pt (B x)) j)
--                    ; (j = i0) → compPath-filler' (push x)
--                                    (λ i₁ → inr (x , toSusp (B x) a i₁)) k i
--                    ; (j = i1) → inr (x , merid a i)})
--           (inr (x , compPath-filler (merid a) (sym (merid (pt (B x)))) (~ j) i))
--   Iso.rightInv Iso-cofibFst-⋁ (push a i) j = push a (i ∧ j)
--   Iso.leftInv Iso-cofibFst-⋁ (inl x) = refl
--   Iso.leftInv Iso-cofibFst-⋁ (inr x) = push (x , snd (B x))
--   Iso.leftInv Iso-cofibFst-⋁ (push (a , b) i) j = help j i
--     where
--     help : Square (cong ⋁→cofibFst ((push a ∙ λ i → inr (a , toSusp (B a) b i))))
--                   (push (a , b)) refl (push (a , (snd (B a))))
--     help = (cong-∙ ⋁→cofibFst (push a) (λ i → inr (a , toSusp (B a) b i))
--          ∙ sym (lUnit _)
--          ∙ cong-∙ (⋁→cofibFst ∘ inr ∘ (a ,_)) (merid b) (sym (merid (snd (B a)))))
--          ◁ λ i j → compPath-filler (push (a , b)) (sym (push (a , pt (B a)))) (~ i) j

open import Cubical.CW.Properties
open import Cubical.CW.Instances.Sn
open import Cubical.CW.Homology.Groups.Sn



-- Sn approx
Sn→SfamGen : ∀ {n k : ℕ} (p : Trichotomyᵗ k (suc n))
  → 0 <ᵗ k → S₊ n → Sgen.Sfam n k p
Sn→SfamGen {n = n} {suc k} (lt x₁) _ x = tt
Sn→SfamGen {n = n} {suc k} (eq x₁) _ x = x
Sn→SfamGen {n = n} {suc k} (gt x₁) _ x = x

Sn→SfamGen∙ : ∀ {n k : ℕ} (p : Trichotomyᵗ (suc k) (suc n))
  → Sn→SfamGen p tt (ptSn n) ≡ Sgen.Sfam∙ n k p
Sn→SfamGen∙ (lt x) = refl
Sn→SfamGen∙ (eq x) = refl
Sn→SfamGen∙ (gt x) = refl

{- {suc k} p with  (k ≟ᵗ n)
... | lt x = λ _ → tt
... | eq x = idfun _
... | gt x = idfun _
-}
CWskel∙ : ∀ {ℓ} (X : CWskel ℓ) → fst X 1 → (n : ℕ) → fst X (suc n)
CWskel∙ X x zero = x
CWskel∙ X x (suc n) = CW↪ X (suc n) (CWskel∙ X x n)

CWskel∞∙ : ∀ {ℓ} (X : CWskel ℓ) → fst X 1 → (n : ℕ) → realise X
CWskel∞∙ X x₀ n = incl (CWskel∙ X x₀ n)

CWskel∞∙Id : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) (n : ℕ) → CWskel∞∙ X x₀ n ≡ incl x₀
CWskel∞∙Id X x₀ zero = refl
CWskel∞∙Id X x₀ (suc n) = sym (push (CWskel∙ X x₀ n)) ∙ CWskel∞∙Id X x₀ n

incl∙ : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) {n : ℕ}
  → (fst X (suc n) , CWskel∙ X x₀ n) →∙ (realise X , incl x₀)
fst (incl∙ X x₀ {n = n}) = incl
snd (incl∙ X x₀ {n = n}) = CWskel∞∙Id X x₀ n

CWskel∙Gen : ∀ {ℓ} (X : CWskel ℓ) → fst X 1 → (n m : ℕ) (p : _)
  → G.subComplexFam X (suc m) (suc n) p
CWskel∙Gen X x₀ n m (lt x) = CWskel∙ X x₀ n
CWskel∙Gen X x₀ n m (eq x) = CWskel∙ X x₀ n
CWskel∙Gen X x₀ n m (gt x) = CWskel∙ X x₀ m

CWskel∙Gen≡CWskel∙ : ∀ {ℓ} (X : CWskel ℓ) (x : fst X 1) → (n m : ℕ)
  → CWskel∙Gen X x n (suc m) (suc n ≟ᵗ suc (suc m))
   ≡ CWskel∙ (subComplex X (suc (suc m))) x n
CWskel∙Gen≡CWskel∙ X x zero m = refl
CWskel∙Gen≡CWskel∙ X x (suc n) m =
  lem _ _
  ∙ cong (CW↪ (subComplex X (suc (suc m))) (suc n))
         (CWskel∙Gen≡CWskel∙ X x n m)
  where
  lem : (p : _) (q : _) → CWskel∙Gen X x (suc n) (suc m) p
      ≡ invEq (G.subComplexFam≃Pushout X (suc (suc m)) (suc n) q p)
         (inl (CWskel∙Gen X x n (suc m) q))
  lem (lt x) (lt x₁) = refl
  lem (lt x) (eq x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc m)) x₁ (<ᵗ-trans <ᵗsucm x)))
  lem (lt x) (gt x₁) = ⊥.rec (¬squeeze (x , <ᵗ-trans x₁ (<ᵗ-trans <ᵗsucm <ᵗsucm)))
  lem (eq x) (lt x₁) = refl
  lem (eq x) (eq x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) (x₁ ∙ sym x) <ᵗsucm))
  lem (eq x) (gt x₁) = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ suc n) (sym x) x₁))
  lem (gt x) (lt x₁) = ⊥.rec (¬squeeze (x₁ , x))
  lem (gt y) (eq z) = ((λ j → transp (λ i → fst X (suc (predℕ (z (~ j ∨ i))))) (~ j)
                                 (CWskel∙ X x (predℕ (z (~ j))))))
                     ∙ cong (λ p → subst (fst X) p (CWskel∙ X x n)) (isSetℕ _ _ _ z)
                     ∙ sym (transportRefl _)
  lem (gt x) (gt x₁) = refl

CWskel∙GenSubComplex : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) {n m : ℕ} (t : m <ᵗ suc (suc n))
  (p : _)
  → CWskel∙Gen X x₀ m (suc n) p
  ≡ subComplexMapGen.subComplex←map' X (suc (suc n)) (suc m) t p (CWskel∙ X x₀ m)
CWskel∙GenSubComplex X x₌ t (lt x) = refl
CWskel∙GenSubComplex X x₌ t (eq x) = refl
CWskel∙GenSubComplex X x₌ t (gt x) = ⊥.rec (¬squeeze (x , t))

CWskel∙SubComplex : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) {n m : ℕ} (t : m <ᵗ suc (suc n))
  → CWskel∙ (subComplex X (suc (suc n))) x₀ m
   ≡ fst (complex≃subcomplex' X (suc (suc n)) (suc m) t
           (suc m ≟ᵗ suc (suc n))) (CWskel∙ X x₀ m)
CWskel∙SubComplex X x₀ t  =
  sym (CWskel∙Gen≡CWskel∙ X x₀ _ _) ∙ CWskel∙GenSubComplex X x₀ t _

module _ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
  (f : S₊ n → fst X (suc n))
  (f₀ : f (ptSn n) ≡ CWskel∙ X x₀ n) where

  private
    <ᵗ→0<ᵗ : {n m : ℕ} → n <ᵗ m → 0 <ᵗ m
    <ᵗ→0<ᵗ {n} {suc m} _ = tt

  makeFinSequenceMapGen : ∀ k → (p : _) → Sgen.Sfam n k p → fst X k
  makeFinSequenceMapGen (suc k) (lt x₁) x = CWskel∙ X x₀ k
  makeFinSequenceMapGen (suc k) (eq x₁) x = subst (fst X) (sym x₁) (f x)
  makeFinSequenceMapGen (suc k) (gt x₁) x =
    CW↪ X k (makeFinSequenceMapGen k (k ≟ᵗ suc n) (Sn→SfamGen _ (<ᵗ→0<ᵗ x₁) x))

  makeFinSequenceMapGen∙ : ∀ k → (p : _)
    → makeFinSequenceMapGen (suc k) p (Sgen.Sfam∙ n k p) ≡ CWskel∙ X x₀ k
  makeFinSequenceMapGen∙ k (lt x) = refl
  makeFinSequenceMapGen∙ k (eq x) =
    cong₂ (λ p q → subst (fst X) p q) (isSetℕ _ _ _ _) f₀ ∙ H _ (cong predℕ x)
    where
    H : (n : ℕ) (x : k ≡ n)
      → subst (fst X) (cong suc (sym x)) (CWskel∙ X x₀ n) ≡ CWskel∙ X x₀ k
    H = J> transportRefl _
  makeFinSequenceMapGen∙ (suc k) (gt x) =
    cong (CW↪ X (suc k))
      (cong (makeFinSequenceMapGen (suc k) (Trichotomyᵗ-suc (k ≟ᵗ n)))
            (Sn→SfamGen∙ (Trichotomyᵗ-suc (k ≟ᵗ n)))
      ∙ makeFinSequenceMapGen∙ k (suc k ≟ᵗ suc n))

  makeFinSequenceMapComm : (k : ℕ) (p : _) (q : _) (x : _)
    → makeFinSequenceMapGen (suc k) p (invEq (SαEqGen n k p q) (inl x))
    ≡ CW↪ X k (makeFinSequenceMapGen k q x)
  makeFinSequenceMapComm (suc k) (lt x₁) (lt x₂) x = refl
  makeFinSequenceMapComm (suc k) (lt x₁) (eq x₂) x =
    ⊥.rec (¬-suc-n<ᵗn (subst (suc k <ᵗ_) (cong predℕ (sym x₂)) x₁))
  makeFinSequenceMapComm (suc k) (lt x₁) (gt x₂) x =
    ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x₁ x₂))
  makeFinSequenceMapComm (suc k) (eq x₁) (lt x₂) x =
    cong (subst (fst X) (sym x₁) ∘ f) (invEqSαEqGen∙ n k _ _)
    ∙ makeFinSequenceMapGen∙ (suc k) (eq x₁)
  makeFinSequenceMapComm k (eq x₁) (eq x₂) x =
    ⊥.rec (falseDichotomies.eq-eq (refl , sym (x₁ ∙ sym x₂)))
  makeFinSequenceMapComm k (eq x₁) (gt x₂) x =
    ⊥.rec (¬-suc-n<ᵗn {n} (subst (suc (suc n) <ᵗ_) x₁ x₂))
  makeFinSequenceMapComm k (gt x₁) (lt x₂) x = ⊥.rec (¬squeeze (x₁ , x₂))
  makeFinSequenceMapComm (suc k) (gt x₁) (eq x₂) x with (k ≟ᵗ n)
  ... | lt x₃ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (cong predℕ x₂) x₃))
  ... | eq x₃ = cong (CW↪ X (suc k))
    (cong (subst (fst X) (cong suc (sym x₃))) (cong f (lem n x x₁ x₂))
    ∙ cong (λ p → subst (fst X) p (f x)) (isSetℕ _ _ (cong suc (sym x₃)) (sym x₂)))
    where
    lem : (n : ℕ) (x : _) (x₁ : _) (x₂ : _)
      → invEq (SαEqGen n (suc k) (gt x₁) (eq x₂)) (inl x) ≡ x
    lem zero x x₁ x₂ = refl
    lem (suc n) x x₁ x₂ = refl
  ... | gt x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) (cong predℕ  x₂) x₃))
  makeFinSequenceMapComm (suc k) (gt x₁) (gt x₂) x with k ≟ᵗ n
  ... | lt x₃ = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₂ x₃))
  ... | eq x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₃ x₂))
  ... | gt x₃ =
    cong (CW↪ X (suc k))
       (cong (CW↪ X k ∘ makeFinSequenceMapGen k (k ≟ᵗ suc n))
         (cong (λ w → Sn→SfamGen (k ≟ᵗ suc n) (<ᵗ→0<ᵗ w)
           (invEq (SαEqGen n (suc k) (gt x₁) (gt x₂)) (inl x))) (isProp<ᵗ x₃ x₂)
       ∙ cong (Sn→SfamGen (k ≟ᵗ suc n) (<ᵗ→0<ᵗ x₂))
          (lem n k x₁ x₂ x (k ≟ᵗ suc n)))
      ∙ makeFinSequenceMapComm k (gt x₂) (k ≟ᵗ suc n) _)
      where
      lem : (n k : ℕ) (x₁ : _) (x₂ : _) (x : _) (w : _)
        → invEq (SαEqGen n (suc k) (gt x₁) (gt x₂)) (inl x) ≡
                         invEq (SαEqGen n k (gt x₂) w)
                         (inl (Sn→SfamGen w (<ᵗ→0<ᵗ x₂) x))
      lem n k x₁ x₂ x (lt x₃) = ⊥.rec (¬squeeze (x₂ , x₃))
      lem zero (suc k) x₁ x₂ x (eq x₃) = refl
      lem (suc n) (suc k) x₁ x₂ x (eq x₃) = refl
      lem zero (suc k) x₁ x₂ x (gt x₃) = refl
      lem (suc n) (suc k) x₁ x₂ x (gt x₃) = refl

  niceCellMapS : cellMap (Sˢᵏᵉˡ n) X
  SequenceMap.map niceCellMapS k = makeFinSequenceMapGen k (k ≟ᵗ suc n)
  SequenceMap.comm niceCellMapS k x =
    sym (makeFinSequenceMapComm k (suc k ≟ᵗ suc n) (k ≟ᵗ suc n) x)

approxSphereMap∙ : ∀ {ℓ} (Xsk : CWskel ℓ) → (x₀ : fst Xsk (suc zero)) (n : ℕ)
  (f : S₊∙ (suc n) →∙ (realise Xsk , incl x₀))
  → ∃[ f' ∈ S₊∙ (suc n) →∙ (fst Xsk (suc (suc n)) , CWskel∙ Xsk x₀ (suc n)) ]
      (incl∙ Xsk x₀ ∘∙ f' ≡ f)
approxSphereMap∙ Xsk x₀ n f = PT.rec squash₁
                (λ F → TR.rec squash₁ (λ fp → ∣ ((λ x → F x .fst .fst) , sym (cong fst fp))
                  , ΣPathP ((funExt (λ x → F x .fst .snd))
                  , (SQ' _ _ _ _ _ _ _ _ (cong snd fp))) ∣₁)
                (F (ptSn (suc n)) .snd refl))
                approx'
 where
 SQ' : ∀ {ℓ} {A : Type ℓ} (x y : A) (p : x ≡ y) (z : A) (q : y ≡ z) (w : A) (r : x ≡ w) (t :  w ≡ z)
   → Square (p ∙ q) t r refl → Square (sym r ∙ p) (sym q)  t refl
 SQ' x = J> (J> (J> λ t s → sym (rUnit refl) ◁ λ i j → (rUnit refl ◁ s) (~ j) i))
 approx' : ∥ ((x : S₊ (suc n)) → Σ[ fb ∈ fiber (CW↪∞ Xsk (suc (suc n))) (fst f x) ]
               ((p : ptSn (suc n) ≡ x)
             → hLevelTrunc 1 (PathP (λ i → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
                 ((CWskel∙ Xsk x₀ (suc n)) , (CWskel∞∙Id Xsk x₀ (suc n) ∙ sym (snd f))) fb))) ∥₁
 approx' = sphereToTrunc (suc n)
   {λ x → Σ[ fb ∈ fiber (CW↪∞ Xsk (suc (suc n))) (fst f x) ]
               ((p : ptSn (suc n) ≡ x)
             → hLevelTrunc 1 (PathP (λ i → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
                 ((CWskel∙ Xsk x₀ (suc n)) , (CWskel∞∙Id Xsk x₀ (suc n) ∙ sym (snd f))) fb) )}
     λ a → TR.rec (isOfHLevelTrunc (suc (suc n)))
     (λ fa → ∣ fa , (λ p → J (λ a p → (fa : fiber (CW↪∞ Xsk (suc (suc n))) (fst f a))
                    → hLevelTrunc 1 (PathP (λ i → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
                        (CWskel∙ Xsk x₀ (suc n) , CWskel∞∙Id Xsk x₀ (suc n) ∙ (λ i → snd f (~ i))) fa))
                        (λ fa → isConnectedPathP 1 (isConnectedSubtr' n 2
                          (isConnected-CW↪∞ (suc (suc n)) Xsk (fst f (ptSn (suc n))))) _ _ .fst) p fa) ∣ₕ)
     (isConnected-CW↪∞ (suc (suc n)) Xsk (fst f a) .fst)


module _ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
  (fap : S₊∙ n →∙ (fst X (suc n) , CWskel∙ X x₀ n))
  (f : S₊∙ n →∙ (realise X , incl x₀))
  (fap≡ : (x : _) → incl {n = suc n} (fst fap x) ≡ fst f x) where

  betterApprox : cellMap (Sˢᵏᵉˡ n) X
  betterApprox = niceCellMapS X n x₀ (fst fap) (snd fap)

  isApprox : realiseSequenceMap betterApprox ≡ fst f ∘ invEq (isCWSphere n .snd)
  isApprox = funExt λ x → cong (realiseSequenceMap betterApprox) (sym (secEq (isCWSphere n .snd) x))
                         ∙ lem _
    where
    lem : (x : _) → realiseSequenceMap betterApprox (fst (isCWSphere n .snd) x) ≡ fst f x
    lem x with (n ≟ᵗ n)
    ... | lt x₁ = ⊥.rec (¬m<ᵗm x₁)
    ... | eq x₁ = cong (incl {n = suc n})
                  (cong (λ p → subst (fst X) p (fst fap x))
                   (isSetℕ _ _ _ refl)
                ∙ transportRefl (fst fap x)) ∙ fap≡ x
    ... | gt x₁ = ⊥.rec (¬m<ᵗm x₁)

  betterFinCellApproxS : (k : ℕ) → finCellApprox (Sˢᵏᵉˡ n) X (fst f ∘ invEq (isCWSphere n .snd)) k
  FinSequenceMap.fmap (fst (betterFinCellApproxS k)) = SequenceMap.map betterApprox ∘ fst
  FinSequenceMap.fcomm (fst (betterFinCellApproxS k)) = SequenceMap.comm betterApprox ∘ fst
  snd (betterFinCellApproxS k) = →FinSeqColimHomotopy _ _
    (funExt⁻ isApprox ∘ FinSeqColim→Colim k ∘ (fincl flast))

open import Cubical.HITs.Sn.Degree
bouquetDegree+ : (n m k : ℕ)
  (f g : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
  → bouquetDegree (SphereBouquet∙Π f g .fst)
   ≡ addGroupHom ℤ[Fin m ] ℤ[Fin k ] (bouquetDegree (fst f)) (bouquetDegree (fst g))
bouquetDegree+ n m k f g =
  agreeOnℤFinGenerator→≡
    λ s → funExt λ y → (sym (isGeneratorℤFinGenerator' _ s)
      ∙ cong (degree (suc n)) (funExt (main n s y f g))
       ∙ degreeHom {n = n}
         ((λ x₁ → pickPetal y (fst f (inr (s , x₁))))
                 , cong (pickPetal y) (cong (fst f) (sym (push s)) ∙ snd f))
         ((λ x₁ → pickPetal y (fst g (inr (s , x₁))))
                 , cong (pickPetal y) (cong (fst g) (sym (push s)) ∙ snd g))
      ∙ isGeneratorℤFinGenerator' _ s
      ∙ cong sumFinℤ (funExt λ x →
        ·DistR+ (ℤFinGenerator s x)
                (degree (suc n) (λ x₁ → pickPetal y (fst f (inr (x , x₁)))))
                (degree (suc n) (λ x₁ → pickPetal y (fst g (inr (x , x₁))))))
      ∙ sumFinℤHom _ _) --
  where
  main : (n : ℕ) (s : Fin m) (y : _)
    (f g : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k)) (x : S₊ (suc n)) →
      pickPetal y (SphereBouquet∙Π f g .fst (inr (s , x)))
    ≡ (∙Π ((λ x₁ → pickPetal y (fst f (inr (s , x₁)))) ,
           (λ i → pickPetal y (((λ i₁ → fst f (push s (~ i₁))) ∙ snd f) i)))
          ((λ x₁ → pickPetal y (fst g (inr (s , x₁)))) ,
           (λ i → pickPetal y (((λ i₁ → fst g (push s (~ i₁))) ∙ snd g) i))) .fst x)
  main zero s y f g base = refl
  main zero s y f g (loop i) = refl
  main (suc n) s y f g north = refl
  main (suc n) s y f g south = refl
  main (suc n) s y f g (merid a i) j = lem j i
    where
    lem : cong (pickPetal y) (cong (λ x → SphereBouquet∙Π f g .fst (inr (s , x))) (merid a))
        ≡ (sym (cong (pickPetal y) ((λ i₁ → fst f (push s (~ i₁))) ∙ snd f))
          ∙∙ cong (pickPetal y) (cong (λ x → fst f (inr (s , x))) (σS a))
          ∙∙ cong (pickPetal y) ((λ i₁ → fst f (push s (~ i₁))) ∙ snd f))
        ∙ (sym (cong (pickPetal y) ((λ i₁ → fst g (push s (~ i₁))) ∙ snd g))
          ∙∙ cong (pickPetal y) (cong (λ x → fst g (inr (s , x))) (σS a))
          ∙∙ cong (pickPetal y) ((λ i₁ → fst g (push s (~ i₁))) ∙ snd g))
    lem = (cong-∙ (pickPetal y) _ _
      ∙ cong₂ _∙_ (cong-∙∙ (pickPetal y) (sym ((λ i₁ → fst f (push s (~ i₁))) ∙ snd f)) _ _)
                  (cong-∙∙ (pickPetal y) (sym ((λ i₁ → fst g (push s (~ i₁))) ∙ snd g)) _ _))


∙Π∘∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (n : ℕ) (f g : S₊∙ (suc n) →∙ A) (h : A →∙ B)
  → h ∘∙ ∙Π f g ≡ ∙Π (h ∘∙ f) (h ∘∙ g)
∙Π∘∙ {A = A} n f g h =
     cong (h ∘∙_) (cong₂ ∙Π (sym (Iso.rightInv (sphereFunIso n) f))
                            (sym (Iso.rightInv (sphereFunIso n) g)))
  ∙∙ le n (Iso.inv (sphereFunIso n) f) (Iso.inv (sphereFunIso n) g)
  ∙∙ cong₂ (λ f g → ∙Π (h ∘∙ f) (h ∘∙ g))
           (Iso.rightInv (sphereFunIso n) f)
           (Iso.rightInv (sphereFunIso n) g)
  where
  lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → Square p refl (refl ∙ p) refl
  lem p = lUnit p ◁ λ i j → (refl ∙ p) (i ∨ j)

  mainEq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (a : A) (b : B)
    (fp : f a ≡ b) (l1 l2 : a ≡ a)
    → Square (cong f ((l1 ∙ refl) ∙ (l2 ∙ refl)))
             ((sym (refl ∙ fp) ∙∙ cong f l1 ∙∙ (refl ∙ fp))
            ∙ (sym (refl ∙ fp) ∙∙ cong f l2 ∙∙ (refl ∙ fp)))
              fp fp
  mainEq f a = J> λ l1 l2 → cong-∙ f _ _
    ∙ cong₂ _∙_ (cong-∙ f l1 refl  ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
                (cong-∙ f l2 refl ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))

  le : (n : ℕ) (f g : S₊∙ n →∙ Ω A)
    → (h ∘∙ ∙Π (Iso.fun (sphereFunIso n) f) (Iso.fun (sphereFunIso n) g))
    ≡ ∙Π (h ∘∙ Iso.fun (sphereFunIso n) f) (h ∘∙ Iso.fun (sphereFunIso n) g)
  fst (le zero f g i) base = snd h i
  fst (le zero f g i) (loop i₁) = mainEq (fst h) _ _ (snd h) (fst f false) (fst g false) i i₁
  fst (le (suc n) f g i) north = snd h i
  fst (le (suc n) f g i) south = snd h i
  fst (le (suc n) f g i) (merid a i₁) =
    mainEq (fst h) _ _ (snd h)
      (cong (Iso.fun (sphereFunIso (suc n)) f .fst) (σS a))
      (cong (Iso.fun (sphereFunIso (suc n)) g .fst) (σS a)) i i₁
  snd (le zero f g i) j = lem (snd h) j i
  snd (le (suc n) f g i) j = lem (snd h) j i

niceCellMapS∙Π : ∀ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
  (fap gap : S₊∙ (suc n) →∙ (fst X (suc (suc n)) , CWskel∙ X x₀ (suc n)))
  (f : S₊∙ (suc n) →∙ (realise X , incl x₀))
  (fap≡ : incl∙ X x₀ ∘∙ fap ≡ f)
  (g : S₊∙ (suc n) →∙ (realise X , incl x₀))
  (gap≡ : incl∙ X x₀ ∘∙ gap ≡ g)
  → realiseCellMap (betterApprox X (suc n) x₀ (∙Π fap gap) (∙Π f g)
      (λ x → funExt⁻ (cong fst (∙Π∘∙ n fap gap (incl∙ X x₀))) x
            ∙ λ i → ∙Π (fap≡ i) (gap≡ i) .fst x))
    ≡ (∙Π f g .fst ∘ invEq (isCWSphere (suc n) .snd))
niceCellMapS∙Π X n x₀ fap gap =
  J> (J> funExt λ x → cong h (sym (secEq (isCWSphere (suc n) .snd) x))
                     ∙ main _
                     ∙ cong (∙Π (incl∙ X x₀ ∘∙ fap) (incl∙ X x₀ ∘∙ gap) .fst)
                         (retEq (SfamTopElement (suc n)) _))
  where
  h = realiseCellMap (betterApprox X (suc n) x₀
      (∙Π fap gap) (∙Π (incl∙ X x₀ ∘∙ fap) (incl∙ X x₀ ∘∙ gap))
      (λ x → (funExt⁻ (cong fst (∙Π∘∙ n fap gap (incl∙ X x₀))) x) ∙ refl))

  main : (x : Sgen.Sfam (suc n) (suc (suc n)) (suc (suc n) ≟ᵗ suc (suc n)))
       → h (incl {n = suc (suc n)} x)
       ≡ ∙Π (incl∙ X x₀ ∘∙ fap) (incl∙ X x₀ ∘∙ gap) .fst (invEq (SfamTopElement (suc n)) x)
  main with (n ≟ᵗ n)
  ... | lt x = ⊥.rec (¬m<ᵗm x)
  ... | eq x = λ x
    → cong (incl {n = suc (suc n)})
         (cong (λ p → subst (fst X) p (fst (∙Π fap gap) x)) (isSetℕ _ _ _ refl)
          ∙ transportRefl _)
      ∙ funExt⁻ (cong fst (∙Π∘∙ n fap gap (incl∙ X x₀))) x
  ... | gt x = ⊥.rec (¬m<ᵗm x)


--------------------------------------------


isPropTrichotomyᵗ : ∀ {n m : ℕ} → isProp (Trichotomyᵗ n m)
isPropTrichotomyᵗ {n = n} {m = m} (lt x) (lt x₁) i = lt (isProp<ᵗ x x₁ i)
isPropTrichotomyᵗ {n = n} {m = m} (lt x) (eq x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) x₁ x))
isPropTrichotomyᵗ {n = n} {m = m} (lt x) (gt x₁) = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ x))
isPropTrichotomyᵗ {n = n} {m = m} (eq x) (lt x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) x x₁))
isPropTrichotomyᵗ {n = n} {m = m} (eq x) (eq x₁) i = eq (isSetℕ n m x x₁ i)
isPropTrichotomyᵗ {n = n} {m = m} (eq x) (gt x₁) =
  ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (sym x) x₁))
isPropTrichotomyᵗ {n = n} {m = m} (gt x) (lt x₁) = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ x))
isPropTrichotomyᵗ {n = n} {m = m} (gt x) (eq x₁) =
  ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (sym x₁) x))
isPropTrichotomyᵗ {n = n} {m = m} (gt x) (gt x₁) i = gt (isProp<ᵗ x x₁ i)



CW↪CommSubComplex : ∀ {ℓ} (C : CWskel ℓ) (m k : ℕ) →
    CW↪ C m ∘ subComplex→map C k m
  ≡ subComplex→map C k (suc m) ∘ CW↪ (subComplex C k) m
CW↪CommSubComplex C m k with (m ≟ᵗ k) | (suc m ≟ᵗ k)
... | lt x | lt x₁ = refl
... | lt x | eq x₁ = refl
... | lt x | gt x₁ = ⊥.rec (¬squeeze (x , x₁))
... | eq x | lt x₁ = (⊥.rec (¬m<ᵗm (subst (_<ᵗ k) x (<ᵗ-trans <ᵗsucm x₁))))
... | eq x | eq x₁ = (⊥.rec (¬m<ᵗm (subst (_<ᵗ_ m) (x₁ ∙ (λ i → x (~ i))) <ᵗsucm)))
... | eq x | gt x₁ = funExt λ s → help _ _ x x₁ s (suc m ≟ᵗ suc k)
  where
  help : (m : ℕ) (k : ℕ) (x : m ≡ k) (x₁ : k <ᵗ suc m) (s : fst C m) (p : _)
    →  CW↪ C m s ≡ CW↑Gen C k (suc m) p x₁ (transport refl (subst (fst C) x s))
  help zero = λ k x y s → ⊥.rec (CW₀-empty C s)
  help (suc m) = J> λ x₁ s
    → λ { (lt x) → ⊥.rec (¬squeeze (x₁ , x))
         ; (eq x) → cong (CW↪ C (suc m)) (sym (transportRefl s)
              ∙ λ i → subst (fst C) (isSetℕ _ _ refl (cong predℕ (sym x)) i)
                      (transportRefl (transportRefl s (~ i)) (~ i)))
         ; (gt x) → ⊥.rec (¬m<ᵗm x) }
... | gt x | lt x₁ = ⊥.rec (¬squeeze (x₁ , <ᵗ-trans x (<ᵗ-trans <ᵗsucm <ᵗsucm)))
... | gt x | eq x₁ =
  ⊥.rec (¬m<ᵗm (transp (λ i → k <ᵗ x₁ i) i0 (<ᵗ-trans x <ᵗsucm)))
... | gt x | gt x₁ = funExt λ a → help _ _ x x₁ (suc m ≟ᵗ suc k) a
  where
  help : (m k : ℕ) (x : k <ᵗ m) (x₁ : k <ᵗ suc m) (p : _) (a : _)
    → CW↪ C m (CW↑Gen C k m  (m ≟ᵗ suc k) x a) ≡ CW↑Gen C k (suc m) p x₁ a
  help (suc m) zero x x₁ p a = ⊥.rec (C .snd .snd .snd .fst a)
  help (suc m) (suc k) x x₁ (lt x₂) a = ⊥.rec (¬squeeze (x₁ , x₂))
  help (suc m) (suc k) x x₁ (eq x₂) a =
    ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) (sym (cong (predℕ ∘ predℕ) x₂)) x))
  help (suc m) (suc k) x x₁ (gt x₂) a =
    cong (CW↪ C (suc m))
      λ i → CW↑Gen C (suc k) (suc m)
              (Trichotomyᵗ-suc (m ≟ᵗ suc k)) (isProp<ᵗ x x₂ i) a

CW↪SubComplexCharac : ∀ {ℓ} (C : CWskel ℓ) (m k : ℕ) (q : m <ᵗ k) →
    CW↪ (subComplex C k) m ≡ invEq (subComplex→Equiv C k (suc m) q) ∘ CW↪ C m ∘ subComplex→map C k m
CW↪SubComplexCharac C m k q = funExt λ x
  → sym (retEq (subComplex→Equiv C k (suc m) q) _)
   ∙ cong (invEq (subComplex→Equiv C k (suc m) q)) (funExt⁻ (sym (CW↪CommSubComplex C m k)) x)


CW↑GenComm : ∀ {ℓ} (C : CWskel ℓ) (m n k : ℕ) (p : Trichotomyᵗ n (suc m)) (t : m <ᵗ n) →
    CW↑Gen C m n p t ∘ subComplex→map C k m
  ≡ subComplex→map C k n ∘ CW↑Gen (subComplex C k) m n p t
CW↑GenComm C zero (suc n) k p t = funExt λ x → (⊥.rec (G.subComplex₀-empty C k (0 ≟ᵗ k) x))
CW↑GenComm C (suc m) (suc n) k p t =
  funExt (λ qa → (help n m k p _ t refl qa
  ∙ cong ((subComplex→map C k (suc n) ∘
       CW↑Gen (subComplex C k) (suc m) (suc n) p t)) (transportRefl qa)))
  where
  help : (n m k : ℕ) (p : _) (s : _) (t : _) (pp : s ≡ (suc m ≟ᵗ k))
    → (x : G.subComplexFam C k (suc m) s) →
         CW↑Gen C (suc m) (suc n) p t
         (subComplexMapGen.subComplex→map' C k (suc m) s x)
         ≡
         subComplexMapGen.subComplex→map' C k (suc n) (suc n ≟ᵗ k)
         (CW↑Gen (subComplex C k) (suc m) (suc n) p t (subst (G.subComplexFam C k (suc m)) pp x))
  help (suc n) m k (lt x₁) s t pp x = ⊥.rec (¬squeeze (t , x₁))
  help (suc n) m k (eq x₁) s t pp x = cong (CW↪ C (suc n))
    (cong (λ p → subst (fst C) p
      (subComplexMapGen.subComplex→map' C k (suc m) s x)) (isSetℕ _ _ _ _)
    ∙ lem m (cong predℕ (cong predℕ x₁)) s (sym pp) x
    ∙ cong (subComplex→map C k (suc n))
        (cong (λ p → subst (subComplexFam C k) p
          (subst (G.subComplexFam C k (suc m)) pp x))
          (isSetℕ _ _ _ _)))
    ∙ funExt⁻ (CW↪CommSubComplex C (suc n) k)
        ((subst (λ m₁ → subComplexFam C k m₁) (cong predℕ (sym x₁))
          (subst (G.subComplexFam C k (suc m)) pp x)))
    where
    lem : (m : ℕ) (x₁ : n ≡ m) (s : _) (t : (suc m ≟ᵗ k) ≡ s) (x : _)
      → subst (fst C) (cong suc (sym x₁)) (subComplexMapGen.subComplex→map' C k (suc m) s x)
        ≡ subComplex→map C k (suc n)
           (subst (subComplexFam C k) (cong suc (sym x₁))
             (subst (G.subComplexFam C k (suc m)) (sym t) x))
    lem = J> (J> λ x → transportRefl _ ∙ sym (cong (subComplex→map C k (suc n)) (transportRefl _ ∙ transportRefl x)))
  help (suc n) m k (gt x₁) s t pp x =
    cong (CW↪ C (suc n)) (help n m k (suc n ≟ᵗ suc (suc m)) s x₁ pp x)
    ∙ funExt⁻ (CW↪CommSubComplex C (suc n) k)
      (CW↑Gen (subComplex C k) (suc m) (suc n) (suc n ≟ᵗ suc (suc m)) x₁
         (subst (G.subComplexFam C k (suc m)) pp x))

subComplex→comm : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ)
    (p : _) (q : _) (x : G.subComplexFam C n m p)
  → CW↪ C m (subComplexMapGen.subComplex→map' C n m p x)
  ≡ subComplexMapGen.subComplex→map' C n (suc m) q
       (SubComplexGen.subComplexCW↪Gen C n m p q x)
subComplex→comm C m zero (eq x₁) s x = ⊥.rec (CW₀-empty C (subst (fst C) x₁ x))
subComplex→comm C m zero (gt x₁) q x = ⊥.rec (CW₀-empty C x)
subComplex→comm C m (suc n) (lt x₁) (lt x₂) x = refl
subComplex→comm C m (suc n) (lt x₁) (eq x₂) x = refl
subComplex→comm C m (suc n) (lt x₁) (gt x₂) x = ⊥.rec (¬squeeze (x₁ , x₂))
subComplex→comm C m (suc n) (eq x₁) (lt x₂) x =
  ⊥.rec (¬m<ᵗm (transp (λ i → x₁ i <ᵗ suc n) i0 (<ᵗ-trans <ᵗsucm x₂)))
subComplex→comm C m (suc n) (eq x₁) (eq x₂) x =
  ⊥.rec ( falseDichotomies.eq-eq (sym x₁ , sym x₂))
subComplex→comm C m (suc n) (eq x₁) (gt x₂) x with (m ≟ᵗ suc n)
... | lt x₃ =  ⊥.rec (¬squeeze (x₂ , x₃))
... | eq x₃ = cong (CW↪ C m) (sym (cong (subst (fst C) (sym x₃))
                (transportRefl _
                ∙ cong (λ p → subst (fst C) p x) (isSetℕ _ _ x₁ x₃))
                ∙ subst⁻Subst (fst C) x₃ x))
... | gt x₃ = ⊥.rec (¬m<ᵗm (subst (suc n <ᵗ_) x₁ x₃))
subComplex→comm C m (suc n) (gt x₁) (lt x₂) x =
  ⊥.rec (¬squeeze (x₂ , <ᵗ-trans x₁ (<ᵗ-trans <ᵗsucm <ᵗsucm)))
subComplex→comm C m (suc n) (gt x₁) (eq x₂) x = (⊥.rec
       (¬m<ᵗm (transp (λ i → suc n <ᵗ x₂ i) i0 (<ᵗ-trans x₁ <ᵗsucm))))
subComplex→comm C (suc m) (suc n) (gt x₁) (gt x₂) x with m ≟ᵗ n
... | lt x₃ = ⊥.rec (¬squeeze (x₂ , x₃))
... | eq x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₃ x₁))
... | gt x₃ = cong (CW↪ C (suc m))
  λ j → CW↑Gen C (suc n) (suc m)
          (Trichotomyᵗ-suc (m ≟ᵗ suc n)) (isProp<ᵗ x₁ x₃ j) x

subComplex→Full : ∀ {ℓ} (C : CWskel ℓ) (m : ℕ) → cellMap (subComplex C m) C
SequenceMap.map (subComplex→Full C n) = subComplex→map C n
SequenceMap.comm (subComplex→Full C n) m = subComplex→comm C m n _ _

subComplex→ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) → finCellMap n (subComplex C m) C
FinSequenceMap.fmap (subComplex→ C m n) = subComplex→map C m ∘ fst
FinSequenceMap.fcomm (subComplex→ C m n) t = subComplex→comm C (fst t) m _ _

goDown : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _)
  → G.subComplexFam C m (suc m) p → G.subComplexFam C m m q
goDown C m (lt x) q = ⊥.rec (¬-suc-n<ᵗn x)
goDown C m (eq x) q = ⊥.rec (falseDichotomies.eq-eq(refl , sym x))
goDown C m (gt x) (lt x₁) = ⊥.rec (¬m<ᵗm x₁)
goDown C m (gt x) (eq x₁) = idfun _
goDown C m (gt x) (gt x₁) = ⊥.rec (¬m<ᵗm x₁)

CW↪goDown : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _) (x : _)
  → SubComplexGen.subComplexCW↪Gen C m m p q (goDown C m q p x) ≡ x
CW↪goDown C m p (lt x₁) x = ⊥.rec (¬-suc-n<ᵗn x₁)
CW↪goDown C m p (eq x₁) x = ⊥.rec (falseDichotomies.eq-eq(refl , sym x₁))
CW↪goDown C m (lt x₂) (gt x₁) x = ⊥.rec (¬m<ᵗm x₂)
CW↪goDown C m (eq x₂) (gt x₁) x =
  transportRefl _ ∙ cong (λ p → subst (fst C) p x) (isSetℕ _ _ x₂ refl)
                  ∙ transportRefl x
CW↪goDown C m (gt x₂) (gt x₁) x = ⊥.rec (¬m<ᵗm x₂)

Charac↑ : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _)
  → subComplexMapGen.subComplex→map' C m (suc m) p
   ≡ CW↪ C m ∘ subComplexMapGen.subComplex→map' C m m q ∘ goDown C m p q
Charac↑ C m p (lt x) = ⊥.rec (¬m<ᵗm x)
Charac↑ C m (lt x₁) (eq x) = ⊥.rec (¬-suc-n<ᵗn x₁)
Charac↑ C m (eq x₁) (eq x) = ⊥.rec (falseDichotomies.eq-eq (refl , sym x₁))
Charac↑ C zero (gt x₁) (eq x) = funExt (λ q → ⊥.rec (C .snd .snd .snd .fst q))
Charac↑ C (suc m) (gt x₁) (eq x) with (m ≟ᵗ m)
... | lt x₂ =  ⊥.rec (¬m<ᵗm x₂)
... | eq x₂ = funExt λ x
  → cong (CW↪ C (suc m)) (cong (λ p → subst (fst C) p x) (isSetℕ _ _ _ _)
    ∙ transportRefl x)
... | gt x₂ =  ⊥.rec (¬m<ᵗm x₂)
Charac↑ C m p (gt x) = ⊥.rec (¬m<ᵗm x)

subComplexHomologyEquiv≡ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ)  (q : suc (suc n) <ᵗ m)
  → Iso.inv (fst (subComplexHomology C m n q))
   ≡ H̃ˢᵏᵉˡ→ (suc n) (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
subComplexHomologyEquiv≡ C m n q =
  funExt (SQ.elimProp (λ _ → squash/ _ _)
    λ a → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
      (mainGen (suc n ≟ᵗ m) (suc (suc n) ≟ᵗ m) (fst a)
      ∙ (λ i → bouquetDegree ((BouquetFuns.CTB (suc n) (C .snd .fst (suc n))
       (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN))
       ∘
       f1/f2≡ i ∘
       BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) (suc n ≟ᵗ m))
       (G.subComplexα C m (suc n) (suc n ≟ᵗ m))
       (G.subComplexFam≃Pushout C m (suc n) (suc n ≟ᵗ m)
        (suc (suc n) ≟ᵗ m)))) .fst (fst a))
      ∙ refl {x = bouquetDegree (prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
                                (help q .fst) (suc n , snd (injectSuc (suc n , <ᵗ-trans (snd flast) <ᵗsucm)))) .fst (fst a)})
      ))
    ∙ cong fst (sym (H̃ˢᵏᵉˡ→β (subComplex C m) C (suc n) {f = (incl ∘ Iso.inv (realiseSubComplex m C))}
                 (help q)))
  where
  help' : (m : _)  (k : _) (q : _) →  finCellApprox (subComplex C m) C
      (λ x → incl (Iso.inv (realiseSubComplex m C) x)) k
  fst (help' m k q) = subComplex→ C m k
  snd (help' m k q) = →FinSeqColimHomotopy _ _ λ x → CW↑Gen≡ C k (suc m) (suc m ≟ᵗ suc k) q _
    ∙ cong (incl {n = suc m}) (funExt⁻ (CW↑GenComm C k (suc m) m (suc m ≟ᵗ suc k) q) x
      ∙ funExt⁻ (Charac↑ C m (suc m ≟ᵗ m) (m ≟ᵗ m)) (CW↑Gen (subComplex C m)
                  k (suc m) (Trichotomyᵗ-suc (m ≟ᵗ k)) q x)
      ∙ cong (CW↪ C m) (sym (Iso.leftInv ( (realiseSubComplex m C) ) _)
      ∙ cong (Iso.inv (realiseSubComplex m C))
        ((push _ ∙ cong (incl {n = suc m})
           (cong (CW↪ (subComplex C m) m)
             (secEq (complex≃subcomplex' C m m <ᵗsucm (m ≟ᵗ m)) _)
          ∙ CW↪goDown C m (m ≟ᵗ m) (suc m ≟ᵗ m) _))
        ∙ sym (CW↑Gen≡ (subComplex C m)  k (suc m) ((suc m) ≟ᵗ (suc k)) q x))))
    ∙ sym (push _)

  help : (q : suc (suc n) <ᵗ m) → finCellApprox (subComplex C m) C
       (λ x → incl (Iso.inv (realiseSubComplex m C) x))
      (suc (suc (suc (suc n))))
  fst (help q) = subComplex→ C m (suc (suc (suc (suc n))))
  snd (help q) with (suc (suc (suc n)) ≟ᵗ m)
  ... | lt x = help' m (suc (suc (suc (suc n)))) x .snd
  ... | eq x = funExt (subst (λ m → (x : _)
    → FinSeqColim→Colim (suc (suc (suc (suc n))))
         (finCellMap→FinSeqColim (subComplex C m) C
          (subComplex→ C m (suc (suc (suc (suc n))))) x) ≡ incl
         (Iso.inv (realiseSubComplex m C)
          (FinSeqColim→Colim (suc (suc (suc (suc n)))) x))) x
          (funExt⁻ (→FinSeqColimHomotopy _ _
            λ w → (cong (incl {n = suc (suc (suc (suc n)))})
                    (cong (subComplex→map C (suc (suc (suc n))) (suc (suc (suc (suc n)))))
                      (sym (secEq (_ , subComplexFin C (suc (suc (suc n))) (suc (suc (suc n)) , <ᵗsucm)) w)))
            ∙ ((cong (incl {n = suc (suc (suc (suc n)))})
                     (mm (suc (suc (suc n)))
                       (Trichotomyᵗ-suc (Trichotomyᵗ-suc (Trichotomyᵗ-suc (suc n ≟ᵗ n))))
                       (Trichotomyᵗ-suc (Trichotomyᵗ-suc (Trichotomyᵗ-suc (n ≟ᵗ n)))) (invEq
                       (CW↪ (subComplex C (suc (suc (suc n)))) (suc (suc (suc n))) ,
                        subComplexFin C (suc (suc (suc n))) (suc (suc (suc n)) , <ᵗsucm))
                       w))
            ∙ sym (push (FinSequenceMap.fmap
                          (fst (help' (suc (suc (suc n))) (suc (suc (suc n))) <ᵗsucm))
                          (suc (suc (suc n)) , <ᵗsucm)
                          (invEq
                           (CW↪ (subComplex C (suc (suc (suc n)))) (suc (suc (suc n))) ,
                            subComplexFin C (suc (suc (suc n))) (suc (suc (suc n)) , <ᵗsucm))
                           w))))
                   ∙ funExt⁻ (help' (suc (suc (suc n))) (suc (suc (suc n))) <ᵗsucm .snd)
                             (fincl (suc (suc (suc n)) , <ᵗsucm)
                             _)))
            ∙ cong (incl {n = suc (suc (suc n))})
                (refl ∙
                 (cong (Iso.inv (realiseSubComplex (suc (suc (suc n))) C))
                   (push _
                   ∙ cong (incl {n = suc (suc (suc (suc n)))})
                   (secEq (_ , subComplexFin C (suc (suc (suc n))) (suc (suc (suc n)) , <ᵗsucm)) w)))))))
    where
    mmmain : (n : ℕ) (x₂ : _) (x : _)
      → CW↑Gen C n (suc n) (eq (λ _ → suc n)) x₂ x ≡
           snd (snd (snd (snd (snd C))) n) .equiv-proof (inl x) .fst .fst
    mmmain zero x₂ x = ⊥.rec (C .snd .snd .snd .fst x)
    mmmain (suc n) x₂ x = cong (CW↪ C (suc n)) (transportRefl x)
    
    mm : (n : ℕ) (P : _) (Q : _) (x : _)
      → subComplexMapGen.subComplex→map' C n (suc n) P
          (invEq (G.subComplexFam≃Pushout C n n Q P) (inl x))
      ≡ CW↪ C n (subComplexMapGen.subComplex→map' C n n Q x)
    mm n P (lt x₁) x = ⊥.rec (¬m<ᵗm x₁)
    mm n (lt x₂) (eq x₁) x = ⊥.rec (¬-suc-n<ᵗn x₂)
    mm n (eq x₂) (eq x₁) x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) (sym x₂) <ᵗsucm))
    mm n (gt x₂) (eq x₁) x = ah
      where
      ah :  CW↑Gen C n (suc n) (Trichotomyᵗ-suc (n ≟ᵗ n)) x₂
         (invEq (G.subComplexFam≃Pushout C n n (eq x₁) (gt x₂)) (inl x))
         ≡ CW↪ C n (idfun (fst C n) x)
      ah with (n ≟ᵗ n)
      ... | lt x = ⊥.rec (¬m<ᵗm x)
      ... | eq q = cong₂ (λ p r → CW↑Gen C n (suc n) (eq p) x₂ (transport refl (subst (fst C) r x)))
                         (isSetℕ _ _ _ refl) (isSetℕ _ _ _ refl)
                         ∙ cong (CW↑Gen C n (suc n) (eq (λ _ → suc n)) x₂)
                           (transportRefl _ ∙ transportRefl x)
                         ∙ mmmain n x₂ x
      ... | gt x = ⊥.rec (¬m<ᵗm x)
    mm n P (gt x₁) x = ⊥.rec (¬m<ᵗm x₁)
  ... | gt x = ⊥.rec (¬squeeze (q , x))

  FIN : Fin (suc (suc (suc n)))
  FIN = suc n , <ᵗ-trans {n = suc n} {m = suc (suc n)}{k = suc (suc (suc n))} <ᵗsucm <ᵗsucm

  f1/f2gen :  (q1 : _) (q2 : _)
           → cofib (invEq (G.subComplexFam≃Pushout C m (suc n) q1 q2) ∘ inl) →
             Pushout (λ _ → tt) (invEq (C .snd .snd .snd .snd (fst FIN)) ∘ inl)
  f1/f2gen q1 q2 (inl x) = inl x
  f1/f2gen q1 q2 (inr x) = inr (subComplexMapGen.subComplex→map' C m (suc (suc n)) q2 x)
  f1/f2gen q1 q2 (push a i) =
      (push (subComplexMapGen.subComplex→map' C m (suc n) q1 a)
    ∙ λ i → inr (subComplex→comm C (suc n) m q1 q2 a i)) i

  f1/f2≡ :  f1/f2gen (suc n ≟ᵗ m) (suc (suc n) ≟ᵗ m)
         ≡ prefunctoriality.fn+1/fn (suc (suc (suc (suc n)))) (subComplex→ C m (suc (suc (suc (suc n))))) ((suc n , <ᵗ-trans-suc (<ᵗ-trans (snd flast) <ᵗsucm)))
  f1/f2≡ = funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl}


  f1/f2genId : (q1 : _) (q2 : _) → f1/f2gen (lt q1) (lt q2) ≡ idfun _
  f1/f2genId q1 q2 = funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) j
    → ((λ i → push a ∙ (λ j → inr (help2 m q1 q2 a i j))) ∙ sym (rUnit (push a))) j i}
    where
    help2 : (m : ℕ) (q1 : _) (q2 : _) (a : _) → subComplex→comm C (suc n) m (lt q1) (lt q2) a ≡ refl
    help2 (suc m) q1 q2 a = refl

  mainGen : (q1 : _) (q2 : _) (a : _)
    → Iso.inv (fst (subChainIsoGen C m (suc n , <ᵗ-trans <ᵗsucm q) q1)) a
    ≡ bouquetDegree
      (BouquetFuns.CTB (suc n) (C .snd .fst (suc n)) (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN))
      ∘ f1/f2gen q1 q2
      ∘ (BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) q1)
         (G.subComplexα C m (suc n) q1)
           (G.subComplexFam≃Pushout C m (suc n) q1 q2))) .fst a
  mainGen (lt x) (lt x₁) a = funExt⁻ (sym (cong fst (bouquetDegreeId))) a ∙ λ i → bouquetDegree (cool (~ i)) .fst a
    where
    cool : BouquetFuns.CTB (suc n) (C .snd .fst (suc n)) (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN))
         ∘ f1/f2gen (lt x) (lt x₁)
         ∘ BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) (lt x))
         (G.subComplexα C m (suc n) (lt x))
           (G.subComplexFam≃Pushout C m (suc n) (lt x) (lt x₁))
         ≡ idfun _
    cool = funExt λ a → cong (BouquetFuns.CTB (suc n) (C .snd .fst (suc n)) (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN)))
                  (funExt⁻ (f1/f2genId x x₁) _)
                ∙ CTB-BTC-cancel (suc n) (C .snd .fst (suc n)) (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN)) .fst _
  mainGen (lt x) (eq x₁) a = ⊥.rec (¬m<ᵗm (subst (suc (suc n) <ᵗ_) (sym x₁) q))
  mainGen (lt x) (gt x₁) a =  ⊥.rec (¬squeeze (x , x₁))
  mainGen (eq x) q2 a = ⊥.rec (¬m<ᵗm  (subst (_<ᵗ_ (suc n)) (sym x) (<ᵗ-trans <ᵗsucm q)))
  mainGen (gt x) q2 a = ⊥.rec (¬m<ᵗm (<ᵗ-trans x (<ᵗ-trans <ᵗsucm q)))

subComplexHomologyEquiv : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (m : ℕ) (p : suc (suc n) <ᵗ m)
  → GroupEquiv (H̃ˢᵏᵉˡ (subComplex C m) (suc n))
                (H̃ˢᵏᵉˡ C (suc n))
fst (fst (subComplexHomologyEquiv C n m p)) = H̃ˢᵏᵉˡ→ (suc n) (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
snd (fst (subComplexHomologyEquiv C n m p)) =
  subst isEquiv (subComplexHomologyEquiv≡ C m n p)
    (isoToIsEquiv (invIso (fst (subComplexHomology C m n p))))
snd (subComplexHomologyEquiv C n m p) = H̃ˢᵏᵉˡ→ (suc n) (incl ∘ Iso.inv (realiseSubComplex m C)) .snd

subComplexHomologyᶜʷEquiv : ∀ {ℓ} (C : CWexplicit ℓ) (n : ℕ) (m : ℕ) (p : suc (suc n) <ᵗ m)
  → GroupEquiv (H̃ᶜʷ ((fst (fst (snd C))) m , ∣ subComplex (snd C .fst) m , isoToEquiv (realiseSubComplex m (snd C .fst)) ∣₁) (suc n))
                (H̃ᶜʷ (realise (snd C .fst) , ∣ fst (snd C) , idEquiv _ ∣₁) (suc n))
fst (subComplexHomologyᶜʷEquiv C n m p) = H̃ᶜʷ→ (suc n) (incl {n = m}) .fst , subComplexHomologyEquiv (snd C .fst) n m p .fst .snd
snd (subComplexHomologyᶜʷEquiv C n m p) = H̃ᶜʷ→ (suc n) (incl {n = m}) .snd

--- bouquetDegreeHom


open import Cubical.HITs.Sn.Degree renaming (degreeConst to degree-const)

-- pickPetal

open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure





-- Sphere stuff
module _ {ℓ} (Xsk : CWskel ℓ) (x₀ : fst Xsk 1) where
  fn+1/fn-SGen-inr : (n m : ℕ)
    (f : S₊∙ n →∙ (fst Xsk (suc m) , CWskel∙ Xsk x₀ m))
   → (p : _) → Sgen.Sfam n (suc (suc m)) p → fst Xsk (suc m)
  fn+1/fn-SGen-inr n m f (lt x) = λ _ → CWskel∙ Xsk x₀ m
  fn+1/fn-SGen-inr n m f (eq x) = fst f
  fn+1/fn-SGen-inr n m f (gt x) = fst f

  fn+1/fn-SGenEq : (n m : ℕ)
    (f : S₊∙ n →∙ (fst Xsk (suc (suc m)) , CWskel∙ Xsk x₀ (suc m)))
    (g : S₊∙ n →∙ (fst Xsk (suc m) , CWskel∙ Xsk x₀ m))
    → (q : _) (a : Sgen.Sfam n (suc (suc m)) q)
    →  fst Xsk (suc m)
  fn+1/fn-SGenEq n m f g (lt x) a = CWskel∙ Xsk x₀ m
  fn+1/fn-SGenEq n m f g (eq x) a = g .fst a
  fn+1/fn-SGenEq n m f g (gt x) a = g .fst a
