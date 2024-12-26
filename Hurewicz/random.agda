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
open import Cubical.CW.Homology
open import Hurewicz.SubcomplexNew


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

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.LES
open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Truncation as TR

connected→πEquiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 +ℕ n) (fst f)
  → GroupEquiv (πGr n A) (πGr n B)
connected→πEquiv {ℓ = ℓ}  {A = A} {B = B} n f conf =
  (πHom n f .fst
  , subst isEquiv (funExt (ST.elim (λ _ → isSetPathImplicit) (λ _ → refl)))
    (sss .snd))
  , πHom n f .snd
  where
  lem : (n : ℕ) → suc (suc n) ∸ n ≡ 2
  lem zero = refl
  lem (suc n) = lem n

  Bat : isConnectedFun 2 (fst (Ω^→ (suc n) f))
  Bat = subst (λ k → isConnectedFun k (fst (Ω^→ (suc n) f)))
              (lem n)
              (isConnectedΩ^→ (suc (suc n)) (suc n) f conf)

  sss : π (suc n) A ≃ π (suc n) B
  sss = compEquiv setTrunc≃Trunc2
         (compEquiv (connectedTruncEquiv 2
                     (fst (Ω^→ (suc n) f)) Bat)
          (invEquiv setTrunc≃Trunc2))

GroupHomπ≅π'PathP-hom : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (n : ℕ) (f : A →∙ B)
  → PathP (λ i → GroupHomπ≅π'PathP A B n i) (πHom n f) (π'∘∙Hom n f)
GroupHomπ≅π'PathP-hom {A = A} {B = B} n f =
  (λ j → transp (λ i → GroupHomπ≅π'PathP A B n (i ∧ j)) (~ j)
                 (πHom n f))
  ▷ Σ≡Prop (λ _ → isPropIsGroupHom _ _) (π'∘∙Hom'≡π'∘∙fun n f)

connected→π'Equiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 +ℕ n) (fst f)
  → GroupEquiv (π'Gr n A) (π'Gr n B)
fst (fst (connected→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf)) = π'∘∙Hom n f .fst
snd (fst (connected→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf)) =
  transport (λ i → isEquiv (GroupHomπ≅π'PathP-hom n f i .fst))
            (connected→πEquiv n f conf .fst .snd)
snd (connected→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf) = π'∘∙Hom n f .snd

connected→πSurj : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (2 +ℕ n) (fst f)
  → isSurjective {G = πGr n A} {H = πGr n B} (πHom n f)
connected→πSurj {ℓ = ℓ}  {A = A} {B = B} n f conf =
  ST.elim (λ _ → isProp→isSet squash₁)
    λ p → TR.rec squash₁ (λ {(q , r) → ∣ ∣ q ∣₂ , (cong ∣_∣₂ r) ∣₁}) (Bat p .fst)
  where
  lem : (n : ℕ) → suc n ∸ n ≡ 1
  lem zero = refl
  lem (suc n) = lem n

  Bat : isConnectedFun 1 (fst (Ω^→ (suc n) f))
  Bat = subst (λ k → isConnectedFun k (fst (Ω^→ (suc n) f)))
              (lem n)
              (isConnectedΩ^→ (suc n) (suc n) f conf)

connected→π'Surj : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (2 +ℕ n) (fst f)
  → isSurjective (π'∘∙Hom n f)
connected→π'Surj n f conf =
  transport (λ i → isSurjective (GroupHomπ≅π'PathP-hom n f i))
            (connected→πSurj n f conf)

-- move to around pre∂ defn?
module _ {ℓ} (C : CWskel ℓ) (n : ℕ) (ptC : fst C (suc n))
         (α≡0 : (x : _) → CWskel-fields.α C (suc n) (x , ptSn n) ≡ ptC) where
  open preboundary C n
  open CWskel-fields C
  pre∂-alt : SphereBouquet n (Fin (preboundary.An+1 C n)) → SphereBouquet n (Fin (preboundary.An C n))
  pre∂-alt = fst (Bouquet≃-gen n An (α n) (e n))
            ∘ to_cofibCW n C ∘ λ { (inl x) → ptC
                                ; (inr x) → α (suc n) x
                                ; (push a i) → α≡0 a (~ i)}

Susp-pred∂ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (ptC : fst C (suc n))
       (ptCn : Fin (fst (C .snd) n))
       (α≡0 : (x : _) → CWskel-fields.α C (suc n) (x , ptSn n) ≡ ptC)
       (e≡ : CWskel-fields.e C n .fst ptC ≡ inr ptCn)
       (x : _) → preboundary.pre∂ C n x ≡ bouquetSusp→ (pre∂-alt C n ptC α≡0) x
Susp-pred∂ C zero ptC ptCn α≡0 e≡ (inl x) = refl
Susp-pred∂ C zero ptC ptCn α≡0 e≡ (inr (x , base)) = refl
Susp-pred∂ C zero ptC ptCn α≡0 e≡ (inr (x , loop i)) j = lem j i
  where
  open preboundary C zero
  open CWskel-fields C
  lem : cong (pre∂ ∘ inr ∘ (x ,_)) loop
      ≡ λ i → bouquetSusp→ (pre∂-alt C zero ptC α≡0) (inr (x , loop i))
  lem = cong (cong (isoSuspBouquet ∘ (suspFun isoCofBouquet)
           ∘ (suspFun (to_cofibCW 0 C))))
             (cong-∙∙ (δ 1 C) (push (αn+1 (x , false)))
             (λ i → inr (invEq (e 1) ((push (x , false) ∙ sym (push (x , true))) i)))
             (sym (push (αn+1 (x , true))))
             ∙ (λ j → (λ i → merid (αn+1 (x , false)) (i ∧ ~ j)) ∙∙
                    (λ i → merid (αn+1 (x , false)) (~ j ∨ i)) ∙∙ sym (merid (α 1 (x , true)))))
          ∙ (cong-∙ (isoSuspBouquet ∘ suspFun isoCofBouquet ∘ suspFun (to 0 cofibCW C))
             (merid (αn+1 (x , false))) (sym (merid (α 1 (x , true)))))
      ∙ sym (cong-∙ sphereBouquetSuspFun
               (merid (pre∂-alt C zero ptC α≡0 (inr (x , false))))
               (sym (merid (pre∂-alt C zero ptC α≡0 (inr (x , true))))))
      ∙ cong (cong (sphereBouquetSuspFun))
             ( sym (cong-∙ (suspFun (pre∂-alt C zero ptC α≡0))
                   (merid (inr (x , false))) (sym (merid (inr (x , true))))))
      ∙ cong (cong (sphereBouquetSuspFun ∘ (suspFun (pre∂-alt C zero ptC α≡0))))
             (sym (cong-∙ (Iso.inv (Iso-SuspBouquet-Bouquet (Fin An+1) λ _ → S₊∙ zero)
                         ∘ inr ∘ (x ,_))
                         (merid false) (sym (merid true))))
Susp-pred∂ C zero ptC ptCn α≡0 e≡ (push a i) = refl
Susp-pred∂ C (suc n) ptC ptCn α≡0 e≡ (inl x) = refl
Susp-pred∂ C (suc n) ptC ptCn α≡0 e≡ (inr (x , north)) = refl
Susp-pred∂ C (suc n) ptC ptCn α≡0 e≡ (inr (x , south)) = refl
Susp-pred∂ C (suc n) ptC ptCn α≡0 e≡ (inr (x , merid a i)) j = lem j i
  where
  open preboundary C (suc n)
  open CWskel-fields C
  F = isoSuspBouquet ∘ (suspFun isoCofBouquet)
           ∘ (suspFun (to_cofibCW (suc n) C))
  lem : cong (pre∂ ∘ inr ∘ (x ,_)) (merid a)
      ≡ λ i → bouquetSusp→ (pre∂-alt C (suc n) ptC α≡0) (inr (x , merid a i))
  lem = cong-∙∙ (F ∘ δ (suc (suc n)) C)
           (push (αn+1 (x , a)))
                    (λ i → inr (invEq (e (2 +ℕ n)) ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) i)))
                    (sym (push (αn+1 (x , ptSn (suc n)))))
      ∙ cong₃ _∙∙_∙∙_ refl refl
              (cong (cong F) (cong (sym ∘ merid) (α≡0 x))
            ∙ cong (sym ∘ Bouquet→ΩBouquetSusp (Fin An) (λ _ → S₊∙ (suc n)))
                   (cong (Pushout→Bouquet (suc n) (snd C .fst (suc n))
                           (snd C .snd .fst (suc n)) (snd C .snd .snd .snd (suc n)))
                             e≡)
            ∙ cong sym ((λ i → push ptCn ∙∙ (λ j → inr (ptCn , rCancel (merid (ptSn (suc n))) i j)) ∙∙ sym (push ptCn)) ∙ ∙∙lCancel (sym (push ptCn))))
      ∙ sym (compPath≡compPath' _ _)
      ∙ sym (rUnit _)
Susp-pred∂ C (suc n) ptC ptCn α≡0 e≡ (push (x , y) i) = refl

module _ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
  (f1 : A → B) (f2 : B → C) {g : A → D} where
  PushoutComp→IteratedPushout : Pushout (f2 ∘ f1) g → Pushout {C = Pushout f1 g} f2 inl
  PushoutComp→IteratedPushout (inl x) = inl x
  PushoutComp→IteratedPushout (inr x) = inr (inr x)
  PushoutComp→IteratedPushout (push a i) = (push (f1 a) ∙ λ i → inr (push a i)) i

  IteratedPushout→PushoutComp : Pushout {C = Pushout f1 g} f2 inl → Pushout (f2 ∘ f1) g
  IteratedPushout→PushoutComp (inl x) = inl x
  IteratedPushout→PushoutComp (inr (inl x)) = inl (f2 x)
  IteratedPushout→PushoutComp (inr (inr x)) = inr x
  IteratedPushout→PushoutComp (inr (push a i)) = push a i
  IteratedPushout→PushoutComp (push a i) = inl (f2 a)

  Iso-PushoutComp-IteratedPushout : Iso (Pushout (f2 ∘ f1) g) (Pushout {C = Pushout f1 g} f2 inl)
  Iso.fun Iso-PushoutComp-IteratedPushout = PushoutComp→IteratedPushout
  Iso.inv Iso-PushoutComp-IteratedPushout = IteratedPushout→PushoutComp
  Iso.rightInv Iso-PushoutComp-IteratedPushout (inl x) = refl
  Iso.rightInv Iso-PushoutComp-IteratedPushout (inr (inl x)) = push x
  Iso.rightInv Iso-PushoutComp-IteratedPushout (inr (inr x)) = refl
  Iso.rightInv Iso-PushoutComp-IteratedPushout (inr (push a i)) j =
    compPath-filler' (push (f1 a)) (λ i₁ → inr (push a i₁)) (~ j) i
  Iso.rightInv Iso-PushoutComp-IteratedPushout (push a i) j = push a (i ∧ j)
  Iso.leftInv Iso-PushoutComp-IteratedPushout (inl x) = refl
  Iso.leftInv Iso-PushoutComp-IteratedPushout (inr x) = refl
  Iso.leftInv Iso-PushoutComp-IteratedPushout (push a i) j = T j i
    where
    T = cong-∙ IteratedPushout→PushoutComp (push (f1 a)) (λ i → inr (push a i))
      ∙ sym (lUnit _)


-- move to Wedge.Properties?
module _ {ℓ ℓ'} {A : Type ℓ} (B : A → Pointed ℓ')
  where
  cofibFst : Type _
  cofibFst = cofib {A = Σ A (fst ∘ B)} {B = A} fst

  cofibFst→⋁ : cofibFst → ⋁gen A λ a → Susp∙ (fst (B a))
  cofibFst→⋁ (inl x) = inl x
  cofibFst→⋁ (inr a) = inr (a , north) 
  cofibFst→⋁ (push (a , b) i) = (push a ∙ λ i → inr (a , toSusp (B a) b i)) i

  ⋁→cofibFst : ⋁gen A (λ a → Susp∙ (fst (B a))) → cofibFst
  ⋁→cofibFst (inl x) = inl x
  ⋁→cofibFst (inr (x , north)) = inl tt
  ⋁→cofibFst (inr (x , south)) = inr x
  ⋁→cofibFst (inr (x , merid a i)) = push (x , a) i
  ⋁→cofibFst (push a i) = inl tt

  Iso-cofibFst-⋁ : Iso cofibFst (⋁gen A (λ a → Susp∙ (fst (B a))))
  Iso.fun Iso-cofibFst-⋁ = cofibFst→⋁
  Iso.inv Iso-cofibFst-⋁ = ⋁→cofibFst
  Iso.rightInv Iso-cofibFst-⋁ (inl x) = refl
  Iso.rightInv Iso-cofibFst-⋁ (inr (x , north)) = push x
  Iso.rightInv Iso-cofibFst-⋁ (inr (x , south)) i = inr (x , merid (pt (B x)) i)
  Iso.rightInv Iso-cofibFst-⋁ (inr (x , merid a i)) j =
    hcomp (λ k → λ {(i = i0) → push x (j ∨ ~ k)
                   ; (i = i1) → inr (x , merid (pt (B x)) j)
                   ; (j = i0) → compPath-filler' (push x)
                                   (λ i₁ → inr (x , toSusp (B x) a i₁)) k i
                   ; (j = i1) → inr (x , merid a i)})
          (inr (x , compPath-filler (merid a) (sym (merid (pt (B x)))) (~ j) i))
  Iso.rightInv Iso-cofibFst-⋁ (push a i) j = push a (i ∧ j)
  Iso.leftInv Iso-cofibFst-⋁ (inl x) = refl
  Iso.leftInv Iso-cofibFst-⋁ (inr x) = push (x , snd (B x))
  Iso.leftInv Iso-cofibFst-⋁ (push (a , b) i) j = help j i
    where
    help : Square (cong ⋁→cofibFst ((push a ∙ λ i → inr (a , toSusp (B a) b i))))
                  (push (a , b)) refl (push (a , (snd (B a))))
    help = (cong-∙ ⋁→cofibFst (push a) (λ i → inr (a , toSusp (B a) b i))
         ∙ sym (lUnit _)
         ∙ cong-∙ (⋁→cofibFst ∘ inr ∘ (a ,_)) (merid b) (sym (merid (snd (B a)))))
         ◁ λ i j → compPath-filler (push (a , b)) (sym (push (a , pt (B a)))) (~ i) j

{-
  cofibFst : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Iso (cofib {A = A × B} {B = A} fst) (⋁gen A λ _ → Susp∙ B)
  Iso.fun cofibFst (inl x) = inl x
  Iso.fun cofibFst (inr x) = inr (x , north)
  Iso.fun cofibFst (push (a , b) i) = (push a ∙ λ j → inr (a , {!toSusp B !})) i
  Iso.inv cofibFst = {!!}
  Iso.rightInv cofibFst = {!!}
  Iso.leftInv cofibFst = {!!}
-}


-- delete?
module falseDichotomies where
  lt-eq : {n m : ℕ} → ¬ m <ᵗ n × (m ≡ suc n)
  lt-eq {n = n} (p , q) = ¬-suc-n<ᵗn (subst (_<ᵗ n) q p)

  lt-gt : {n m : ℕ}  → ¬ m <ᵗ n × (suc n <ᵗ m)
  lt-gt (p , q) = ¬-suc-n<ᵗn (<ᵗ-trans q p)

  eq-eq : {n m : ℕ} → ¬ (m ≡ n) × (m ≡ suc n)
  eq-eq {n = n} (p , q) = ¬m<ᵗm (subst (_<ᵗ suc n) (sym p ∙ q) <ᵗsucm)

  eq-gt : {n m : ℕ} → ¬ (m ≡ n) × (suc n <ᵗ m)
  eq-gt (p , q) = lt-eq (q , cong suc (sym p))

  gt-lt : {n m : ℕ} → ¬ (n <ᵗ m) × (m <ᵗ suc n)
  gt-lt = ¬squeeze

-- subComplexIncl : ∀ {ℓ} (C : CWskel ℓ) → {!!}
-- subComplexIncl = {!!}

-- CW↑' : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) →  m <ᵗ n → fst C m → fst C n
-- CW↑' C zero (suc n) p q = ⊥.rec (C .snd .snd .snd .fst q)
-- CW↑' C (suc m) (suc n) p x with (n ≟ᵗ suc m)
-- ... | gt s = CW↪ C n (CW↑ C (suc m) n s x)
-- ... | eq q = CW↪ C n (subst (fst C) (sym q) x)
-- ... | lt s = ⊥.rec (¬squeeze (p , s))

-- TrichotomyᵗSucR : {n m : ℕ} →  Trichotomyᵗ n m → Trichotomyᵗ n (suc m)
-- TrichotomyᵗSucR {n = n} {m} (lt x) = {!lt ?!}
-- TrichotomyᵗSucR {n = n} {m} (eq x) = {!!}
-- TrichotomyᵗSucR {n = n} {m} (gt x) = {!!}

CW↑Gen : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) → Trichotomyᵗ n (suc m) → m <ᵗ n → fst C m → fst C n
CW↑Gen C zero (suc n) s p q = ⊥.rec (C .snd .snd .snd .fst q)
CW↑Gen C (suc m) (suc n) (lt x₁) p x = ⊥.rec (¬squeeze (p , x₁))
CW↑Gen C (suc m) (suc n) (eq x₁) p x =
  CW↪ C n (subst (fst C) (sym (cong predℕ x₁)) x)
CW↑Gen C (suc m) (suc n) (gt x₁) p x =
  CW↪ C n (CW↑Gen C (suc m) n (n ≟ᵗ suc (suc m)) x₁ x)

CW↑Gen≡ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ)
     (p : Trichotomyᵗ n (suc m)) (q : m <ᵗ n) (x : fst C m)
  → Path (realise C) (incl x) (incl {n = n} (CW↑Gen C m n p q x))
CW↑Gen≡ C zero (suc n) p q x = ⊥.rec (C .snd .snd .snd .fst x)
CW↑Gen≡ C (suc m) (suc n) (lt x₁) q x = ⊥.rec (¬squeeze (q , x₁))
CW↑Gen≡ C (suc m) (suc n) (eq x₁) q x = help _ (cong predℕ (sym x₁))
  where
  help : (n : ℕ) (p : suc m ≡ n) → Path (realise C) (incl x) (incl (CW↪ C n (subst (fst C) p x)))
  help = J> push x ∙ λ i → incl {n = suc (suc m)} (CW↪ C (suc m) (transportRefl x (~ i)))
CW↑Gen≡ C (suc m) (suc n) (gt x₁) q x =
    CW↑Gen≡ C (suc m) n (n ≟ᵗ suc (suc m)) x₁ x
  ∙ push (CW↑Gen C (suc m) n (n ≟ᵗ suc (suc m)) x₁ x)

module subComplexMapGen {ℓ : Level} (C : CWskel ℓ) where
  subComplex→map' : (m n : ℕ) (p : Trichotomyᵗ n m)
    → SubComplexGen.subComplexFam C m n p → fst C n
  subComplex→map' m n (lt x) = idfun _
  subComplex→map' m n (eq x) = idfun _
  subComplex→map' m n (gt x) = CW↑Gen C m n (n ≟ᵗ suc m) x
  {-
  subComplex→map' C m n with (n ≟ᵗ m)
  ... | lt x = idfun _
  ... | eq x = idfun _
  ... | gt x = CW↑Gen C m n x
-}

subComplex→map : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) → subComplexFam C m n → fst C n
subComplex→map C m n = subComplexMapGen.subComplex→map' C m n (n ≟ᵗ m)

⊥elimLem : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {x : B} {s : _} → x ≡ f (⊥.rec s)
⊥elimLem {s = ()}

subComplex→ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) → finCellMap n (subComplex C m) C
FinSequenceMap.fmap (subComplex→ C m n) (t , q) = subComplex→map C m t
FinSequenceMap.fcomm (subComplex→ C zero (suc n)) (t , q) x = ⊥.rec (C .snd .snd .snd .fst {!!})
FinSequenceMap.fcomm (subComplex→ C (suc m) (suc n)) (t , q) with (t ≟ᵗ m)
... | lt x = ltx
  where
  ltx : _
  ltx s with (t ≟ᵗ suc m)
  ... | gt x = ⊥.rec {!!}
  ... | eq x = ⊥.rec {!!}
  ... | lt x = refl
... | eq x = eqx
  where
  eqx : _
  eqx s with (t ≟ᵗ suc m)
  ... | lt x = refl
  ... | eq x = ⊥.rec {!!}
  ... | gt x = ⊥.rec {!!}
... | gt x = mx
  where
  mx : (o : _) → _ ≡ _
  mx with (t ≟ᵗ suc m)
  ... | lt x = ⊥.rec {!!}
  ... | eq x = λ o → cong (CW↪ C t) (sym (cong (subst (fst C) (sym x)) (transportRefl _) ∙ subst⁻Subst (fst C) x o ))
  ... | gt x = λ _ → refl


subComplexHomologyEquiv≡ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) (p : suc (suc n) <ᵗ m)
  → Iso.inv (fst (subComplexHomology C m n p)) ≡ Hˢᵏᵉˡ→ n (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
subComplexHomologyEquiv≡ C m n p = {!→FinSeqColimHomotopy ? ?!}
  ∙ cong fst (sym (Hˢᵏᵉˡ→β (subComplex C m) C n {f = (incl ∘ Iso.inv (realiseSubComplex m C))}
    help))
  where
  help : finCellApprox (subComplex C m) C
      (λ x → incl (Iso.inv (realiseSubComplex m C) x))
      (suc (suc (suc n)))
  fst help = subComplex→ C m (suc (suc (suc n)))
  snd help = →FinSeqColimHomotopy _ _ aa
   where
   main! : (m : ℕ) (p : suc (suc n) <ᵗ m) (x : subComplexFam C m (suc (suc (suc n)))) (q : _)
     → (CW↑Gen C (suc (suc (suc n))) (suc m))
       q p
       (subComplex→map C m (suc (suc (suc n))) x)
       ≡ CW↪ C m (Iso.inv (realiseSubComplex m C) (incl x))
   main! m p x (lt x₁) = ⊥.rec (¬squeeze (p , x₁))
   main! m p x (eq x₁) = cong (CW↪ C m) (L m (sym (cong predℕ x₁)) x)
     where
     FF : (x : _) → (fst (SubComplexGen.complex≃subcomplex' C (suc (suc (suc n))) (suc (suc (suc n))) <ᵗsucm
                      (Trichotomyᵗ-suc (Trichotomyᵗ-suc (Trichotomyᵗ-suc (n ≟ᵗ n))))))
                      (subComplex→map C (suc (suc (suc n))) (suc (suc (suc n))) x)
                  ≡ x
     FF x with (n ≟ᵗ n)
     ... | lt x₁ = ⊥.rec (¬m<ᵗm x₁)
     ... | eq x₁ = refl
     ... | gt x₁ = ⊥.rec (¬m<ᵗm x₁)

     L : (m : ℕ) (p : suc (suc (suc n)) ≡ m) (x : _)
       → subst (fst C) p (subComplex→map C m (suc (suc (suc n))) x)
        ≡ Iso.inv (realiseSubComplex m C) (incl x)
     L = J> λ x → transportRefl _
       ∙ sym (Iso.leftInv (realiseSubComplex (suc (suc (suc n))) C) _)
       ∙ cong (Iso.inv (realiseSubComplex (suc (suc (suc n))) C)) (cong incl (FF x))
   main! (suc m) p x (gt x₁) =
     cong (CW↪ C (suc m)) (sym (Iso.leftInv (realiseSubComplex (suc m) C) _)
     ∙ cong (Iso.inv (realiseSubComplex (suc m) C)) (MA _))
     where
     MA : (p : _) → Iso.fun (realiseSubComplex (suc m) C) (CW↑Gen C (suc (suc (suc n))) (suc m) p x₁
      (subComplex→map C (suc m) (suc (suc (suc n))) x))
      ≡ incl x
     MA p = cong (incl {n = suc m}) (OHA _ _)
           ∙ sym (CW↑Gen≡ (subComplex C (suc m)) (suc (suc (suc n))) (suc m) p x₁ x)
       where
       OHA : (p : _) (x : _) → G.complex≃subcomplex' C (suc m) (suc m) <ᵗsucm
                                (Trichotomyᵗ-suc (m ≟ᵗ m)) .fst
                                (CW↑Gen C (suc (suc (suc n))) (suc m) p x₁
                                 (subComplex→map C (suc m) (suc (suc (suc n))) x))
                                ≡ CW↑Gen (subComplex C (suc m)) (suc (suc (suc n))) (suc m) p x₁ x
       OHA (lt e) x = ⊥.rec (¬squeeze (x₁ , e)) -- ⊥.rec (¬squeeze (x₂ , x₁))
       OHA (eq e) x with (m ≟ᵗ m)
       ... | lt w = ⊥.rec (¬m<ᵗm w)
       ... | eq w = lemma m (cong predℕ (sym e)) w (isSetℕ _ _ _ _) x
         where
         me : (inq : _) (x : _) → CW↪ C (suc (suc (suc n)))
                   (subComplexMapGen.subComplex→map' C (suc (suc (suc (suc n)))) (suc (suc (suc n))) inq x)
                       ≡
                       invEq
                       (G.subComplexFam≃Pushout C (suc (suc (suc (suc n))))
                        (suc (suc (suc n))) inq
                        (eq (λ _ → suc (suc (suc (suc n))))))
                       (inl x)
         me (lt x₁) x = refl
         me (eq x₁) x = ⊥.rec {!!}
         me (gt x₁) x = ⊥.rec (¬-suc-n<ᵗn x₁)
         lemma : (m : ℕ)  (e : suc (suc (suc n)) ≡ m) (w : m ≡ m) (wr : refl ≡ w) (x : _)
           → CW↪ C m (subst (fst C) e (subComplex→map C (suc m) (suc (suc (suc n))) x))
           ≡ invEq (G.subComplexFam≃Pushout C (suc m) m (m ≟ᵗ suc m) (eq (cong suc w)))
                   (inl (transport (λ i → G.subComplexFam C (suc m) (e i) (e i ≟ᵗ suc m)) x))
         lemma = J> (J> λ x → cong (CW↪ C (suc (suc (suc n)))) (transportRefl _)
           ∙ me _ x
           ∙ cong (invEq (G.subComplexFam≃Pushout C (suc (suc (suc (suc n)))) (suc (suc (suc n))) ( (suc (suc (suc n))) ≟ᵗ suc  (suc (suc (suc n)))) (eq refl)) ∘ inl) (sym (transportRefl x)))
       ... | gt w = ⊥.rec (¬m<ᵗm w)
       OHA (gt e) x with (m ≟ᵗ m)
       ... | lt w = ⊥.rec (¬m<ᵗm w)
       ... | eq w = {!refl!}
         where
         TO : (x : _) → idfun (fst C (suc m))
               (snd (snd (snd (snd (snd C))) m) .equiv-proof
                (inl
                 (CW↑Gen C (suc (suc (suc n))) m (m ≟ᵗ suc (suc (suc (suc n)))) e
                  (subComplexMapGen.subComplex→map' C (suc m) (suc (suc (suc n)))
                   (Trichotomyᵗ-suc (suc (suc n) ≟ᵗ m)) x)))
                .fst .fst)
               ≡
               snd
               (G.subComplexFam≃Pushout C (suc m) m (m ≟ᵗ suc m)
                (eq (λ i → suc (w i))))
               .equiv-proof
               (inl
                (CW↑Gen (subComplex C (suc m)) (suc (suc (suc n))) m
                 (m ≟ᵗ suc (suc (suc (suc n)))) e x))
               .fst .fst
         TO = {!!}
         lemma : (w : m ≡ m) (wr : refl ≡ w) (aa : {!!}) (bb : {!!}) (x : _)
           → snd (snd (snd (snd (snd C))) m) .equiv-proof
                (inl
                 (CW↑Gen C (suc (suc (suc n))) m aa e
                  (subComplexMapGen.subComplex→map' C (suc m) (suc (suc (suc n)))
                   (Trichotomyᵗ-suc (suc (suc n) ≟ᵗ m)) x)))
                .fst .fst
                ≡
                snd
                (G.subComplexFam≃Pushout C (suc m) m (m ≟ᵗ suc m)
                 (eq (λ i → suc (w i))))
                .equiv-proof
                (inl
                 (CW↑Gen (subComplex C (suc m)) (suc (suc (suc n))) m
                  bb e x))
                .fst .fst
         lemma w p (lt x₁) bb x = {!!}
         lemma w p (eq x₁) bb x = {!!}
         lemma w p (gt x₁) bb x = {!!}
       ... | gt w = ⊥.rec (¬m<ᵗm w)

   aa : (x : subComplexFam C m (suc (suc (suc n)))) →
      incl (subComplex→map C m (suc (suc (suc n))) x) ≡
      incl (Iso.inv (realiseSubComplex m C) (incl x))
   aa x = CW↑Gen≡ C (suc (suc (suc n))) (suc m) (Trichotomyᵗ-suc (m ≟ᵗ suc (suc (suc n)))) -- (Trichotomyᵗ-suc (m ≟ᵗ suc (suc (suc n))))
                    p (subComplex→map C m (suc (suc (suc n))) x)
        ∙ cong (incl {n = suc m}) (main! m p x _)
        ∙ sym (push _)

subComplexHomologyEquiv : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (m : ℕ) (p : suc (suc n) <ᵗ m)
  → GroupEquiv (Hˢᵏᵉˡ (subComplex C (suc (suc (suc n)))) n)
                (Hˢᵏᵉˡ C n)
fst (subComplexHomologyEquiv C n m p) = {!Hˢᵏᵉˡ→ ? ?!}
snd (subComplexHomologyEquiv C n m p) = {!!}
