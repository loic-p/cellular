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


open import Cubical.CW.Properties
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
  {-
  help pp s zero t x = {!!}
  help (lt x₁) s (suc n) p t pp x = 
  help (eq x₁) s (suc n) p t pp x = cong (CW↪ C n) {!!}
    ∙ funExt⁻ (CW↪CommSubComplex C n k)
        ((subst (λ m₁ → subComplexFam C k m₁)
          (λ i → predℕ (x₁ (~ i))) (subst (G.subComplexFam C k (suc m)) pp x)))
  help (gt x₁) s (suc n) p t pp x =
    cong (CW↪ C n) {!help ? ? !}
    ∙ funExt⁻ (CW↪CommSubComplex C n k)
       ((CW↑Gen (subComplex C k) (suc m) n (n ≟ᵗ suc (suc m)) x₁
        (subst (G.subComplexFam C k (suc m)) pp x)))
        -}
  {-
  help (lt x₂) (lt x₁) pp x =  ⊥.rec (¬squeeze (t , x₂)) 
  help (eq x₂) (lt x₁) pp x = cong (CW↪ C n) {!!}
    ∙ funExt⁻ (CW↪CommSubComplex C n k) ((subst (λ m₁ → subComplexFam C k m₁) (λ i → predℕ (x₂ (~ i))) (subst (G.subComplexFam C k (suc m)) pp x)))
  help (gt x₂) (lt x₁) pp x = {!!}
  help p (eq x₁) pp x  = {!!}
  help p (gt x₁) pp x = {!!}
  -}
{-
  funExt λ q → help n (cong predℕ (sym x)) (suc m ≟ᵗ k) q (suc n ≟ᵗ k) (n ≟ᵗ k) λ i → predℕ (x (~ i)) ≟ᵗ k
-- {!CW↪SubComplexCharac C (suc m) k!}
  where
  help : (n : ℕ) (p : suc m ≡ n) (t : _) (q : G.subComplexFam C k (suc m) t) (t' : _) (s : _)
    → (pp : PathP (λ i → Trichotomyᵗ (p i) k) t s)
    → CW↪ C n (subst (fst C) p (subComplexMapGen.subComplex→map' C k (suc m) t q))
    ≡ subComplexMapGen.subComplex→map' C k (suc n) t'
        (invEq (G.subComplexFam≃Pushout C k n s t')
          (inl (transport (λ i → G.subComplexFam C k (p i) (pp i)) q)))
  help = J> λ t q t' → J> cong (CW↪ C (suc m)) (transportRefl _)
    ∙ {!!}
    ∙ cong (subComplexMapGen.subComplex→map' C k (suc (suc m)) t')
       (cong (invEq (G.subComplexFam≃Pushout C k (suc m) t t'))
         λ j → inl (transportRefl q (~ j)))
-}
-- CW↑GenComm C (suc m) (suc n) zero (gt x) t = funExt {!!}
-- CW↑GenComm C (suc m) (suc n) (suc k) (gt x) t = {!!}
{- with (suc n ≟ᵗ k)
... | lt x₁ = funExt λ r → {!!} ∙ {!!}
... | eq x₁ = {!!}
  where
  help : {!!}
  help = {!!}
... | gt x₁ = funExt λ r → {!CW↑GenComm C k (suc m) !}
-}
{-
 -- subComplex→map C k (suc n) ∘
      (λ x₁ →
         CW↪ (subComplex C k) n
         (CW↑Gen (subComplex C k) (suc m) n (n ≟ᵗ suc (suc m)) x x₁))
-}
-- ⊥elimLem : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {x : B} {s : _} → x ≡ f (⊥.rec s)
-- ⊥elimLem {s = ()}

subComplex→comm : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) (p : _) (q : _) (x : G.subComplexFam C n m p)
    → CW↪ C m (subComplexMapGen.subComplex→map' C n m p x)
    ≡ subComplexMapGen.subComplex→map' C n (suc m) q (SubComplexGen.subComplexCW↪Gen C n m p q x)
subComplex→comm C m zero (eq x₁) s x = ⊥.rec (CW₀-empty C (subst (fst C) x₁ x))
subComplex→comm C m zero (gt x₁) q x = ⊥.rec (CW₀-empty C x)
subComplex→comm C m (suc n) (lt x₁) (lt x₂) x = refl
subComplex→comm C m (suc n) (lt x₁) (eq x₂) x = refl
subComplex→comm C m (suc n) (lt x₁) (gt x₂) x = ⊥.rec (¬squeeze (x₁ , x₂))
subComplex→comm C m (suc n) (eq x₁) (lt x₂) x = ⊥.rec (¬m<ᵗm (transp (λ i → x₁ i <ᵗ suc n) i0 (<ᵗ-trans <ᵗsucm x₂)))
subComplex→comm C m (suc n) (eq x₁) (eq x₂) x = ⊥.rec ( falseDichotomies.eq-eq (sym x₁ , sym x₂))
subComplex→comm C m (suc n) (eq x₁) (gt x₂) x with (m ≟ᵗ suc n)
... | lt x₃ =  ⊥.rec (¬squeeze (x₂ , x₃))
... | eq x₃ = cong (CW↪ C m) (sym (cong (subst (fst C) (sym x₃)) (transportRefl _ ∙ cong (λ p → subst (fst C) p x) (isSetℕ _ _ x₁ x₃)) ∙ subst⁻Subst (fst C) x₃ x))
... | gt x₃ = ⊥.rec (¬m<ᵗm (subst (suc n <ᵗ_) x₁ x₃))
subComplex→comm C m (suc n) (gt x₁) (lt x₂) x = (⊥.rec (¬squeeze (x₂ , <ᵗ-trans x₁ (<ᵗ-trans <ᵗsucm <ᵗsucm))))
subComplex→comm C m (suc n) (gt x₁) (eq x₂) x = (⊥.rec
       (¬m<ᵗm (transp (λ i → suc n <ᵗ x₂ i) i0 (<ᵗ-trans x₁ <ᵗsucm))))
subComplex→comm C (suc m) (suc n) (gt x₁) (gt x₂) x with m ≟ᵗ n
... | lt x₃ = ⊥.rec (¬squeeze (x₂ , x₃))
... | eq x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₃ x₁))
... | gt x₃ = cong (CW↪ C (suc m)) λ j → CW↑Gen C (suc n) (suc m) (Trichotomyᵗ-suc (m ≟ᵗ suc n)) (isProp<ᵗ x₁ x₃ j) x

subComplex→Full : ∀ {ℓ} (C : CWskel ℓ) (m : ℕ) → cellMap (subComplex C m) C
SequenceMap.map (subComplex→Full C n) = subComplex→map C n
SequenceMap.comm (subComplex→Full C n) m = subComplex→comm C m n _ _

subComplex→ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) → finCellMap n (subComplex C m) C
FinSequenceMap.fmap (subComplex→ C m n) = subComplex→map C m ∘ fst
FinSequenceMap.fcomm (subComplex→ C m n) t = subComplex→comm C (fst t) m _ _

-- subComplex→ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) → finCellMap n (subComplex C m) C
-- FinSequenceMap.fmap (subComplex→ C m n) (t , q) = subComplex→map C m t
-- FinSequenceMap.fcomm (subComplex→ C zero (suc n)) (t , q) x with (t ≟ᵗ 0)
-- ... | eq x₁ = ⊥.rec
--       (C .snd .snd .snd .fst
--        (snd (G.subComplexFam≃Pushout C 0 t (eq x₁) (gt tt)) .equiv-proof
--         (inl x) .fst .fst))
-- ... | gt x₁ = ⊥.rec (C .snd .snd .snd .fst x)
-- FinSequenceMap.fcomm (subComplex→ C (suc m) (suc n)) (t , q) with (t ≟ᵗ m)
-- ... | lt x = ltx
--   where
--   ltx : _
--   ltx s with (t ≟ᵗ suc m)
--   ... | gt s = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans s x))
--   ... | eq s = ⊥.rec (¬-suc-n<ᵗn ((subst (suc t <ᵗ_) (sym s) x)))
--   ... | lt s = refl
-- ... | eq x = eqx
--   where
--   eqx : _
--   eqx s with (t ≟ᵗ suc m)
--   ... | lt s = refl
--   ... | eq s = ⊥.rec (falseDichotomies.eq-eq (x , s))
--   ... | gt s = ⊥.rec (¬-suc-n<ᵗn (subst (suc m <ᵗ_) x s))
-- ... | gt x = mx
--   where
--   mx : (o : _) → _ ≡ _
--   mx with (t ≟ᵗ suc m)
--   ... | lt s = ⊥.rec (¬squeeze (s , x))
--   ... | eq x = λ o
--     → cong (CW↪ C t) (sym (cong (subst (fst C) (sym x)) (transportRefl _)
--      ∙ subst⁻Subst (fst C) x o ))
--   ... | gt x = λ _ → refl

-- subComplexHomologyEquiv≡ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) (p : suc (suc n) <ᵗ m)
--   → (e : realise (subComplex C m) ≃ fst C m)
--   → ((x : _) → fst e (incl {n = m} x)
--                ≡ subst (G.subComplexFam C m m) (isPropTrichotomyᵗ (m ≟ᵗ m) (eq refl)) x)
--   → Iso.inv (fst (subComplexHomology C m n p)) ≡ Hˢᵏᵉˡ→ n (incl ∘ fst e) .fst
-- subComplexHomologyEquiv≡ C m n p e ide = {!!} -- funExt {!!}
--   where
--   help : finCellApprox (subComplex C m) C
--       (λ x → incl (fst e x))
--       (suc (suc (suc n)))
--   fst help = subComplex→ C m (suc (suc (suc n)))
--   snd help = →FinSeqColimHomotopy _ _ {!fst e!}-- →FinSeqColimHomotopy _ _ (λ x → main (suc (suc (suc n)) ≟ᵗ m) x refl ∙ {!!})
--     where
--     mainS : (b : ℕ) (t : b <ᵗ suc (suc (suc (suc n)))) (x : _) → incl (subComplex→map C m b x) ≡ incl (fst e (incl x))
--     mainS zero t x = {!!}
--     mainS (suc b) t x = {!!}
    
  
--     main : (p : _)  (x : _) (q : p ≡ (suc (suc (suc n)) ≟ᵗ m)) → Path (realise C) (incl {n = suc(suc (suc n))}
--       (subComplexMapGen.subComplex→map' C m (suc (suc (suc n)))
--        p x))
--      ( incl (fst e (incl (subst (G.subComplexFam C m (suc (suc (suc n)))) q x))))
--     main (lt x₁) x q = {!!} ∙ {!!} ∙  cong (incl {n = m}) (sym (ide _) ∙ {!!} ∙ cong (fst e) {!sym (CW↑Gen≡ C (suc (suc (suc n))) m ? x₁ ?)!})
--     main (eq x₁) x q = {!!}
--     main (gt x₁) x q = {!!}

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
  transportRefl _ ∙ cong (λ p → subst (fst C) p x) (isSetℕ _ _ x₂ refl) ∙ transportRefl x
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

subComplexHomologyEquiv≡ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) (p : suc (suc n) <ᵗ m)
  → Iso.inv (fst (subComplexHomology C m n p)) ≡ Hˢᵏᵉˡ→ n (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
subComplexHomologyEquiv≡ C m n p =
  funExt (SQ.elimProp (λ _ → squash/ _ _) λ a → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _) (main (fst a)))) -- funExt {!!}
  ∙ cong fst (sym (Hˢᵏᵉˡ→β (subComplex C m) C n {f = (incl ∘ Iso.inv (realiseSubComplex m C))}
    help))
  where
  help : finCellApprox (subComplex C m) C
      (λ x → incl (Iso.inv (realiseSubComplex m C) x))
      (suc (suc (suc n)))
  fst help = subComplex→ C m (suc (suc (suc n)))
  snd help = →FinSeqColimHomotopy _ _ λ x → CW↑Gen≡ C (suc (suc (suc n))) (suc m) (suc m ≟ᵗ suc (suc (suc (suc n)))) p _
    ∙ cong (incl {n = suc m}) (funExt⁻ (CW↑GenComm C (suc (suc (suc n))) (suc m) m (suc m ≟ᵗ suc (suc (suc (suc n)))) p) x
      ∙ funExt⁻ (Charac↑ C m (suc m ≟ᵗ m) (m ≟ᵗ m)) (CW↑Gen (subComplex C m)
                  (suc (suc (suc n))) (suc m) (Trichotomyᵗ-suc (m ≟ᵗ suc (suc (suc n)))) p x)  -- funExt⁻ (Charac↑ C m _ ?) 
      ∙ cong (CW↪ C m) (sym (Iso.leftInv ( (realiseSubComplex m C) ) _)
      ∙ cong (Iso.inv (realiseSubComplex m C))
        ((push _ ∙ cong (incl {n = suc m}) (cong (CW↪ (subComplex C m) m) (secEq (complex≃subcomplex' C m m <ᵗsucm (m ≟ᵗ m)) _)
          ∙ CW↪goDown C m (m ≟ᵗ m) (suc m ≟ᵗ m) _))
        ∙ sym (CW↑Gen≡ (subComplex C m)  (suc (suc (suc n))) (suc m) ((suc m) ≟ᵗ (suc (suc (suc (suc n))))) p x))))
    ∙ sym (push _) -- mainna x (suc (suc (suc n)) ≟ᵗ m)

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

  f1/f2≡ : f1/f2gen (suc n ≟ᵗ m) (suc (suc n) ≟ᵗ m)
         ≡ prefunctoriality.fn+1/fn (suc (suc (suc n))) (subComplex→ C m (suc (suc (suc n)))) FIN
  f1/f2≡ = funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl}

  f1/f2genId : (q1 : _) (q2 : _) → f1/f2gen (lt q1) (lt q2) ≡ idfun _
  f1/f2genId q1 q2 = funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) j
    → ((λ i → push a ∙ (λ j → inr (help2 m q1 q2 a i j))) ∙ sym (rUnit (push a))) j i}
    where
    help2 : (m : ℕ) (q1 : _) (q2 : _) (a : _) → subComplex→comm C (suc n) m (lt q1) (lt q2) a ≡ refl
    help2 (suc m) q1 q2 a = refl

  mainGen : (q1 : _) (q2 : _) (a : _)
    → Iso.inv (fst (subChainIsoGen C m (suc n , <ᵗ-trans <ᵗsucm p) q1)) a
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
  mainGen (lt x) (eq x₁) a = ⊥.rec (¬m<ᵗm (subst (suc (suc n) <ᵗ_) (sym x₁) p))
  mainGen (lt x) (gt x₁) a =  ⊥.rec (¬squeeze (x , x₁))
  mainGen (eq x) q2 a = ⊥.rec (¬m<ᵗm  (subst (_<ᵗ_ (suc n)) (sym x) (<ᵗ-trans <ᵗsucm p)))
  mainGen (gt x) q2 a = ⊥.rec (¬m<ᵗm (<ᵗ-trans x (<ᵗ-trans <ᵗsucm p)))

  main : (a : _) → Iso.inv
      (fst (subChainIso C m (suc n , <ᵗ-trans <ᵗsucm p)))
      a
      ≡ _
  main a = mainGen (suc n ≟ᵗ m) (suc (suc n) ≟ᵗ m) a
        ∙ λ j → bouquetDegree
      (BouquetFuns.CTB (suc n) (C .snd .fst (suc n))
       (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN))
       ∘
       f1/f2≡ j ∘
       BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) (suc n ≟ᵗ m))
       (G.subComplexα C m (suc n) (suc n ≟ᵗ m))
       (G.subComplexFam≃Pushout C m (suc n) (suc n ≟ᵗ m)
        (suc (suc n) ≟ᵗ m)))
      .fst a

subComplexHomologyEquiv : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (m : ℕ) (p : suc (suc n) <ᵗ m)
  → GroupEquiv (Hˢᵏᵉˡ (subComplex C m) n)
                (Hˢᵏᵉˡ C n)
fst (fst (subComplexHomologyEquiv C n m p)) = Hˢᵏᵉˡ→ n (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
snd (fst (subComplexHomologyEquiv C n m p)) =
  subst isEquiv (subComplexHomologyEquiv≡ C m n p)
    (isoToIsEquiv (invIso (fst (subComplexHomology C m n p))))
snd (subComplexHomologyEquiv C n m p) = Hˢᵏᵉˡ→ n (incl ∘ Iso.inv (realiseSubComplex m C)) .snd

subComplexHomologyᶜʷEquiv : ∀ {ℓ} (C : CWexplicit ℓ) (n : ℕ) (m : ℕ) (p : suc (suc n) <ᵗ m)
  → GroupEquiv (Hᶜʷ ((fst (fst (snd C))) m , ∣ subComplex (snd C .fst) m , isoToEquiv (realiseSubComplex m (snd C .fst)) ∣₁) n)
                (Hᶜʷ (realise (snd C .fst) , ∣ fst (snd C) , idEquiv _ ∣₁) n)
fst (subComplexHomologyᶜʷEquiv C n m p) = Hᶜʷ→ n (incl {n = m}) .fst , subComplexHomologyEquiv (snd C .fst) n m p .fst .snd
snd (subComplexHomologyᶜʷEquiv C n m p) = Hᶜʷ→ n (incl {n = m}) .snd
