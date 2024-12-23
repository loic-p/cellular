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

