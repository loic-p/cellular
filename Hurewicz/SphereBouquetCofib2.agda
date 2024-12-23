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



module _ {ℓ ℓ'} {A : Type ℓ} (B : A → Pointed ℓ') -- → Iso (cofib {A = Σ A (fst B)} {B = A} fst) (⋁gen A λ a → Susp∙ (fst (B a)))
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


-- To compute : cofibre of wedge map α : S₊

SphereBouquetMap : (c1 c2 : ℕ) (n : ℕ) → Type
SphereBouquetMap c1 c2 n =
  SphereBouquet (suc n) (Fin c1) → SphereBouquet (suc n) (Fin c2)

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


{-
inr a ≡
      BouquetFuns.BTC (suc n) c2 (λ _ → tt)
      (compEquiv (SphereBouquet/EqBottomMain* c1 c2 α)
       (pathToEquiv (λ i → cofib (λ r₁ → fst r₁))))
      a
————————————————————————————————————————————————————————————
a      : SphereBouquet (suc n) (Fin c2)
-}

BTC-inr : ∀ {ℓ} {Cₙ Cₙ₊₁ : Type ℓ} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    (t : _)
    → Pushout→Bouquet n mₙ αₙ e {!αₙ !} ≡ {!!} -- inr {!!}
BTC-inr = {!!}

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

--   SphereBouquet/FamTopElement : cofib α ≃ SphereBouquet/Fam (3 +ℕ n)
--   SphereBouquet/FamTopElement with (dich2 (suc (suc n)))
--   ... | lt x = ⊥.rec (¬-suc-n<ᵗn x)
--   ... | eq x = ⊥.rec (falseDichotomies.eq-eq (x , refl))
--   ... | gt x = idEquiv _



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

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' : (p : Trichotomyᵗ (suc n) (suc n)) (q :  Trichotomyᵗ (suc n) (suc (suc n)))
    → (Fin (SphereBouquet/Card* c1 c2 (suc n) p q) → ℤ) → ℤ[Fin c2 ] .fst
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (lt x) q = λ _ _ → 0
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (eq x) (lt x₁) = λ f → f
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (eq x) (eq x₁) = λ f → f
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (eq x) (gt x₁) = λ f → f
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (gt x) q = λ _ _ → 0
  {- with dich1 n | (dich2 (suc n))
  ... | lt x | t = λ _ _ → 0
  ... | eq x | lt x₁ = λ f → f
  ... | eq x | eq x₁ = λ f → f
  ... | eq x | gt x₁ = λ f → f
  ... | gt x | t = λ _ _ → 0
-}

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap : Hˢᵏᵉˡ SphereBouquet/ˢᵏᵉˡ n .fst → ℤ[]/ImSphereMap .fst
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap =
    SQ.elim {!!}
      (λ f → [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) (fst f) ])
      λ {(a , ak) (b , bk) → PT.elim {!!} λ {(t , s) → main a b ak bk (t , cong fst s)}}
      where
{-
-- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh* :
-- --     (a b : Fin (SphereBouquet/Card (suc n)) → ℤ)
-- --     → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst a ≡ (λ _ → 0)
-- --     → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst b ≡ (λ _ → 0)
-- --     → (r : Σ[ t ∈ (Fin (SphereBouquet/Card (suc (suc n))) → ℤ) ]
-- --              ∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n) .fst t ≡ λ q → a q - b q)
-- --     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun a
-- --      ≡ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun b
-}

      card1≡ : (p : _) (q : _) → c1 ≡ SphereBouquet/Card* c1 c2 {n = n} (suc (suc n)) p q
      card1≡ (lt x) q = ⊥.rec (¬-suc-n<ᵗn x)
      card1≡ (eq x) q = ⊥.rec (falseDichotomies.eq-eq (refl , (cong predℕ (sym x))))
      card1≡ (gt x) (lt x₁) = ⊥.rec (¬m<ᵗm x₁)
      card1≡ (gt x) (eq x₁) = refl
      card1≡ (gt x) (gt x₁) = ⊥.rec (¬m<ᵗm x₁)

      card2≡ : (p : _) (q : _) → c2 ≡ SphereBouquet/Card* c1 c2 {n = n} (suc n) p q
      card2≡ (lt x) q = ⊥.rec (¬m<ᵗm x)
      card2≡ (eq x) q = refl
      card2≡ (gt x) q = ⊥.rec (¬m<ᵗm x)

      toho : PathP (λ i → SphereBouquet (suc (suc n)) (Fin (card1≡ (suc (suc n) ≟ᵗ suc n) (suc (suc n) ≟ᵗ suc (suc n)) i))
                        → SphereBouquet (suc (suc n)) (Fin (card2≡ (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) i)))
                   (bouquetSusp→ α)
                   (preboundary.pre∂ SphereBouquet/ˢᵏᵉˡ (suc n))
      toho with (n ≟ᵗ n) | (n ≟ᵗ suc n) | (suc n ≟ᵗ n)
      ... | lt x | b | c = ⊥.rec (¬m<ᵗm x)
      ... | eq x | lt x₁ | lt x₂ = ⊥.rec (¬-suc-n<ᵗn x₂)
      ... | eq x | lt x₁ | eq x₂ = ⊥.rec (falseDichotomies.eq-eq (x , sym x₂))
      ... | eq x | lt x₁ | gt x₂ = {!!}
      ... | eq x | eq x₁ | c = ⊥.rec (falseDichotomies.eq-eq (x , x₁))
      ... | eq x | gt x₁ | c = ⊥.rec (¬-suc-n<ᵗn x₁)
      ... | gt x | b | c = ⊥.rec (¬m<ᵗm x)


      module _ (a b : Fin (SphereBouquet/Card* c1 c2 (suc n) (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n))) → ℤ)
               (ak : ∂ SphereBouquet/ˢᵏᵉˡ n .fst a ≡ (λ _ → 0)) (bk : ∂ SphereBouquet/ˢᵏᵉˡ n .fst b ≡ (λ _ → 0))
               (r : Σ[ t ∈ (Fin (SphereBouquet/Card* c1 c2 (suc (suc n)) (suc (suc n) ≟ᵗ suc n) (suc (suc n) ≟ᵗ suc (suc n))) → ℤ) ]
                      ∂ SphereBouquet/ˢᵏᵉˡ (suc n) .fst t ≡ λ q → a q - b q) where

        cons : Σ[ a ∈ fst SphereBouquet/ˢᵏᵉˡ (suc (suc n)) ]
                 Σ[ b ∈ Fin (fst (SphereBouquet/ˢᵏᵉˡ .snd) (suc n)) ]
                 ((x : _) → CWskel-fields.α SphereBouquet/ˢᵏᵉˡ (suc (suc n)) (x , ptSn (suc n))  ≡ a)
               × (CWskel-fields.e SphereBouquet/ˢᵏᵉˡ (suc n) .fst a ≡ inr b)
        cons with (n ≟ᵗ n) | (n ≟ᵗ suc n)
        ... | lt x | q = ⊥.rec (¬m<ᵗm x)
        ... | eq x | lt x₁ = (inl tt) , ({!!} , {!!} , {!!})
        ... | eq x | eq x₁ = ⊥.rec (falseDichotomies.eq-eq (x , x₁))
        ... | eq x | gt x₁ = ⊥.rec (falseDichotomies.eq-gt (x , x₁))
        ... | gt x | q = ⊥.rec (¬m<ᵗm x)

        lem* = Susp-pred∂ SphereBouquet/ˢᵏᵉˡ (suc n) (fst cons)
                          (fst (snd cons))
                          (snd (snd cons) .fst) (snd (snd cons) .snd)

        main : Path (ℤ[]/ImSphereMap .fst)
                 [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) a ]
                [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (suc n ≟ᵗ suc n) (suc n ≟ᵗ suc (suc n)) b ]
        main  with (n ≟ᵗ n) | (n ≟ᵗ suc n) | (suc n ≟ᵗ n)
        ... | lt x | st | ah = ⊥.rec (¬m<ᵗm x)
        ... | eq x | lt x₁ | lt x₂ = ⊥.rec (¬-suc-n<ᵗn x₂)
        ... | eq x | lt x₁ | eq x₂ = ⊥.rec (falseDichotomies.eq-eq (x , sym x₂))
        ... | eq x | lt x₁ | gt x₂ = PT.rec (squash/ _ _) (λ apt →
          eq/ _ _ ∣ (fst r) , ((λ i → bouquetDegree α .fst (fst r))
                            ∙ funExt⁻ (cong fst (bouquetDegreeSusp α)) (fst r) -- preboundary.An+1 SphereBouquet/ˢᵏᵉˡ (suc n)
                            ∙ λ i → bouquetDegree (M {!!} x (isSetℕ _ _ refl x) (~ i)) .fst (fst r)) ∙ snd r ∣₁) α∙
          where
          -- MO : (x : _) → (Iso.fun sphereBouquetSuspIso
          --   ∘ suspFun (Iso.fun (BouquetIso-gen (suc n) c2
          --               (λ _ → tt)
          --               (SphereBouquet/EqBottomMain* c1 c2 α)))
          --  ∘ suspFun inr
          --  ∘ δ-pre ((invEq (SphereBouquet/EqTop** c1 c2 (suc n) α refl) ∘ inl))
          --   ∘ Iso.inv (BouquetIso-gen (suc (suc n)) c1
          --       (λ x₃ → α (inr (fst x₃ , subst (S₊ ∘ suc) refl (snd x₃))))
          --       (SphereBouquet/EqTop** c1 c2 (suc n) α refl))) x ≡ bouquetSusp→ α x
          -- MO (inl x) = refl
          -- MO (inr (x , north)) = refl
          -- MO (inr (x , south)) = refl
          -- MO (inr (x , merid a i)) = {!!}
          -- MO (push a i) = refl

          module _ (x : n ≡ n) where
            FIs : Iso _ _
            FIs = (BouquetIso-gen (suc n) c2
                          (λ _ → tt)
                          (compEquiv (SphereBouquet/EqBottomMain* c1 c2 α)
                          (pathToEquiv (λ i → cofib {A = Fin c2 × S₊ (x (~ i))} fst))))

            F2' = Iso.fun (BouquetIso-gen (suc n) c2
                          (λ _ → tt)
                          (compEquiv (SphereBouquet/EqBottomMain* c1 c2 α)
                          (pathToEquiv (λ i → cofib {A = Fin c2 × S₊ (x (~ i))} fst))))
                          
            F1 = Iso.fun sphereBouquetSuspIso
            F2 = suspFun (Iso.fun (BouquetIso-gen (suc n) c2
                          (λ _ → tt)
                          (compEquiv (SphereBouquet/EqBottomMain* c1 c2 α)
                            (pathToEquiv (λ i → cofib {A = Fin c2 × S₊ (x (~ i))} fst)))))
            F3 = suspFun inr
            F4 = δ-pre ((invEq (SphereBouquet/EqTop** c1 c2 (suc n) α (cong suc x)) ∘ inl))
            F5 = F1 ∘ F2 ∘ F3 ∘ F4
            F5' = F1 ∘ F2 ∘ F3

          F2'help : {!!}
          F2'help = {!Pushout→Bouquet (suc n) c2 (λ _ → tt)
(compEquiv (SphereBouquet/EqBottomMain* c1 c2 α)
 (pathToEquiv (λ i → cofib (λ r₁ → fst r₁))))
(Cubical.HITs.Pushout.Base.transpPushout (λ i _ → tt)
 (λ i r₁ → fst r₁) i0
 (⋁→cofibFst (λ _ → S₊∙ n)
  (Cubical.HITs.Pushout.Properties.pushoutIso→ (λ _ → tt)
   (λ z → z , ptSn (suc n)) (λ _ → tt) (λ z → z , north)
   (idEquiv (Fin c2)) (idEquiv Unit)
   (Σ-cong-equiv-snd (λ a₁ → isoToEquiv (IsoSucSphereSusp n)))
   (λ _ a₁ → tt)
   (funExt (λ a₁ → ΣPathP ((λ _ → a₁) , IsoSucSphereSusp∙' n))) a)))!}
      
          F2'≡id : (a : _) → F2' refl (inr a) ≡ a
          F2'≡id a = (cong (Pushout→Bouquet (suc n) c2 (λ _ → tt)
              (compEquiv (SphereBouquet/EqBottomMain* c1 c2 α)
               (pathToEquiv (λ i → cofib (λ r₁ → fst r₁))))) (transportRefl {!a!}) ∙ {!!})
                   ∙ {!Iso.inv (FIs refl) a!}

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
          M = {!!}
          -- J> funExt λ { (inl x) → refl
          --                 ; (inr (x , north)) → refl
          --                 ; (inr (x , south)) → refl
          --                 ; (inr (x , merid a i)) j → MaIn x a j i
          --                 ; (push a i) → refl}
          bouquetDegreeEq : ∀ {a b c : ℕ} {α β : SphereBouquet a (Fin b) → SphereBouquet a (Fin c)} → α ≡ β → (r : fst ℤ[Fin b ]) → bouquetDegree α .fst r ≡ bouquetDegree β .fst r
          bouquetDegreeEq = {!!}
          lem : bouquetDegree α ≡ bouquetDegree {!!}
          lem = {!!}
        ... | eq x | eq x₁ | ah = ⊥.rec (falseDichotomies.eq-eq (x , x₁))
        ... | eq x | gt x₁ | ah = ⊥.rec (¬-suc-n<ᵗn x₁)
        ... | gt x | st | ah = ⊥.rec (¬m<ᵗm x)
{-
  ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/ : ℤ[]/ImSphereMap .fst → Hˢᵏᵉˡ SphereBouquet/ˢᵏᵉˡ n .fst
  ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/ = SQ.elim {!!}
    (λ f → [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' {!f!} {!!} f , {!!} ])
    {!!}
-}

--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- : (f : _) (a : _)
--     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (-_ ∘ f) a
--      ≡ - HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' f a
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres-  f a with dich1 n | (dich2 (suc n))
--   ... | lt x | q = refl
--   ... | eq x | lt x₁ = refl
--   ... | eq x | eq x₁ = refl
--   ... | eq x | gt x₁ = refl
--   ... | gt x | q = refl

-- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ : (f g : _) (a : _)
-- --     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (λ x → f x + g x) a
-- --     ≡ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' f a + HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' g a
-- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ f g a with dich1 n | (dich2 (suc n))
-- --   ... | lt x | q = refl
-- --   ... | eq x | lt x₁ = refl
-- --   ... | eq x | eq x₁ = refl
-- --   ... | eq x | gt x₁ = refl
-- --   ... | gt x | q = refl


-- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun : (Fin (SphereBouquet/Card (suc n)) → ℤ) → ℤ[]/ImSphereMap .fst
-- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun = [_] ∘ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'

-- --   SphereBouquet/Card2≡ : SphereBouquet/Card (suc n) ≡ c2
-- --   SphereBouquet/Card2≡ with  dich1 n | (dich2 (suc n))
-- --   ... | lt x | q = ⊥.rec (¬m<ᵗm x)
-- --   ... | eq x | lt x₁ = refl
-- --   ... | eq x | eq x₁ = refl
-- --   ... | eq x | gt x₁ = refl
-- --   ... | gt x | q = ⊥.rec (¬m<ᵗm x)

-- --   SphereBouquet/Card1≡ : SphereBouquet/Card (suc (suc n)) ≡ c1
-- --   SphereBouquet/Card1≡ with dich1 (suc n) | dich2 (suc n)
-- --   ... | p | lt x = ⊥.rec (¬m<ᵗm x)
-- --   ... | lt x₁ | eq x = ⊥.rec (¬-suc-n<ᵗn x₁)
-- --   ... | eq x₁ | eq x = ⊥.rec (falseDichotomies.eq-eq (x₁ , refl))
-- --   ... | gt x₁ | eq x = refl
-- --   ... | p | gt x = ⊥.rec (¬m<ᵗm x)

-- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'≡transport :
-- --     HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'
-- --     ≡ subst (λ p → Fin p → ℤ) SphereBouquet/Card2≡
-- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'≡transport with dich1 n | dich2 (suc n)
-- --   ... | lt x | q = ⊥.rec (¬m<ᵗm x)
-- --   ... | eq x | lt x₁ = funExt λ _ → sym (transportRefl _)
-- --   ... | eq x | eq x₁ = funExt λ _ → sym (transportRefl _)
-- --   ... | eq x | gt x₁ = funExt λ _ → sym (transportRefl _)
-- --   ... | gt x | q = ⊥.rec (¬m<ᵗm x)

-- --   α↑ = subst2 (λ p q → SphereBouquet (suc n) (Fin p)
-- --                                      → SphereBouquet (suc n) (Fin q))
-- --                               (sym SphereBouquet/Card1≡)
-- --                               (sym SphereBouquet/Card2≡) α


-- --   -- l2 : bouquetSusp→ α↑ ≡ preboundary.pre∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n)
-- --   -- l2 with dich1 n | dich2 n
-- --   -- ... | s | t = ?

-- --   T0 : SphereBouquet/Fam (suc (suc n)) ≡ SphereBouquet (suc n) (Fin c2)
-- --   T0 with (dich2 (suc n))
-- --   ... | lt x = ⊥.rec (¬m<ᵗm x)
-- --   ... | eq x = refl
-- --   ... | gt x = ⊥.rec (¬m<ᵗm x)

-- --   T0' : SphereBouquet/Fam (suc (suc (suc n))) ≡ cofib α
-- --   T0' with (dich2 (suc (suc n)))
-- --   ... | lt x = ⊥.rec (¬-suc-n<ᵗn x)
-- --   ... | eq x = ⊥.rec (falseDichotomies.eq-eq (refl , sym x))
-- --   ... | gt x = refl

-- --   T1 : PathP (λ i → Fin (SphereBouquet/Card1≡ i) × S₊ (suc n) → T0 i) (SphereBouquet/α (suc (suc n))) (α ∘ inr)
-- --   T1 with dich1 (suc n)  | dich2 (suc n)
-- --   ... | q | lt x = ⊥.rec (¬m<ᵗm x)
-- --   ... | lt x₁ | eq x = ⊥.rec (¬-suc-n<ᵗn x₁)
-- --   ... | eq x₁ | eq x = ⊥.rec (falseDichotomies.eq-eq (refl , sym x₁))
-- --   ... | gt x₁ | eq x = λ i s → α (inr (fst s , ((λ i → subst S₊ (isSetℕ _ _ x refl i) (snd s)) ∙ transportRefl (snd s)) i))
-- --   ... | q | gt x = ⊥.rec (¬m<ᵗm x)

-- --   T2 : PathP (λ i → T0' i ≃ Pushout (T1 i) fst) (SphereBouquet/Eq (suc (suc n))) {!preboundary.isoCofBouquet!}
-- --   {- (compEquiv (compEquiv (symPushout _ _)
-- --         (pushoutEquiv _ _ _ _
-- --           (idEquiv _) (idEquiv _) (invEquiv (isContr→≃Unit (isContrLem (suc n) {!refl!})))
-- --           (λ _ x → α x)
-- --           λ i x → isContrLem {!!} (sym {!!}) .snd (inl x) i))
-- --         (invEquiv (isoToEquiv (Iso-PushoutComp-IteratedPushout
-- --           (λ x → inr x) α))))
-- --           -}
-- --   T2 = {!SphereBouquet/Eq (suc (suc n))!}

-- --   QQ : (i : I) → _
-- --   QQ i = BouquetFuns.BTC (suc (suc n))
-- --                         (SphereBouquet/Card1≡ i)
-- --                         (T1 i)
-- --                         {!!} -- (SphereBouquet/Eq (suc (suc n)))

-- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh* :
-- --     (a b : Fin (SphereBouquet/Card (suc n)) → ℤ)
-- --     → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst a ≡ (λ _ → 0)
-- --     → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst b ≡ (λ _ → 0)
-- --     → (r : Σ[ t ∈ (Fin (SphereBouquet/Card (suc (suc n))) → ℤ) ]
-- --              ∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n) .fst t ≡ λ q → a q - b q)
-- --     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun a
-- --      ≡ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun b
-- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh* a b aker bker (t , q) =
-- --     eq/ _ _ ∣ (subst (λ p → Fin p → ℤ) SphereBouquet/Card1≡ t)
-- --            , (λ i → transp (λ j → Fin (SphereBouquet/Card2≡ (j ∨ ~ i)) → ℤ) (~ i)
-- --                       (bouquetDegree
-- --                         (transp (λ j → SphereBouquet (suc n) (Fin (SphereBouquet/Card1≡ (~ j ∨ ~ i)))
-- --                                      → SphereBouquet (suc n) (Fin (SphereBouquet/Card2≡ (~ j ∨ ~ i))))
-- --                          (~ i) α) .fst
-- --                         (transp (λ j → Fin (SphereBouquet/Card1≡ (j ∧ ~ i)) → ℤ) i t)))
-- --            ∙ cong (subst (λ p → Fin p → ℤ) SphereBouquet/Card2≡)
-- --                   (funExt⁻ (cong fst lem) t)
-- --            ∙ sym (funExt⁻ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'≡transport
-- --                  (∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n) .fst t))
-- --            ∙ haha ∣₁
-- --     where
-- --     -- α* : _
-- --     -- α* = {!!}


    
-- --     -- _ : α* ≡ α↑
-- --     -- _ = {!!}

-- --     -- l1 : α↑ ≡ BouquetFuns.CTB (suc n)
-- --     --    (SphereBouquet/Card (suc n))
-- --     --    (SphereBouquet/α (suc n))
-- --     --    (SphereBouquet/Eq (suc n))
-- --     --    ∘ inr ∘ {!!}
-- --     -- l1 = {!!}


-- --     {- (λ _ → SuspBouquet→Bouquet (Fin (SphereBouquet/Card (suc n))) (λ _ → S₊∙ (suc n))
-- --        ∘ suspFun α↑
-- --        ∘ Bouquet→SuspBouquet (Fin (SphereBouquet/Card (suc (suc n)))) (λ _ → S₊∙ (suc n)))
-- --        ∙ funExt (λ x → cong (SuspBouquet→Bouquet (Fin (SphereBouquet/Card (suc n))) (λ _ → S₊∙ (suc n)))
-- --                              ({!BouquetFuns.BTC (suc (suc n))
-- --                         (SphereBouquet/Card (suc (suc n)))
-- --                         (SphereBouquet/α (suc (suc n)))
-- --                         (SphereBouquet/Eq (suc (suc n))) (inr ?)!}
-- --                            ∙ funExt⁻ (suspFunComp _ inr) (δ-pre (invEq (SphereBouquet/Eq (suc (suc n))) ∘ inl)
-- --                        (BouquetFuns.BTC (suc (suc n))
-- --                         (SphereBouquet/Card (suc (suc n)))
-- --                         (SphereBouquet/α (suc (suc n)))
-- --                         (SphereBouquet/Eq (suc (suc n))) x))))
-- --        ∙ λ i x → SuspBouquet→Bouquet (Fin (SphereBouquet/Card (suc n))) (λ _ → S₊∙ (suc n))
-- --                    (suspFun (BouquetFuns.CTB (suc n)
-- --                                              (SphereBouquet/Card (suc n))
-- --                                              (SphereBouquet/α (suc n))
-- --                                              (SphereBouquet/Eq (suc n)))
-- --                      (suspFun inr
-- --                       (δ-pre (invEq (SphereBouquet/Eq (suc (suc n))) ∘ inl)
-- --                        (BouquetFuns.BTC (suc (suc n))
-- --                         (SphereBouquet/Card (suc (suc n)))
-- --                         (SphereBouquet/α (suc (suc n)))
-- --                         (SphereBouquet/Eq (suc (suc n))) x))))
-- --                         -}
-- --     {-
-- --     isoSuspBouquet ∘ (suspFun isoCofBouquet)
-- --            ∘ (suspFun (to_cofibCW n C)) ∘ (δ (suc n) C) ∘ isoCofBouquetInv↑
-- --     -}
-- --     -- funExt λ t → cong sphereBouquetSuspFun {!!}
-- --       -- where
-- --       -- P : cofibCW (suc n) (SphereBouquet/ˢᵏᵉˡ n) ≡ SphereBouquet (suc n) (Fin c1)
-- --       -- P with (n ≟ᵗ n)
-- --       -- ... | q = {!!}
-- --       -- l1 : PathP (λ i → P i → {!!}) (preboundary.isoCofBouquet (SphereBouquet/ˢᵏᵉˡ n) (suc n)) α
-- --       -- l1 = {!!}
-- -- {-
-- -- sphereBouquetSuspFun ∘ (suspFun f) ∘ sphereBouquetSuspInvFun
-- -- -}

-- --     lem : bouquetDegree (subst2 (λ p q → SphereBouquet (suc n) (Fin p)
-- --                                        → SphereBouquet (suc n) (Fin q))
-- --                                 (sym SphereBouquet/Card1≡)
-- --                                 (sym SphereBouquet/Card2≡) α)
-- --         ≡ ∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n)
-- --     lem = bouquetDegreeSusp _ ∙ cong bouquetDegree {!!} -- l2

-- --     haha = cong HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' q
-- --          ∙ funExt (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ a (-_ ∘ b))
-- --          ∙ funExt (λ x → cong₂ _+_ refl (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- b x))

-- --     main : {!bouquetDegree α .fst
-- --       (subst (λ p → Fin p → ℤ) SphereBouquet/Card1≡ t)!}
-- --     main = {!!}

-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh :
-- -- --     (a b : Fin (SphereBouquet/Card (suc n)) → ℤ)
-- -- --     → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst a ≡ (λ _ → 0)
-- -- --     → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst b ≡ (λ _ → 0)
-- -- --     → (r : Σ[ t ∈ (Fin (SphereBouquet/Card (suc (suc n))) → ℤ) ]
-- -- --              ∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n) .fst t ≡ λ q → a q - b q)
-- -- --     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun a
-- -- --      ≡ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun b
-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh a b ak bk with (suc n ≟ᵗ n)
-- -- --   ... | lt x = ⊥.rec {!!}
-- -- --   ... | eq x = ⊥.rec {!!}
-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh a b ak bk | gt x with (Trichotomyᵗ-suc (n ≟ᵗ n))
-- -- --   ... | lt x₁ = ⊥.rec {!!}
-- -- --   ... | eq x₁ = help*
-- -- --     where
-- -- --     help* : _
-- -- --     help* = {!!}
-- -- --   ... | gt x₁ = ⊥.rec {!!}
-- -- --   {- | gt x with (n ≟ᵗ n)
-- -- --   ... | t = ?
-- -- --     where
-- -- --     H : {!SphereBouquet/Card (suc n)!}
-- -- --     H = {!!}
-- -- -- -}

-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap :
-- -- --     Hˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ n) n .fst → ℤ[]/ImSphereMap .fst
-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap =
-- -- --     SQ.rec squash/
-- -- --       (λ a → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun (a .fst))
-- -- --        λ {(a , ak) (b , bk) → PT.elim (λ _ → squash/ _ _)
-- -- --        λ r → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh a b ak bk
-- -- --                (fst r , cong fst (snd r))}

-- -- -- module _ {c1 c2 : ℕ} {n : ℕ} (α : SphereBouquetMap c1 c2 (suc n)) where
-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' : (m : ℕ) → (Fin (SphereBouquet/Card α m) → ℤ) → ℤ[Fin c2 ] .fst
-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' zero = λ _ _ → 0
-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (suc m) with m ≟ᵗ suc n | m ≟ᵗ suc (suc n)
-- -- --   ... | lt x | t = λ _ _ → 0
-- -- --   ... | eq x | lt x₁ = λ f → f
-- -- --   ... | eq x | eq x₁ = λ f → f
-- -- --   ... | eq x | gt x₁ = λ f → f
-- -- --   ... | gt x | t = λ _ _ → 0

-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- : (m : ℕ) (f : _) (a : _)
-- -- --     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' m (-_ ∘ f) a
-- -- --      ≡ - HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' m f a
-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- zero f a = refl
-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- (suc m) f a with m ≟ᵗ suc n | m ≟ᵗ suc (suc n)
-- -- --   ... | lt x | q = refl
-- -- --   ... | eq x | lt x₁ = refl
-- -- --   ... | eq x | eq x₁ = refl
-- -- --   ... | eq x | gt x₁ = refl
-- -- --   ... | gt x | q = refl

-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ : (m : ℕ) (f g : _) (a : _)
-- -- --     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' m (λ x → f x + g x) a
-- -- --     ≡ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' m f a + HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' m g a
-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ zero f g a = refl
-- -- --   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ (suc m) f g a with m ≟ᵗ suc n | m ≟ᵗ suc (suc n)
-- -- --   ... | lt x | q = refl
-- -- --   ... | eq x | lt x₁ = refl
-- -- --   ... | eq x | eq x₁ = refl
-- -- --   ... | eq x | gt x₁ = refl
-- -- --   ... | gt x | q = refl

-- -- -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh'' : {c1 c2 : ℕ} {n : ℕ} (α : SphereBouquetMap c1 c2 (suc n))
-- -- --   (m : ℕ)
-- -- --   (a b : Fin c2 → ℤ)
-- -- --   (p : SphereBouquet/Card α (suc m) ≡ c2)
-- -- --   (p2 : SphereBouquet/Card α (suc (suc m)) ≡ c1)
-- -- --   → ∂ (SphereBouquet/ˢᵏᵉˡ α n) m .fst (subst (λ p → Fin p → ℤ) (sym p) a) ≡ (λ _ → 0)
-- -- --   → ∂ (SphereBouquet/ˢᵏᵉˡ α n) m .fst (subst (λ p → Fin p → ℤ) (sym p) b) ≡ (λ _ → 0)
-- -- --    → (r : Σ[ t ∈ (Fin c1 → ℤ) ]
-- -- --          ((q : Fin c2) → ∂ (SphereBouquet/ˢᵏᵉˡ α n) (suc m) .fst (subst (λ p → Fin p → ℤ) (sym p2) t) (subst Fin (sym p) q) ≡ a q - b q))
-- -- --   → Σ[ k ∈ _ ] (bouquetDegree α .fst k
-- -- --     ≡ λ x → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (suc m) (subst (λ p → Fin p → ℤ) (sym p) a) x
-- -- --            - HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (suc m) (subst (λ p → Fin p → ℤ) (sym p) b) x)
-- -- -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh'' {n = n} α m a b p p2 aa aaa r = {!!}


-- -- -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh' : {c1 c2 : ℕ} {n : ℕ} (α : SphereBouquetMap c1 c2 (suc n))
-- -- --   (a b : Fin (SphereBouquet/Card α (2 +ℕ n)) → ℤ)
-- -- --   → ∂ (SphereBouquet/ˢᵏᵉˡ α n) (suc n) .fst a ≡ (λ _ → 0)
-- -- --   → ∂ (SphereBouquet/ˢᵏᵉˡ α n) (suc n) .fst b ≡ (λ _ → 0)
-- -- --    → (r : Σ[ t ∈ (Fin (SphereBouquet/Card α (3 +ℕ n)) → ℤ) ]
-- -- --          ∂ (SphereBouquet/ˢᵏᵉˡ α n) ((2 +ℕ n)) .fst t ≡ λ q → a q - b q)
-- -- --   → Σ[ k ∈ _ ] (bouquetDegree α .fst k
-- -- --     ≡ λ x → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (2 +ℕ n) a x
-- -- --            - HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (2 +ℕ n) b x)
-- -- -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh' {n = n} α a b ak bk (r , q) = {!r!} , ({!!} ∙ haha)
-- -- --   where
-- -- --   haha : HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (2 +ℕ n) (∂ (SphereBouquet/ˢᵏᵉˡ α n) (2 +ℕ n) .fst r)
-- -- --       ≡ _
-- -- --   haha = cong (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (2 +ℕ n)) q
-- -- --        ∙ funExt (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ α (2 +ℕ n) a (-_ ∘ b))
-- -- --        ∙ funExt (λ x → cong₂ _+_ refl (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- α (2 +ℕ n) b x))

-- -- -- -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh' {n = suc n} α m a b ak bk with (m ≟ᵗ suc n) | (Trichotomyᵗ-suc (m ≟ᵗ suc (suc n)))
-- -- -- -- ... | lt x | q = {!!}
-- -- -- -- ... | eq x | lt x₁ = {!!}
-- -- -- -- ... | eq x | eq x₁ = {!a!}
-- -- -- -- ... | eq x | gt x₁ = {!!}
-- -- -- -- ... | gt x | q = {!!}
-- -- -- -- {- with (Trichotomyᵗ-suc (m ≟ᵗ n)) | (Trichotomyᵗ-suc (m ≟ᵗ suc n))
-- -- -- -- ... | lt x | qq = {!!}
-- -- -- -- ... | eq x | lt x₁ = {!!}
-- -- -- -- ... | eq x | eq x₁ = {!!}
-- -- -- -- ... | eq x | gt x₁ = {!!}
-- -- -- -- ... | gt x | qq = {!!}
-- -- -- -- -}

-- -- -- --   {-
-- -- -- --     SQ.rec squash/ (λ a → [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (suc m) (fst a) ])
-- -- -- --                    λ {(a , ak) (b , bk) → PT.elim {!!}
-- -- -- --                    (λ r → eq/ _ _ ∣ {!!} , {!!} ∣₁)}
-- -- -- -- -}
 

-- -- -- -- -- with n ≟ᵗ n | n ≟ᵗ suc n
-- -- -- -- --   ... | lt x | b = [ (λ _ → 0) ]
-- -- -- -- --   ... | eq x | lt x₁ = [ f ]
-- -- -- -- --   ... | eq x | eq x₁ = [ (λ _ → 0) ]
-- -- -- -- --   ... | eq x | gt x₁ = [ (λ _ → 0) ]
-- -- -- -- --   ... | gt x | b = [ (λ _ → 0) ]


-- -- -- --   -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh :
-- -- -- --   --   (a b : Fin (SphereBouquet/Card (suc n)) → ℤ)
-- -- -- --   --   → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst a ≡ (λ _ → 0)
-- -- -- --   --   → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst b ≡ (λ _ → 0)
-- -- -- --   --   → (r : Σ[ t ∈ (Fin (SphereBouquet/Card (suc (suc n))) → ℤ) ]
-- -- -- --   --            ∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n) .fst t ≡ λ q → a q - b q)
-- -- -- --   --   → ? -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun a
-- -- -- --   --    ≡ ? -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun b
-- -- -- --   -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh a b ak bk = {!!}
