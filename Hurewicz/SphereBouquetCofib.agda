{-# OPTIONS --cubical --lossy-unification #-}
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

module _ {c1 c2 : ℕ} {n : ℕ} (α : SphereBouquetMap c1 c2 n) where
  SphereBouquet/Fam : ℕ → Type
  SphereBouquet/Fam zero = ⊥
  SphereBouquet/Fam (suc m) with (m ≟ᵗ suc n)
  ... | lt x = Unit
  ... | eq x = SphereBouquet (suc n) (Fin c2)
  ... | gt x = cofib α

  SphereBouquet/Fam∙ : (n : ℕ) → SphereBouquet/Fam (suc n)
  SphereBouquet/Fam∙ m with (m ≟ᵗ suc n)
  ... | lt x = tt
  ... | eq x = inl tt
  ... | gt x = inl tt

  SphereBouquet/Card-gt : ℕ → ℕ
  SphereBouquet/Card-gt m with (m ≟ᵗ n)
  ... | lt x = 0
  ... | eq x = c1
  ... | gt x = 0

  SphereBouquet/Card : ℕ → ℕ
  SphereBouquet/Card zero = 1
  SphereBouquet/Card (suc m) with (m ≟ᵗ n) | (m ≟ᵗ suc n)
  ... | lt x | s = 0
  ... | eq x | s = c2
  ... | gt x | lt x₁ = 0
  ... | gt x | eq x₁ = c1
  ... | gt x | gt x₁ = 0

  SphereBouquet/α : (m : ℕ) → Fin (SphereBouquet/Card m) × S⁻ m → SphereBouquet/Fam m
  SphereBouquet/α  (suc m) with m ≟ᵗ n | m ≟ᵗ suc n
  ... | lt x | t = λ()
  ... | eq x | lt x₁ = λ _ → tt -- 
  ... | eq x | eq x₁ = λ _ → inl tt
  ... | eq x | gt x₁ =  λ _ → inl tt
  ... | gt x | lt x₁ = λ()
  ... | gt x | eq x₁ = λ x → α (inr (fst x , subst S₊ x₁ (snd x)))
  ... | gt x | gt x₁ = λ()

  SphereBouquet/EqContr : (m : ℕ) → m <ᵗ suc n → isContr (Pushout (SphereBouquet/α m) (λ r → fst r))
  SphereBouquet/EqContr zero p = (inr fzero) , λ { (inr (zero , tt)) → refl}
  SphereBouquet/EqContr (suc m) p with m ≟ᵗ n | m ≟ᵗ suc n
  ... | lt x | lt x₁ = (inl tt) , λ { (inl x) → refl}
  ... | lt x | eq x₁ = ⊥.rec (falseDichotomies.lt-eq (x , x₁))
  ... | lt x | gt x₁ = ⊥.rec (falseDichotomies.lt-gt (x , x₁))
  ... | eq x | q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x p))
  ... | gt x | q = ⊥.rec (¬m<ᵗm (<ᵗ-trans p x))

  SphereBouquet/EqBottomMain : SphereBouquet (suc n) (Fin c2)
                             ≃ cofib {A = Fin c2 × S₊ n} {B = Fin c2} fst
  SphereBouquet/EqBottomMain =
    isoToEquiv 
      (compIso (pushoutIso _ _ _ _ (idEquiv _) (idEquiv Unit)
                  (Σ-cong-equiv-snd (λ a → isoToEquiv (IsoSucSphereSusp n)))
                  refl
                  (funExt (λ a → ΣPathP (refl , IsoSucSphereSusp∙' n))))
               (invIso (Iso-cofibFst-⋁ λ _ → S₊∙ n)))

  SphereBouquet/EqBottom : SphereBouquet (suc n) (Fin c2) ≃ Pushout (SphereBouquet/α (suc n)) fst
  SphereBouquet/EqBottom with n ≟ᵗ n | n ≟ᵗ suc n
  ... | lt x | q = ⊥.rec (¬m<ᵗm x)
  ... | eq x | lt x₁ = SphereBouquet/EqBottomMain
  ... | eq x | eq x₁ = ⊥.rec (falseDichotomies.eq-eq (x , x₁))
  ... | eq x | gt x₁ = ⊥.rec (falseDichotomies.eq-gt (x , x₁))
  ... | gt x | q = ⊥.rec (¬m<ᵗm x)

  isContrLem : (m : ℕ) (x : suc n ≡ m)
    → isContr (Pushout  {A = Fin c1 × S₊ m} {B = SphereBouquet (suc n) (Fin c1)}
                         (λ x₂ → inr (fst x₂ , subst S₊ (sym x) (snd x₂))) fst)
  isContrLem =
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
  
  SphereBouquet/EqTop : (m : ℕ) → suc n <ᵗ m → cofib α ≃ Pushout (SphereBouquet/α m) fst 
  SphereBouquet/EqTop (suc m) p with (m ≟ᵗ n) | (m ≟ᵗ suc n)
  ... | lt x | a = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))
  ... | eq x | a = ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) (sym x) p))
  ... | gt x | lt x₁ = ⊥.rec (¬squeeze (x₁ , x))
  ... | gt x | eq x₁ =
      compEquiv (compEquiv (symPushout _ _)
        (pushoutEquiv _ _ _ _
          (idEquiv _) (idEquiv _) (invEquiv (isContr→≃Unit (isContrLem m (sym x₁))))
          (λ _ x → α x)
          λ i x → isContrLem m (sym x₁) .snd (inl x) i))
        (invEquiv (isoToEquiv (Iso-PushoutComp-IteratedPushout
          (λ x → inr (fst x , subst S₊ x₁ (snd x))) α)))
  ... | gt x | gt x₁ = isoToEquiv (PushoutEmptyFam (λ()) λ())

  SphereBouquet/Eq : (m : ℕ) → (SphereBouquet/Fam (suc m))
                               ≃ Pushout (SphereBouquet/α m) fst
  SphereBouquet/Eq m with (m ≟ᵗ suc n)
  ... | lt x = invEquiv (isContr→≃Unit (SphereBouquet/EqContr m x))
  ... | eq x = subst (λ m → SphereBouquet (suc n) (Fin c2)
                           ≃ Pushout (SphereBouquet/α m) fst)
                     (sym x)
                     SphereBouquet/EqBottom
  ... | gt x = SphereBouquet/EqTop m x


  SphereBouquet/ˢᵏᵉˡ : (m : ℕ) → CWskel ℓ-zero
  fst (SphereBouquet/ˢᵏᵉˡ m) = SphereBouquet/Fam
  fst (snd (SphereBouquet/ˢᵏᵉˡ m)) = SphereBouquet/Card
  fst (snd (snd (SphereBouquet/ˢᵏᵉˡ m))) = SphereBouquet/α
  fst (snd (snd (snd (SphereBouquet/ˢᵏᵉˡ m)))) x = x
  snd (snd (snd (snd (SphereBouquet/ˢᵏᵉˡ m)))) = SphereBouquet/Eq




  SphereBouquet/ˢᵏᵉˡConverges : (k : ℕ)
    → isEquiv {B = Pushout (SphereBouquet/α (k +ℕ suc (suc (suc n)))) fst} inl
  SphereBouquet/ˢᵏᵉˡConverges k =
    isoToIsEquiv (PushoutEmptyFam (l (k +ℕ (3 +ℕ n)) (<→<ᵗ (k , refl)) ∘ fst)
                                  (l (k +ℕ (3 +ℕ n)) (<→<ᵗ (k , refl))))
    where
    l : (m : ℕ) → suc (suc n) <ᵗ m → ¬ Fin (SphereBouquet/Card m)
    l (suc m) p with (m ≟ᵗ n) | (m ≟ᵗ suc n)
    ... | lt x | b = snd
    ... | eq x | b = λ _ → falseDichotomies.eq-gt (x , p)
    ... | gt x | lt x₁ = snd
    ... | gt x | eq x₁ = λ _ → ¬m<ᵗm (subst (suc n <ᵗ_) x₁ p)
    ... | gt x | gt x₁ = snd

  SphereBouquet/FamTopElement : cofib α ≃ SphereBouquet/Fam (3 +ℕ n)
  SphereBouquet/FamTopElement with (Trichotomyᵗ-suc (suc n ≟ᵗ n)) -- suc n ≟ᵗ n)
  ... | lt x = ⊥.rec (¬-suc-n<ᵗn x)
  ... | eq x = ⊥.rec (falseDichotomies.eq-eq (x , refl))
  ... | gt x = idEquiv _


  isCWSphereBouquet/ : (n : ℕ) → isCW (cofib α)
  fst (isCWSphereBouquet/ n) = SphereBouquet/ˢᵏᵉˡ n
  snd (isCWSphereBouquet/ m) =
    compEquiv SphereBouquet/FamTopElement
      (isoToEquiv (converges→ColimIso (suc (suc (suc n)))
      λ k → compEquiv (inl , SphereBouquet/ˢᵏᵉˡConverges k)
        (invEquiv (SphereBouquet/Eq _)) .snd))

  SphereBouquet/ᶜʷ : CW ℓ-zero
  fst SphereBouquet/ᶜʷ = cofib α
  snd SphereBouquet/ᶜʷ = ∣ isCWSphereBouquet/ n ∣₁

  open import Cubical.Algebra.Group.Subgroup
  ℤ[]/ImSphereMap : Group₀
  ℤ[]/ImSphereMap = (AbGroup→Group ℤ[Fin c2 ])
                  / (imSubgroup (bouquetDegree α)
                  , isNormalIm (bouquetDegree α)
                    λ _ _ → AbGroupStr.+Comm (snd ℤ[Fin c2 ]) _ _)

  ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/ : ℤ[]/ImSphereMap .fst → Hˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ n) n .fst
  ℤ[]/ImSphereMap→HₙSphereBouquetⁿ/ = SQ.elim {!!}
    (λ f → {!!})
    {!!}

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' : (Fin (SphereBouquet/Card (suc n)) → ℤ) → ℤ[Fin c2 ] .fst
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' with n ≟ᵗ n | n ≟ᵗ suc n
  ... | lt x | t = λ _ _ → 0
  ... | eq x | lt x₁ = λ f → f
  ... | eq x | eq x₁ = λ f → f
  ... | eq x | gt x₁ = λ f → f
  ... | gt x | t = λ _ _ → 0

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- : (f : _) (a : _)
    → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (-_ ∘ f) a
     ≡ - HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' f a
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres-  f a with n ≟ᵗ n | n ≟ᵗ suc n
  ... | lt x | q = refl
  ... | eq x | lt x₁ = refl
  ... | eq x | eq x₁ = refl
  ... | eq x | gt x₁ = refl
  ... | gt x | q = refl

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ : (f g : _) (a : _)
    → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (λ x → f x + g x) a
    ≡ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' f a + HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' g a
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ f g a with n ≟ᵗ n | n ≟ᵗ suc n
  ... | lt x | q = refl
  ... | eq x | lt x₁ = refl
  ... | eq x | eq x₁ = refl
  ... | eq x | gt x₁ = refl
  ... | gt x | q = refl


  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun : (Fin (SphereBouquet/Card (suc n)) → ℤ) → ℤ[]/ImSphereMap .fst
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun = [_] ∘ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'

  SphereBouquet/Card2≡ : SphereBouquet/Card (suc n) ≡ c2
  SphereBouquet/Card2≡ with n ≟ᵗ n | n ≟ᵗ suc n
  ... | lt x | q = ⊥.rec (¬m<ᵗm x)
  ... | eq x | lt x₁ = refl
  ... | eq x | eq x₁ = refl
  ... | eq x | gt x₁ = refl
  ... | gt x | q = ⊥.rec (¬m<ᵗm x)

  SphereBouquet/Card1≡ : SphereBouquet/Card (suc (suc n)) ≡ c1
  SphereBouquet/Card1≡ with suc n ≟ᵗ n | n ≟ᵗ n
  ... | p | lt x = ⊥.rec (¬m<ᵗm x)
  ... | lt x₁ | eq x = ⊥.rec (¬-suc-n<ᵗn x₁)
  ... | eq x₁ | eq x = ⊥.rec (falseDichotomies.eq-eq (x , sym x₁))
  ... | gt x₁ | eq x = refl
  ... | p | gt x = ⊥.rec (¬m<ᵗm x)

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'≡transport :
    HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'
    ≡ subst (λ p → Fin p → ℤ) SphereBouquet/Card2≡
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'≡transport with n ≟ᵗ n | n ≟ᵗ suc n
  ... | lt x | q = ⊥.rec (¬m<ᵗm x)
  ... | eq x | lt x₁ = funExt λ _ → sym (transportRefl _)
  ... | eq x | eq x₁ = funExt λ _ → sym (transportRefl _)
  ... | eq x | gt x₁ = funExt λ _ → sym (transportRefl _)
  ... | gt x | q = ⊥.rec (¬m<ᵗm x)

  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh* :
    (a b : Fin (SphereBouquet/Card (suc n)) → ℤ)
    → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst a ≡ (λ _ → 0)
    → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst b ≡ (λ _ → 0)
    → (r : Σ[ t ∈ (Fin (SphereBouquet/Card (suc (suc n))) → ℤ) ]
             ∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n) .fst t ≡ λ q → a q - b q)
    → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun a
     ≡ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun b
  HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh* a b aker bker (t , q) =
    eq/ _ _ ∣ (subst (λ p → Fin p → ℤ) SphereBouquet/Card1≡ t)
           , (λ i → transp (λ j → Fin (SphereBouquet/Card2≡ (j ∨ ~ i)) → ℤ) (~ i)
                      (bouquetDegree
                        (transp (λ j → SphereBouquet (suc n) (Fin (SphereBouquet/Card1≡ (~ j ∨ ~ i)))
                                     → SphereBouquet (suc n) (Fin (SphereBouquet/Card2≡ (~ j ∨ ~ i))))
                         (~ i) α) .fst
                        (transp (λ j → Fin (SphereBouquet/Card1≡ (j ∧ ~ i)) → ℤ) i t)))
           ∙ cong (subst (λ p → Fin p → ℤ) SphereBouquet/Card2≡)
                  (funExt⁻ (cong fst lem) t)
           ∙ sym (funExt⁻ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'≡transport
                 (∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n) .fst t))
           ∙ haha ∣₁
    where
    α* : _
    α* = {!!}

    α↑ = subst2 (λ p q → SphereBouquet (suc n) (Fin p)
                                       → SphereBouquet (suc n) (Fin q))
                                (sym SphereBouquet/Card1≡)
                                (sym SphereBouquet/Card2≡) α

    
    _ : α* ≡ α↑
    _ = {!!}

    l1 : α↑ ≡ BouquetFuns.CTB (suc n)
       (SphereBouquet/Card (suc n))
       (SphereBouquet/α (suc n))
       (SphereBouquet/Eq (suc n))
       ∘ inr ∘ {!!}
    l1 = {!!}

    l2 : bouquetSusp→ α↑ ≡ preboundary.pre∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n)
    l2 = (λ _ → SuspBouquet→Bouquet (Fin (SphereBouquet/Card (suc n))) (λ _ → S₊∙ (suc n))
       ∘ suspFun α↑
       ∘ Bouquet→SuspBouquet (Fin (SphereBouquet/Card (suc (suc n)))) (λ _ → S₊∙ (suc n)))
       ∙ funExt (λ x → cong (SuspBouquet→Bouquet (Fin (SphereBouquet/Card (suc n))) (λ _ → S₊∙ (suc n)))
                             ({!BouquetFuns.BTC (suc (suc n))
                        (SphereBouquet/Card (suc (suc n)))
                        (SphereBouquet/α (suc (suc n)))
                        (SphereBouquet/Eq (suc (suc n))) (inr ?)!}
                           ∙ funExt⁻ (suspFunComp _ inr) (δ-pre (invEq (SphereBouquet/Eq (suc (suc n))) ∘ inl)
                       (BouquetFuns.BTC (suc (suc n))
                        (SphereBouquet/Card (suc (suc n)))
                        (SphereBouquet/α (suc (suc n)))
                        (SphereBouquet/Eq (suc (suc n))) x))))
       ∙ λ i x → SuspBouquet→Bouquet (Fin (SphereBouquet/Card (suc n))) (λ _ → S₊∙ (suc n))
                   (suspFun (BouquetFuns.CTB (suc n)
                                             (SphereBouquet/Card (suc n))
                                             (SphereBouquet/α (suc n))
                                             (SphereBouquet/Eq (suc n)))
                     (suspFun inr
                      (δ-pre (invEq (SphereBouquet/Eq (suc (suc n))) ∘ inl)
                       (BouquetFuns.BTC (suc (suc n))
                        (SphereBouquet/Card (suc (suc n)))
                        (SphereBouquet/α (suc (suc n)))
                        (SphereBouquet/Eq (suc (suc n))) x))))
    {-
    isoSuspBouquet ∘ (suspFun isoCofBouquet)
           ∘ (suspFun (to_cofibCW n C)) ∘ (δ (suc n) C) ∘ isoCofBouquetInv↑
    -}
    -- funExt λ t → cong sphereBouquetSuspFun {!!}
      -- where
      -- P : cofibCW (suc n) (SphereBouquet/ˢᵏᵉˡ n) ≡ SphereBouquet (suc n) (Fin c1)
      -- P with (n ≟ᵗ n)
      -- ... | q = {!!}
      -- l1 : PathP (λ i → P i → {!!}) (preboundary.isoCofBouquet (SphereBouquet/ˢᵏᵉˡ n) (suc n)) α
      -- l1 = {!!}
{-
sphereBouquetSuspFun ∘ (suspFun f) ∘ sphereBouquetSuspInvFun
-}

    lem : bouquetDegree (subst2 (λ p q → SphereBouquet (suc n) (Fin p)
                                       → SphereBouquet (suc n) (Fin q))
                                (sym SphereBouquet/Card1≡)
                                (sym SphereBouquet/Card2≡) α)
        ≡ ∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n)
    lem = bouquetDegreeSusp _ ∙ cong bouquetDegree l2

    haha = cong HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' q
         ∙ funExt (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ a (-_ ∘ b))
         ∙ funExt (λ x → cong₂ _+_ refl (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- b x))

    main : {!bouquetDegree α .fst
      (subst (λ p → Fin p → ℤ) SphereBouquet/Card1≡ t)!}
    main = {!!}

--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh :
--     (a b : Fin (SphereBouquet/Card (suc n)) → ℤ)
--     → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst a ≡ (λ _ → 0)
--     → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst b ≡ (λ _ → 0)
--     → (r : Σ[ t ∈ (Fin (SphereBouquet/Card (suc (suc n))) → ℤ) ]
--              ∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n) .fst t ≡ λ q → a q - b q)
--     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun a
--      ≡ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun b
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh a b ak bk with (suc n ≟ᵗ n)
--   ... | lt x = ⊥.rec {!!}
--   ... | eq x = ⊥.rec {!!}
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh a b ak bk | gt x with (Trichotomyᵗ-suc (n ≟ᵗ n))
--   ... | lt x₁ = ⊥.rec {!!}
--   ... | eq x₁ = help*
--     where
--     help* : _
--     help* = {!!}
--   ... | gt x₁ = ⊥.rec {!!}
--   {- | gt x with (n ≟ᵗ n)
--   ... | t = ?
--     where
--     H : {!SphereBouquet/Card (suc n)!}
--     H = {!!}
-- -}

--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap :
--     Hˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ n) n .fst → ℤ[]/ImSphereMap .fst
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap =
--     SQ.rec squash/
--       (λ a → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun (a .fst))
--        λ {(a , ak) (b , bk) → PT.elim (λ _ → squash/ _ _)
--        λ r → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh a b ak bk
--                (fst r , cong fst (snd r))}

-- module _ {c1 c2 : ℕ} {n : ℕ} (α : SphereBouquetMap c1 c2 (suc n)) where
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' : (m : ℕ) → (Fin (SphereBouquet/Card α m) → ℤ) → ℤ[Fin c2 ] .fst
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' zero = λ _ _ → 0
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (suc m) with m ≟ᵗ suc n | m ≟ᵗ suc (suc n)
--   ... | lt x | t = λ _ _ → 0
--   ... | eq x | lt x₁ = λ f → f
--   ... | eq x | eq x₁ = λ f → f
--   ... | eq x | gt x₁ = λ f → f
--   ... | gt x | t = λ _ _ → 0

--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- : (m : ℕ) (f : _) (a : _)
--     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' m (-_ ∘ f) a
--      ≡ - HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' m f a
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- zero f a = refl
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- (suc m) f a with m ≟ᵗ suc n | m ≟ᵗ suc (suc n)
--   ... | lt x | q = refl
--   ... | eq x | lt x₁ = refl
--   ... | eq x | eq x₁ = refl
--   ... | eq x | gt x₁ = refl
--   ... | gt x | q = refl

--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ : (m : ℕ) (f g : _) (a : _)
--     → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' m (λ x → f x + g x) a
--     ≡ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' m f a + HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' m g a
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ zero f g a = refl
--   HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ (suc m) f g a with m ≟ᵗ suc n | m ≟ᵗ suc (suc n)
--   ... | lt x | q = refl
--   ... | eq x | lt x₁ = refl
--   ... | eq x | eq x₁ = refl
--   ... | eq x | gt x₁ = refl
--   ... | gt x | q = refl

-- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh'' : {c1 c2 : ℕ} {n : ℕ} (α : SphereBouquetMap c1 c2 (suc n))
--   (m : ℕ)
--   (a b : Fin c2 → ℤ)
--   (p : SphereBouquet/Card α (suc m) ≡ c2)
--   (p2 : SphereBouquet/Card α (suc (suc m)) ≡ c1)
--   → ∂ (SphereBouquet/ˢᵏᵉˡ α n) m .fst (subst (λ p → Fin p → ℤ) (sym p) a) ≡ (λ _ → 0)
--   → ∂ (SphereBouquet/ˢᵏᵉˡ α n) m .fst (subst (λ p → Fin p → ℤ) (sym p) b) ≡ (λ _ → 0)
--    → (r : Σ[ t ∈ (Fin c1 → ℤ) ]
--          ((q : Fin c2) → ∂ (SphereBouquet/ˢᵏᵉˡ α n) (suc m) .fst (subst (λ p → Fin p → ℤ) (sym p2) t) (subst Fin (sym p) q) ≡ a q - b q))
--   → Σ[ k ∈ _ ] (bouquetDegree α .fst k
--     ≡ λ x → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (suc m) (subst (λ p → Fin p → ℤ) (sym p) a) x
--            - HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (suc m) (subst (λ p → Fin p → ℤ) (sym p) b) x)
-- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh'' {n = n} α m a b p p2 aa aaa r = {!!}


-- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh' : {c1 c2 : ℕ} {n : ℕ} (α : SphereBouquetMap c1 c2 (suc n))
--   (a b : Fin (SphereBouquet/Card α (2 +ℕ n)) → ℤ)
--   → ∂ (SphereBouquet/ˢᵏᵉˡ α n) (suc n) .fst a ≡ (λ _ → 0)
--   → ∂ (SphereBouquet/ˢᵏᵉˡ α n) (suc n) .fst b ≡ (λ _ → 0)
--    → (r : Σ[ t ∈ (Fin (SphereBouquet/Card α (3 +ℕ n)) → ℤ) ]
--          ∂ (SphereBouquet/ˢᵏᵉˡ α n) ((2 +ℕ n)) .fst t ≡ λ q → a q - b q)
--   → Σ[ k ∈ _ ] (bouquetDegree α .fst k
--     ≡ λ x → HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (2 +ℕ n) a x
--            - HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (2 +ℕ n) b x)
-- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh' {n = n} α a b ak bk (r , q) = {!r!} , ({!!} ∙ haha)
--   where
--   haha : HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (2 +ℕ n) (∂ (SphereBouquet/ˢᵏᵉˡ α n) (2 +ℕ n) .fst r)
--       ≡ _
--   haha = cong (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' α (2 +ℕ n)) q
--        ∙ funExt (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres+ α (2 +ℕ n) a (-_ ∘ b))
--        ∙ funExt (λ x → cong₂ _+_ refl (HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun'pres- α (2 +ℕ n) b x))

-- -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh' {n = suc n} α m a b ak bk with (m ≟ᵗ suc n) | (Trichotomyᵗ-suc (m ≟ᵗ suc (suc n)))
-- -- ... | lt x | q = {!!}
-- -- ... | eq x | lt x₁ = {!!}
-- -- ... | eq x | eq x₁ = {!a!}
-- -- ... | eq x | gt x₁ = {!!}
-- -- ... | gt x | q = {!!}
-- -- {- with (Trichotomyᵗ-suc (m ≟ᵗ n)) | (Trichotomyᵗ-suc (m ≟ᵗ suc n))
-- -- ... | lt x | qq = {!!}
-- -- ... | eq x | lt x₁ = {!!}
-- -- ... | eq x | eq x₁ = {!!}
-- -- ... | eq x | gt x₁ = {!!}
-- -- ... | gt x | qq = {!!}
-- -- -}

-- --   {-
-- --     SQ.rec squash/ (λ a → [ HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun' (suc m) (fst a) ])
-- --                    λ {(a , ak) (b , bk) → PT.elim {!!}
-- --                    (λ r → eq/ _ _ ∣ {!!} , {!!} ∣₁)}
-- -- -}
 

-- -- -- with n ≟ᵗ n | n ≟ᵗ suc n
-- -- --   ... | lt x | b = [ (λ _ → 0) ]
-- -- --   ... | eq x | lt x₁ = [ f ]
-- -- --   ... | eq x | eq x₁ = [ (λ _ → 0) ]
-- -- --   ... | eq x | gt x₁ = [ (λ _ → 0) ]
-- -- --   ... | gt x | b = [ (λ _ → 0) ]


-- --   -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh :
-- --   --   (a b : Fin (SphereBouquet/Card (suc n)) → ℤ)
-- --   --   → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst a ≡ (λ _ → 0)
-- --   --   → ∂ (SphereBouquet/ˢᵏᵉˡ n) n .fst b ≡ (λ _ → 0)
-- --   --   → (r : Σ[ t ∈ (Fin (SphereBouquet/Card (suc (suc n))) → ℤ) ]
-- --   --            ∂ (SphereBouquet/ˢᵏᵉˡ n) (suc n) .fst t ≡ λ q → a q - b q)
-- --   --   → ? -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun a
-- --   --    ≡ ? -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-fun b
-- --   -- HₙSphereBouquetⁿ/→ℤ[]/ImSphereMap-coh a b ak bk = {!!}
