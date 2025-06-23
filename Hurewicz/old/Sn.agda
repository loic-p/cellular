{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.Sn where

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


module Sgen (n : ℕ) where
  Sfam : (m : ℕ) → Trichotomyᵗ m (suc n) → Type
  Sfam zero p = ⊥
  Sfam (suc m) (lt x) = Unit
  Sfam (suc m) (eq x) = S₊ n
  Sfam (suc m) (gt x) = S₊ n
  
  Sfam∙ : (m : ℕ) (s : Trichotomyᵗ (suc m) (suc n)) → Sfam (suc m) s
  Sfam∙ m (lt x) = tt
  Sfam∙ m (eq x) = ptSn n
  Sfam∙ m (gt x) = ptSn n

ScardGen : (n m : ℕ) (s : Trichotomyᵗ (suc m) (suc n)) → ℕ
ScardGen zero zero s = 2
ScardGen zero (suc m) s = 0
ScardGen (suc n) zero s = 1
ScardGen (suc n) (suc m) (lt x) = 0
ScardGen (suc n) (suc m) (eq x) = 1
ScardGen (suc n) (suc m) (gt x) = 0

SαGen : (n m : ℕ) (s : Trichotomyᵗ (suc m) (suc n)) (q : Trichotomyᵗ m (suc n))
  → Fin (ScardGen n m s) × S⁻ m → Sgen.Sfam n m q
SαGen n (suc m) s q _ = Sgen.Sfam∙ n m q

Sfam : (n : ℕ) → ℕ → Type
Sfam n m = Sgen.Sfam n m (m ≟ᵗ suc n)

Sfam∙ : (n m : ℕ) → Sfam n (suc m)
Sfam∙ n m = Sgen.Sfam∙ n m (suc m ≟ᵗ suc n)

Scard : (n : ℕ) → ℕ → ℕ
Scard n m = ScardGen n m (suc m ≟ᵗ suc n)

Sα : (n m : ℕ) → Fin (Scard n m) × S⁻ m → Sfam n m
Sα n m t = SαGen n m (suc m ≟ᵗ suc n) (m ≟ᵗ suc n) t

¬ScardGen : (n m : ℕ) (p : _) → n <ᵗ m → ¬ Fin (ScardGen n m p) 
¬ScardGen zero (suc m) p q = ¬Fin0
¬ScardGen (suc n) (suc m) (lt x) q = snd
¬ScardGen (suc n) (suc m) (eq x) q =
  λ _ → ¬m<ᵗm (subst (n <ᵗ_) (cong (predℕ ∘ predℕ) x) q)
¬ScardGen (suc n) (suc m) (gt x) q = snd

¬Scard : (n m : ℕ) → n <ᵗ m → ¬ Fin (Scard n m)
¬Scard n m = ¬ScardGen n m (suc m ≟ᵗ suc n)

¬Scard' : (n : ℕ) → ¬ Fin (Scard (suc (suc n)) (suc n))
¬Scard' n x with (n ≟ᵗ suc n)
... | eq x₁ = ¬m<ᵗm (subst (n <ᵗ_) (sym x₁) <ᵗsucm) 

module _  {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (b : B) (g : A → C) where
  PushoutConst→⋁ : (Pushout (λ _ → b) g) → ((B , b) ⋁ (cofib g , inl tt))
  PushoutConst→⋁ (inl x) = inl x
  PushoutConst→⋁ (inr x) = inr (inr x)
  PushoutConst→⋁ (push a i) = (push tt ∙ λ i → inr (push a i)) i

  ⋁→PushoutConst : (B , b) ⋁ (cofib g , inl tt) → Pushout (λ _ → b) g
  ⋁→PushoutConst (inl x) = inl x
  ⋁→PushoutConst (inr (inl x)) = inl b
  ⋁→PushoutConst (inr (inr x)) = inr x
  ⋁→PushoutConst (inr (push a i)) = push a i
  ⋁→PushoutConst (push a i) = inl b

  PushoutConst→⋁→PushoutConst : (x : Pushout (λ _ → b) g)
    → ⋁→PushoutConst (PushoutConst→⋁ x) ≡ x
  PushoutConst→⋁→PushoutConst (inl x) = refl
  PushoutConst→⋁→PushoutConst (inr x) = refl
  PushoutConst→⋁→PushoutConst (push a i) j =
    ⋁→PushoutConst (compPath-filler' (push tt) (λ i → inr (push a i)) (~ j) i)

  ⋁→PushoutConst→⋁ : (x : (B , b) ⋁ (cofib g , inl tt))
    → PushoutConst→⋁ (⋁→PushoutConst x) ≡ x
  ⋁→PushoutConst→⋁ (inl x) = refl
  ⋁→PushoutConst→⋁ (inr (inl x)) = push x
  ⋁→PushoutConst→⋁ (inr (inr x)) = refl
  ⋁→PushoutConst→⋁ (inr (push a i)) j = compPath-filler' (push tt) (λ i₁ → inr (push a i₁)) (~ j) i
  ⋁→PushoutConst→⋁ (push a i) j = push tt (i ∧ j)

  Iso-PushoutConst→⋁ : Iso (Pushout (λ _ → b) g) ((B , b) ⋁ (cofib g , inl tt))
  Iso.fun Iso-PushoutConst→⋁ = PushoutConst→⋁
  Iso.inv Iso-PushoutConst→⋁ = ⋁→PushoutConst
  Iso.rightInv Iso-PushoutConst→⋁ = ⋁→PushoutConst→⋁
  Iso.leftInv Iso-PushoutConst→⋁ = PushoutConst→⋁→PushoutConst

Sfam0 : (m : ℕ) (p : _) → Sgen.Sfam zero (suc m) p ≃ Bool
Sfam0 m (eq x) = idEquiv _
Sfam0 m (gt x) = idEquiv _

SfamContr : (n : ℕ) (p : _) → isContr (Sgen.Sfam (suc n) (suc zero) p)
fst (SfamContr n p) = Sgen.Sfam∙ (suc n) zero p
snd (SfamContr n (lt x)) y = refl
snd (SfamContr n (eq x)) y = ⊥.rec (snotz (sym (cong predℕ x)))

SαMainEqGen : (n m : ℕ) (p : _) (q : _)
  → Sgen.Sfam n (suc (suc m)) p
     ≃ (((Sgen.Sfam n (suc m) q) , Sgen.Sfam∙ n m q)
     ⋁ (cofib {A = Fin (ScardGen n (suc m) p) × S₊ m} fst , inl tt))
SαMainEqGen zero m p (eq x) =
  compEquiv (Sfam0 (suc m) p) (compEquiv (isoToEquiv
              (invIso (PushoutAlongEquiv
                (invEquiv (isContr→≃Unit ((inl tt)
                , λ { (inl x) → refl}))) λ _ → true)))
                (symPushout _ _))
SαMainEqGen zero m p (gt x) =
  compEquiv (Sfam0 (suc m) p) (compEquiv (isoToEquiv
              (invIso (PushoutAlongEquiv
                (invEquiv (isContr→≃Unit ((inl tt)
                , λ { (inl x) → refl}))) λ _ → true)))
                (symPushout _ _))
SαMainEqGen (suc n) m (lt x₁) (lt x) =
  invEquiv (isContr→≃Unit ((inl tt)
  , (λ { (inl x) → refl ; (inr (inl x)) → push tt ; (push a i) j → push tt (i ∧ j)})))
SαMainEqGen (suc n) m (eq x₁) (lt x) =
  compEquiv (invEquiv (isoToEquiv (⋁-lUnitIso {ℓ' = ℓ-zero} {A = S₊∙ (suc n)})))
      (invEquiv (pushoutEquiv _ _ _ _ (idEquiv Unit) (invEquiv (isContr→≃Unit isContrUnit*))
        (invEquiv (compEquiv (isoToEquiv (IsoSucSphereSusp n))
          (compEquiv (invEquiv PushoutSusp≃Susp)
            (pushoutEquiv _ _ _ _
              (compEquiv (pathToEquiv (cong S₊ (sym (cong (predℕ ∘ predℕ) x₁))))
                         (compEquiv (isoToEquiv (invIso lUnit×Iso))
                           (Σ-cong-equiv-fst (isoToEquiv Iso-Unit-Fin1))))
              (idEquiv Unit) (isoToEquiv Iso-Unit-Fin1) (λ _ _ → tt) λ _ _ → 0 , tt))))
        (funExt (λ _ → isPropUnit* _ _))
        λ i x → IsoSucSphereSusp∙ n i))
SαMainEqGen (suc n) m (gt x₁) (lt x) = ⊥.rec (¬squeeze (x₁ , x))
SαMainEqGen (suc n) m (lt x₁) (eq x) = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ suc n) x x₁))
SαMainEqGen (suc n) m (eq x₁) (eq x) = ⊥.rec (¬m<ᵗm (subst (suc n <ᵗ_) (sym x ∙ cong predℕ x₁) <ᵗsucm))
SαMainEqGen (suc n) m (gt x₁) (eq x) =
  compEquiv (isoToEquiv (invIso (⋁-rUnitIso {A = S₊∙ (suc n)})))
      ((pushoutEquiv _ (λ _ → lift {ℓ-zero} {ℓ-zero} tt) _ _ (idEquiv Unit) (idEquiv _)
        (isoToEquiv (isContr→Iso (isContrUnit*)
          (inl tt , λ { (inl x) → refl})))
        (λ i x → ptSn (suc n))
        refl))
SαMainEqGen (suc n) m (lt x₁) (gt x) = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x x₁))
SαMainEqGen (suc n) m (eq x₁) (gt x) = ⊥.rec (¬-suc-n<ᵗn (subst (suc n <ᵗ_) (cong (predℕ ∘ predℕ) x₁) x))
SαMainEqGen (suc n) m (gt x₁) (gt x) =
  compEquiv (invEquiv (isoToEquiv (⋁-rUnitIso {ℓ' = ℓ-zero} {A = S₊∙ (suc n)})))
   (invEquiv (pushoutEquiv _ _ _ _ (idEquiv Unit) (idEquiv (S₊ (suc n)))
     (isContr→Equiv ((inl tt) , (λ { (inl x) → refl})) isContrUnit*)
     refl
     (funExt (λ _ → isPropUnit* _ _))))

SαEqMain : (n m : ℕ) → Sfam n (suc (suc m))
                      ≃ (((Sfam n (suc m)) , Sfam∙ n m)
                      ⋁ (cofib {A = Fin (Scard n (suc m)) × S₊ m} fst , inl tt))
SαEqMain n m = SαMainEqGen n m (suc (suc m) ≟ᵗ suc n) (suc m ≟ᵗ suc n)

SαEqGen : (n m : ℕ) (p : Trichotomyᵗ (suc m) (suc n)) (q : _)
  → (Sgen.Sfam n (suc m) p) ≃ Pushout (SαGen n m p q) fst
SαEqGen zero zero p q = compEquiv (Sfam0 0 p) (compEquiv (isoToEquiv Iso-Bool-Fin2) (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _)))
SαEqGen (suc n) zero p q =
  compEquiv (isContr→Equiv (SfamContr n p) (flast , (λ {(zero , tt) → refl})))
    (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _))
SαEqGen n (suc m) p q =
  compEquiv (SαMainEqGen n m p q) (isoToEquiv (invIso (Iso-PushoutConst→⋁ (Sgen.Sfam∙ n m q) fst)))

invEqSαEqGen∙ : (n m : ℕ) (p : Trichotomyᵗ (suc (suc m)) (suc n)) (q : _)
  → invEq (SαEqGen n (suc m) p q) (inl (Sgen.Sfam∙ n m q)) ≡ Sgen.Sfam∙ n (suc m) p
invEqSαEqGen∙ (suc n) m (lt x) (lt x₁) = refl
invEqSαEqGen∙ n m (lt x) (eq x₁) = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ n) x₁ x))
invEqSαEqGen∙ (suc n) (suc m) (lt x) (gt x₁) = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x x₁))
invEqSαEqGen∙ (suc n) m (eq x) (lt x₁) = refl
invEqSαEqGen∙ n m (eq x) (eq x₁) =
  ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc m)) (x₁ ∙ sym x) <ᵗsucm))
invEqSαEqGen∙ n m (eq x) (gt x₁) = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ suc m) (sym x) x₁))
invEqSαEqGen∙ (suc n) m (gt x) (lt x₁) = ⊥.rec (¬squeeze (x , x₁))
invEqSαEqGen∙ zero m (gt x) (eq x₁) = refl
invEqSαEqGen∙ (suc n) m (gt x) (eq x₁) = refl
invEqSαEqGen∙ zero m (gt x) (gt x₁) = refl
invEqSαEqGen∙ (suc n) m (gt x) (gt x₁) = refl

SαEq : (n m : ℕ) → (Sfam n (suc m)) ≃ Pushout (Sα n m) fst
SαEq n m = SαEqGen n m (suc m ≟ᵗ suc n) (m ≟ᵗ suc n)

Sˢᵏᵉˡ : (n : ℕ) → CWskel ℓ-zero
fst (Sˢᵏᵉˡ n) = Sfam n
fst (snd (Sˢᵏᵉˡ n)) = Scard n
fst (snd (snd (Sˢᵏᵉˡ n))) = Sα n
fst (snd (snd (snd (Sˢᵏᵉˡ n)))) = λ{()}
snd (snd (snd (snd (Sˢᵏᵉˡ n)))) = SαEq n

SfamTopElement : (n : ℕ) → S₊ n ≃ (Sfam n (suc n)) 
SfamTopElement n with (n ≟ᵗ n)
... | lt x = ⊥.rec (¬m<ᵗm x)
... | eq x = idEquiv _
... | gt x = idEquiv _

SˢᵏᵉˡConverges : (n : ℕ) (k : ℕ)
  → isEquiv (invEq (SαEq n (k +ℕ suc n)) ∘ inl)
SˢᵏᵉˡConverges n k = compEquiv (inl , h n _ (<→<ᵗ (k , refl))) (invEquiv (SαEq n (k +ℕ suc n))) .snd
  where
  h : (n m : ℕ) → n <ᵗ m → isEquiv {A = Sfam n m} {B = Pushout (Sα n m) fst} inl
  h n (suc m) p with (m ≟ᵗ n)
  ... | lt x = ⊥.rec (¬squeeze (x , p))
  ... | eq x = isoToIsEquiv (PushoutEmptyFam (¬Scard n (suc m) p ∘ fst) (¬Scard n (suc m) p))
  ... | gt x = isoToIsEquiv (PushoutEmptyFam (¬Scard n (suc m) p ∘ fst) (¬Scard n (suc m) p))

isCWSphere : (n : ℕ) → isCW (S₊ n)
fst (isCWSphere n) = Sˢᵏᵉˡ n
snd (isCWSphere n) = compEquiv (SfamTopElement n) (isoToEquiv (converges→ColimIso (suc n) (SˢᵏᵉˡConverges n)))

Sᶜʷ : (n : ℕ) → CW ℓ-zero
fst (Sᶜʷ n) = S₊ n
snd (Sᶜʷ n) = ∣ isCWSphere n ∣₁

-- open import

sucn≠n : {n : ℕ} → ¬ (suc n ≡ n)
sucn≠n {n = zero} = snotz
sucn≠n {n = suc n} p = sucn≠n {n = n} (cong predℕ p)

open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.Int

module _ (n : ℕ) where
  ScardDiag : isContr (Fin (Scard (suc n) (suc n)))
  ScardDiag with (n ≟ᵗ n)
  ... | lt x = ⊥.rec (¬m<ᵗm x)
  ... | eq x = inhProp→isContr fzero isPropFin1
  ... | gt x = ⊥.rec (¬m<ᵗm x)

  HₙSⁿ→ℤ-fun : (a : Fin (Scard (suc n) (suc n)) → ℤ) → ℤ
  HₙSⁿ→ℤ-fun a = a (ScardDiag .fst)

  HₙSⁿ→ℤ-coh :
       (a b : Fin (Scard (suc n) (suc n)) → ℤ)
    → (aker : ∂ (Sˢᵏᵉˡ (suc n)) n .fst a ≡ λ _ → 0)
    → (bker : ∂ (Sˢᵏᵉˡ (suc n)) n .fst b ≡ λ _ → 0)
    → (r : Σ[ t ∈ (Fin (Scard (suc n) (suc (suc n))) → ℤ) ]
             ∂ (Sˢᵏᵉˡ (suc n)) (suc n) .fst t ≡ λ q → a q - b q)
    → HₙSⁿ→ℤ-fun a ≡ HₙSⁿ→ℤ-fun b
  HₙSⁿ→ℤ-coh a b aker bker r with (n ≟ᵗ n) | (suc n ≟ᵗ n)
  ... | lt x | t = ⊥.rec (¬m<ᵗm x) 
  ... | eq x | lt x₁ = ⊥.rec (¬-suc-n<ᵗn x₁)
  ... | eq x | eq x₁ = ⊥.rec (sucn≠n x₁)
  ... | eq x | gt x₁ = sym (+Comm (b fzero) 0
                     ∙ cong (_+ b fzero) (funExt⁻ (snd r) fzero)
                     ∙ sym (+Assoc (a fzero) (- b fzero) (b fzero))
                     ∙ cong (a fzero +_) (-Cancel' (b fzero)))
  ... | gt x | t = ⊥.rec (¬m<ᵗm x)

  HₙSⁿ→ℤ : Hˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) n . fst → ℤ
  HₙSⁿ→ℤ = SQ.elim (λ _ → isSetℤ) (λ a → HₙSⁿ→ℤ-fun (fst a))
    λ a b → PT.elim (λ _ → isSetℤ _ _)
      λ x →  HₙSⁿ→ℤ-coh (fst a) (fst b) (snd a) (snd b) (fst x , cong fst (snd x))

  ∂VanishS : (n : ℕ) (t : _) → ∂ (Sˢᵏᵉˡ (suc n)) n .fst t ≡ λ _ → pos 0 
  ∂VanishS zero t = funExt λ { (zero , p) → ·Comm (t fzero) (pos 0)}
  ∂VanishS (suc n) t = funExt λ y → ⊥.rec (¬Scard' n y)

  ℤ→HₙSⁿ-fun : ℤ → Hˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) n . fst
  ℤ→HₙSⁿ-fun z = [ (λ _ → z) , ∂VanishS n (λ _ → z) ]

  ℤ→HₙSⁿ : GroupHom ℤGroup (Hˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) n)
  fst (ℤ→HₙSⁿ) = ℤ→HₙSⁿ-fun
  snd (ℤ→HₙSⁿ) = makeIsGroupHom λ x y
    → cong [_] (Σ≡Prop (λ _ → isOfHLevelPath' 1 (isSetΠ (λ _ → isSetℤ)) _ _)
                refl)

  HₙSⁿ→ℤ→HₙSⁿ : (x : _) → ℤ→HₙSⁿ-fun (HₙSⁿ→ℤ x) ≡ x
  HₙSⁿ→ℤ→HₙSⁿ =
    SQ.elimProp (λ _ → GroupStr.is-set (snd (Hˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) n)) _ _)
        λ {(a , p) → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
                               (funExt λ t → cong a (ScardDiag .snd t)))}

  ℤ≅HₙSⁿ : GroupIso ℤGroup (Hˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) n)
  Iso.fun (fst ℤ≅HₙSⁿ) = ℤ→HₙSⁿ .fst
  Iso.inv (fst ℤ≅HₙSⁿ) = HₙSⁿ→ℤ
  Iso.rightInv (fst ℤ≅HₙSⁿ) = HₙSⁿ→ℤ→HₙSⁿ
  Iso.leftInv (fst ℤ≅HₙSⁿ) _ = refl
  snd ℤ≅HₙSⁿ = ℤ→HₙSⁿ .snd

  HₙSⁿ≅ℤ : GroupIso (Hˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) n) ℤGroup
  HₙSⁿ≅ℤ = invGroupIso ℤ≅HₙSⁿ

  genHₙSⁿ : Hˢᵏᵉˡ (Sˢᵏᵉˡ (suc n)) n .fst
  genHₙSⁿ = [ (λ _ → 1) , (∂VanishS n (λ _ → 1)) ]


