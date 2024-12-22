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

Sfam : (n : ℕ) → ℕ → Type
Sfam n zero = ⊥
Sfam n (suc m) with (m ≟ᵗ n)
... | lt x = Unit
... | eq x = S₊ n
... | gt x = S₊ n

Sfam∙ : (n m : ℕ) → Sfam n (suc m)
Sfam∙ n m with (m ≟ᵗ n)
... | lt x = tt
... | eq x = ptSn n
... | gt x = ptSn n

Scard : (n : ℕ) → ℕ → ℕ
Scard zero zero = 2
Scard zero (suc m) = 0
Scard (suc n) zero = 1
Scard (suc n) (suc m) with (m ≟ᵗ n)
... | lt x = 0
... | eq x = 1
... | gt x = 0

Sα : (n m : ℕ) → Fin (Scard n m) × S⁻ m → Sfam n m
Sα n (suc m) _ = Sfam∙ n m

¬Scard : (n m : ℕ) → n <ᵗ m → ¬ Fin (Scard n m)
¬Scard zero (suc m) p = ¬Fin0
¬Scard (suc n) (suc m) p with (m ≟ᵗ n)
... | lt x = snd
... | eq x = λ _ → ¬m<ᵗm (subst (n <ᵗ_) x p)
... | gt x = snd

¬Scard' : (n m : ℕ) → (n <ᵗ m) → ¬ (Fin (Scard (suc m) (suc n)))
¬Scard' n m p with (n ≟ᵗ m)
... | lt x = snd
... | eq x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) x p))
... | gt x = snd

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

SαEqMain : (n m : ℕ) → Sfam n (suc (suc m))
                      ≃ (((Sfam n (suc m)) , Sfam∙ n m)
                      ⋁ (cofib {A = Fin (Scard n (suc m)) × S₊ m} fst , inl tt))
SαEqMain zero m with (m ≟ᵗ zero)
... | eq x = compEquiv (isoToEquiv
              (invIso (PushoutAlongEquiv
                (invEquiv (isContr→≃Unit ((inl tt)
                , λ { (inl x) → refl}))) λ _ → true)))
                (symPushout _ _)
... | gt x = compEquiv (isoToEquiv
              (invIso (PushoutAlongEquiv
                (invEquiv (isContr→≃Unit ((inl tt)
                , λ { (inl x) → refl}))) λ _ → true)))
                (symPushout _ _)
SαEqMain (suc n) m with (m ≟ᵗ suc n) | (m ≟ᵗ n)
... | lt x | lt x₁ = invEquiv (isContr→≃Unit ((inl tt)
  , (λ { (inl x) → refl ; (inr (inl x)) → push tt ; (push a i) j → push tt (i ∧ j)})))
... | lt x | eq x₁ =
  compEquiv (invEquiv (isoToEquiv (⋁-lUnitIso {ℓ' = ℓ-zero} {A = S₊∙ (suc n)})))
                               (invEquiv (pushoutEquiv _ _ _ _ (idEquiv Unit) (invEquiv (isContr→≃Unit isContrUnit*))
                                 (invEquiv (compEquiv (isoToEquiv (IsoSucSphereSusp n))
                                   (compEquiv (invEquiv PushoutSusp≃Susp)
                                     (pushoutEquiv _ _ _ _
                                       (compEquiv (pathToEquiv (cong S₊ (sym x₁)))
                                                  (compEquiv (isoToEquiv (invIso lUnit×Iso))
                                                    (Σ-cong-equiv-fst (isoToEquiv Iso-Unit-Fin1))))
                                       (idEquiv Unit) (isoToEquiv Iso-Unit-Fin1) (λ _ _ → tt) λ _ _ → 0 , tt))))
                                 (funExt (λ _ → isPropUnit* _ _))
                                 λ i x → IsoSucSphereSusp∙ n i))
... | lt x | gt x₁ = ⊥.rec (¬squeeze (x₁ , x))
... | eq x | lt x₁ = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ n) x x₁))
... | eq x | eq x₁ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) (sym x ∙ x₁) <ᵗsucm))
... | eq x | gt x₁ = compEquiv (isoToEquiv (invIso (⋁-rUnitIso {A = S₊∙ (suc n)})))
                      ((pushoutEquiv _ (λ _ → lift {ℓ-zero} {ℓ-zero} tt) _ _ (idEquiv Unit) (idEquiv _)
                        (isoToEquiv (isContr→Iso (isContrUnit*)
                          (inl tt , λ { (inl x) → refl})))
                        (λ i x → ptSn (suc n))
                        refl))
... | gt x | lt x₁ = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x x₁))
... | gt x | eq x₁ = ⊥.rec (¬-suc-n<ᵗn (subst (suc n <ᵗ_) x₁ x))
... | gt x | gt x₁ = compEquiv (invEquiv (isoToEquiv (⋁-rUnitIso {ℓ' = ℓ-zero} {A = S₊∙ (suc n)})))
                               (invEquiv (pushoutEquiv _ _ _ _ (idEquiv Unit) (idEquiv (S₊ (suc n)))
                                 (isContr→Equiv ((inl tt) , (λ { (inl x) → refl})) isContrUnit*)
                                 refl
                                 (funExt (λ _ → isPropUnit* _ _))))

SαEq : (n m : ℕ) → (Sfam n (suc m)) ≃ Pushout (Sα n m) fst
SαEq zero zero = compEquiv (isoToEquiv Iso-Bool-Fin2) (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _))
SαEq (suc n) zero = compEquiv (isoToEquiv Iso-Unit-Fin1) (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _))
SαEq n (suc m) = compEquiv (SαEqMain n m) (isoToEquiv (invIso (Iso-PushoutConst→⋁ (Sfam∙ n m) fst)))

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
  ∂VanishS (suc n) t = funExt λ y → ⊥.rec (¬Scard' _ _ <ᵗsucm y)

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
