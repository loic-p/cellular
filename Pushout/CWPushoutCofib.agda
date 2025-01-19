{-# OPTIONS --cubical --lossy-unification #-}
module Pushout.CWPushoutCofib where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.CW.Base
open import Cubical.CW.Map

open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
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

open import Cubical.Data.Nat

open import Cubical.CW.Properties
open import Cubical.Algebra.ChainComplex
open import Cubical.CW.ChainComplex
open import Cubical.CW.Homology
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Foundations.Pointed
open import Cubical.HITs.Wedge

open import Hurewicz.random
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Path


open import Cubical.Homotopy.Group.Base

private
  pathlem : ∀ {ℓ} {A : Type ℓ} {x : A}  (Fx : x ≡ x) (Fpt : refl ≡ Fx) (p q : Fx ≡ Fx)
     → Square (rUnit Fx ∙ cong (Fx ∙_) Fpt)
               (rUnit Fx ∙ cong (Fx ∙_) Fpt)
               (p ∙ q) (cong₂ _∙_ p q)
  pathlem = J> λ p q → sym (rUnit _)
    ◁ flipSquare (((λ i → (λ j → rUnit (p j) i) ∙ λ j → lUnit (q j) i)
    ▷ sym (cong₂Funct _∙_ p q)))
    ▷ rUnit _

Bouquet→ΩBouquetSuspPresStr : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
  → (f g : S₊∙ (suc n) →∙ ⋁gen∙ A (λ _ → S₊∙ (suc n))) (s : _)
  → Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc n)) (∙Π f g .fst s)
  ≡ Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc n)) (fst f s)
  ∙ Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc n)) (fst g s)
Bouquet→ΩBouquetSuspPresStr {A = A} zero f g base =
    rUnit refl
  ∙ refl
  ∙ cong₂ _∙_ (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ 1)) (snd f)))
              (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ 1)) (snd g)))
Bouquet→ΩBouquetSuspPresStr {A = A} zero f g (loop i) j =
  m _ _ (sym (snd f)) _ (sym (snd g)) (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ 1))
    refl (cong (fst f) loop) (cong (fst g) loop) j i 
  where
  m : ∀ {ℓ} {A B : Type ℓ} (x : A) (fpt : A) (fp : x ≡ fpt) (gpt : A) (gp : x ≡ gpt)
    {b : B} (F : A → b ≡ b) (Fpt : F x ≡ refl) (fl : fpt ≡ fpt) (gl : gpt ≡ gpt)
    → Square (cong F ((fp ∙∙ fl ∙∙ sym fp) ∙ (gp ∙∙ gl ∙∙ sym gp)))
              (cong₂ _∙_ (cong F fl) (cong F gl))
              (rUnit (F x) ∙ cong (F x ∙_) (sym Fpt) ∙ cong₂ _∙_ (cong F fp) (cong F gp))
              (rUnit (F x) ∙ cong (F x ∙_) (sym Fpt) ∙ cong₂ _∙_ (cong F fp) (cong F gp))
  m x = J> (J> λ F Fpt fl gl
    → (cong (cong F) (λ j i → (rUnit fl (~ j) ∙ rUnit gl (~ j)) i)
    ∙ cong-∙ F fl gl)
    ◁ flipSquare (cong₂ _∙_ refl (sym (rUnit _))
                ◁ pathlem (F x) (sym Fpt) (cong F fl) (cong F gl)
                ▷ cong₂ _∙_ refl (rUnit _)))
Bouquet→ΩBouquetSuspPresStr {A = A} (suc n) f g north =
   rUnit refl
  ∙ refl
  ∙ cong₂ _∙_ (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc (suc n)))) (snd f)))
              (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc (suc n)))) (snd g)))
Bouquet→ΩBouquetSuspPresStr {A = A} (suc n) f g south =
  rUnit refl
  ∙ refl
  ∙ cong₂ _∙_ (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc (suc n))))
                   (cong (fst f) (sym (merid (ptSn (suc n)))) ∙ snd f)))
              (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc (suc n))))
                   (cong (fst g) (sym (merid (ptSn (suc n)))) ∙ snd g)))
Bouquet→ΩBouquetSuspPresStr {A = A} (suc n) f g (merid a i) j =
  m _ _ (sym (snd f)) _ (sym (snd g)) (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc (suc n)))) refl
    _ (cong (fst f)  (merid (ptSn (suc n)))) (cong (fst f) (merid a))
    _ (cong (fst g) (merid (ptSn (suc n)))) (cong (fst g) (merid a))
    _ (sym (cong-∙ (fst f) (merid a) (sym (merid (ptSn (suc n))))))
    _ (sym (cong-∙ (fst g) (merid a) (sym (merid (ptSn (suc n)))))) j i

  
  where
  m : ∀ {ℓ} {A B : Type ℓ} (n : A) (fn : A) (fp : n ≡ fn) (gn : A) (gp : n ≡ gn)
    {b : B} (F : A → b ≡ b) (Fn : F n ≡ refl) (fs : A) (flpt : fn ≡ fs) (fl : fn ≡ fs)  (gs : A) (glpt : gn ≡ gs) (gl : gn ≡ gs)
    (w : _) → fl ∙ sym flpt ≡ w → (u : _) → gl ∙ sym glpt ≡ u
    → Square (cong F ((fp ∙∙ w ∙∙ sym fp) ∙ (gp ∙∙ u ∙∙ sym gp)))
              (cong₂ _∙_ (cong F fl) (cong F gl)) -- (cong₂ _∙_ (cong F fl) (cong F gl))
              (rUnit (F n) ∙ cong (F n ∙_) (sym Fn) ∙ cong₂ _∙_ (cong F fp) (cong F gp))
              (rUnit (F n) ∙ cong (F n ∙_) (sym Fn)
                ∙ cong₂ _∙_ (cong F (sym (sym flpt ∙ sym fp)))
                            (cong F (sym (sym glpt ∙ sym gp))))
  m n = J> (J> λ F Fpt → J> λ fp → J> λ gp
    → J> (J> ((cong (cong F) (cong₂ _∙_ (sym (rUnit _) ∙ sym (rUnit fp))
                                         (sym (rUnit _) ∙ sym (rUnit gp)))
                           ∙  cong-∙ F fp gp)
            ◁ flipSquare (cong₂ _∙_ refl (sym (rUnit _))
              ◁ flipSquare (flipSquare (pathlem _ (sym Fpt) _ _))
            ▷ cong₂ _∙_ refl
               (rUnit _
               ∙ cong₂ _∙_ refl λ  j i → F (rUnit {x = n} refl j i)
                                       ∙ F (rUnit {x = n} refl j i))))))

⋁→Homogeneous≡ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Pointed ℓ'} {C : Type ℓ''}
  (f g : ⋁gen A B → C) → ((x : C) → isHomogeneous (C , x))
  → f (inl tt) ≡ g (inl tt)
  → ((x : _) → f (inr x) ≡ g (inr x))
  → (x : _) → f x ≡ g x
⋁→Homogeneous≡ {A = A} {B = B}{C = C} f g hom p q = funExt⁻ (cong fst main)
  where
  ptC = f (inl tt)

  f' g' : ⋁gen∙ A B →∙ (C , ptC)
  f' = f , refl
  g' = g , sym p

  ⋁→Iso : ∀ {ℓ} (C : Pointed ℓ) → Iso (⋁gen∙ A B →∙ C) ((x : A) → B x →∙ C)
  fst (Iso.fun (⋁→Iso C) f x) y = fst f (inr (x , y))
  snd (Iso.fun (⋁→Iso C) f x) = cong (fst f) (sym (push x)) ∙ snd f
  fst (Iso.inv (⋁→Iso C) f) (inl x) = pt C
  fst (Iso.inv (⋁→Iso C) f) (inr (x , y)) = f x .fst y 
  fst (Iso.inv (⋁→Iso C) f) (push a i) = f a .snd (~ i)
  snd (Iso.inv (⋁→Iso C) f) = refl
  Iso.rightInv (⋁→Iso C) f = funExt λ x → ΣPathP (refl , sym (rUnit _))
  Iso.leftInv (⋁→Iso C) f =
    ΣPathP ((funExt (λ { (inl x) → sym (snd f) ; (inr x) → refl
      ; (push a i) j → compPath-filler (cong (fst f) (sym (push a))) (snd f) (~ j) (~ i)}))
      , λ i j → snd f (~ i ∨ j))

  main : f' ≡ g'
  main = sym (Iso.leftInv (⋁→Iso (C , ptC)) f')
       ∙∙ cong (Iso.inv (⋁→Iso (C , ptC))) (funExt (λ x → →∙Homogeneous≡ (hom _) (funExt (λ y → q (x , y)))))
       ∙∙ Iso.leftInv (⋁→Iso (C , ptC)) g'

-- module _ {ℓ ℓ' : Level} where
--   Pushout→Bouquet' : {Cₙ Cₙ₊₁ Cₙ₊₂ : Type ℓ} (n mₙ mₙ₊₁ : ℕ)
--     (αₙ₊₁ : Fin mₙ₊₁ × S₊ n → Cₙ₊₁)
--     (αₙ : Fin mₙ × S⁻ n → Cₙ)
--     (e : Cₙ₊₁ ≃ Pushout αₙ fst)
--     (e2 : Cₙ₊₂ ≃ Pushout αₙ₊₁ fst)
--     → (a : Fin mₙ₊₁ × S₊ n) → SphereBouquet n (Fin mₙ)
--   Pushout→Bouquet' zero mₙ mₙ₊₁ αₙ₊₁ αₙ e e2 a = {!!}
--   Pushout→Bouquet' (suc zero) mₙ mₙ₊₁ αₙ₊₁ αₙ e e2 (l , base) = inl tt
--   Pushout→Bouquet' (suc zero) mₙ mₙ₊₁ αₙ₊₁ αₙ e e2 (l , loop i) = ({!!} ∙∙ {!λ i → ?!} ∙∙ {!!}) i
--   Pushout→Bouquet' (suc (suc n)) mₙ mₙ₊₁ αₙ₊₁ αₙ e e2 a = {!!}
--   -- inr {!!}

--   Pushout→BouquetEq : {Cₙ Cₙ₊₁ Cₙ₊₂ : Type ℓ} (n mₙ mₙ₊₁ : ℕ)
--     (αₙ₊₁ : Fin mₙ₊₁ × S₊ n → Cₙ₊₁)
--     (αₙ : Fin mₙ × S⁻ n → Cₙ)
--     (e : Cₙ₊₁ ≃ Pushout αₙ fst)
--     (e2 : Cₙ₊₂ ≃ Pushout αₙ₊₁ fst)
--     (t : _) (s : _)
--     → Pushout→Bouquet {Cₙ = Cₙ} {Cₙ₊₁} n mₙ αₙ e (fst e (αₙ₊₁ (t , s)))
--     ≡ {!Pushout→Bouquet!}
--   Pushout→BouquetEq n mₙ αₙ e = {!!}
{-
-- Maps back and forth
module BouquetFuns {Cₙ Cₙ₊₁ : Type ℓ} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where
  CTB : cofib (invEq e ∘ inl) → SphereBouquet n (Fin mₙ)
  CTB (inl x) = inl tt
  CTB (inr x) = Pushout→Bouquet n mₙ αₙ e (fst e x)
  CTB (push a i) = Pushout→Bouquet n mₙ αₙ e (secEq e (inl a) (~ i))
-}


module _ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} where
  foldL : A ⋁ B → fst A
  foldL (inl x) = x
  foldL (inr x) = pt A
  foldL (push a i) = pt A

  foldL∙ : (A ⋁∙ₗ B) →∙ A
  fst foldL∙ = foldL
  snd foldL∙ = refl
  
  foldR : A ⋁ B → fst B
  foldR (inl x) = pt B
  foldR (inr x) = x
  foldR (push a i) = pt B

  foldR∙ : (A ⋁∙ₗ B) →∙ B
  fst foldR∙ = foldR
  snd foldR∙ = refl

cellMap→finCellMap : ∀ {ℓ ℓ'} (m : ℕ) {C : CWskel ℓ} {D : CWskel ℓ'} (ϕ : cellMap C D) → finCellMap m C D
FinSequenceMap.fmap (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.map ϕ x
FinSequenceMap.fcomm (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.comm ϕ x


Pushout-⊎-Iso : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso (A ⊎ B) (Pushout {A = ⊥} {B = A} {C = B} (λ()) λ())
Iso.fun Pushout-⊎-Iso (inl x) = inl x
Iso.fun Pushout-⊎-Iso (inr x) = inr x
Iso.inv Pushout-⊎-Iso (inl x) = inl x
Iso.inv Pushout-⊎-Iso (inr x) = inr x
Iso.rightInv Pushout-⊎-Iso (inl x) = refl
Iso.rightInv Pushout-⊎-Iso (inr x) = refl
Iso.leftInv Pushout-⊎-Iso (inl x) = refl
Iso.leftInv Pushout-⊎-Iso (inr x) = refl

IsoSphereSusp : (n : ℕ) → Iso (S₊ n) (Susp (S⁻ n))
IsoSphereSusp zero = BoolIsoSusp⊥
IsoSphereSusp (suc n) = IsoSucSphereSusp n

finSplit3≃ : ∀ n m l → Fin ((n +ℕ m) +ℕ l) ≃ ((Fin n) ⊎ (Fin m)) ⊎ (Fin l)
finSplit3≃ n m l = isoToEquiv (compIso (invIso (Iso-Fin⊎Fin-Fin+ {n = n + m} {l}))
    (⊎Iso (invIso (Iso-Fin⊎Fin-Fin+ {n = n} {m})) idIso))

finSplit3 : ∀ n m l → Fin ((n +ℕ m) +ℕ l) → ((Fin n) ⊎ (Fin m)) ⊎ (Fin l)
finSplit3 n m l = fst (finSplit3≃ n m l)

invSides-hfill : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → I → I → I → A
invSides-hfill {x = x} p q i j =
  hfill (λ k → λ { (i = i0) → p (k ∧ j)
                 ; (i = i1) → q (~ j ∧ k)
                 ; (j = i0) → q (i ∧ k)
                 ; (j = i1) → p (~ i ∧ k)})
        (inS x)

invSides-hfill1 : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → I → I → I → A
invSides-hfill1 {x = x} p q i j =
  hfill (λ k → λ { (i = i0) → p j
                 ; (i = i1) → q (~ j ∧ k)
                 ; (j = i0) → q (i ∧ k)
                 ; (j = i1) → p (~ i)})
        (inS (p ((~ i) ∧ j)))

invSides-hfill2 : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → I → I → I → A
invSides-hfill2 {x = x} p q i j =
  hfill (λ k → λ { (i = i0) → p (k ∧ j)
                 ; (i = i1) → q (~ j)
                 ; (j = i0) → q (i)
                 ; (j = i1) → p (~ i ∧ k)})
        (inS (q (i ∧ (~ j))))


-- module _ {ℓ : Level} {Xₙ₊₁ : Type ℓ}

open import Cubical.Foundations.Path
open import Cubical.Data.Empty as ⊥

open import Cubical.Relation.Nullary

module _ {ℓ : Level} (B : CWskel ℓ) where
  open CWskel-fields
  open import Cubical.Foundations.Univalence
  strictifyFam : ℕ → Type ℓ
  strictifyFam≡ : (n : ℕ) → strictifyFam n ≡ fst B n
  strictifyFame : (n : ℕ) → fst B n ≃ strictifyFam n
  strictifyFamα : (n : ℕ) → Fin (fst (B .snd) n) × S⁻ n → strictifyFam n
  strictifyFame2 : (n : ℕ) → (Pushout (α B n) fst) ≃ (Pushout (strictifyFamα n) fst)
  strictifyFam zero = fst B 0
  strictifyFam (suc n) = Pushout (strictifyFamα n) fst
  strictifyFamα n = fst (strictifyFame n) ∘ α B n
  strictifyFame zero = idEquiv _
  strictifyFame (suc n) =
    compEquiv (e B n)
              (strictifyFame2 n)
  strictifyFame2 n =
    pushoutEquiv _ _ _ _ (idEquiv _) (strictifyFame n) (idEquiv _)
                   (λ _ x → fst (strictifyFame n) (α B n x))
                   (λ _ x → fst x)
  strictifyFam≡ zero = refl
  strictifyFam≡ (suc n) = ua (invEquiv (strictifyFame (suc n)))

  strictCWskel : CWskel ℓ
  fst strictCWskel = strictifyFam
  fst (snd strictCWskel) = card B
  fst (snd (snd strictCWskel)) = strictifyFamα
  fst (snd (snd (snd strictCWskel))) = fst (snd (snd (snd B)))
  snd (snd (snd (snd strictCWskel))) = λ _ → idEquiv _

  strict≡Gen : ∀ {ℓ ℓ'} {A : Type ℓ} {C D : Type ℓ'} (α : A → C) (e : C ≃ D) (x : A)
    → PathP (λ i → ua (invEquiv e) i) (fst e (α x)) (α x)
  strict≡Gen α e x i =
    hcomp (λ k → λ {(i = i0) → fst e (α x)
                   ; (i = i1) → retEq e (α x) k})
          (ua-gluePt (invEquiv e) i (fst e (α x)))

  strict≡GenT' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C D : Type ℓ''}
    {E : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))} (g : A → B)
    (e : C ≃ D)  (α : A → C) (e' : E ≃ Pushout (λ x₁ → α x₁) g)
    → PathP (λ k → ua (invEquiv (compEquiv {C = Pushout (fst e ∘ α) g} e'
                       (pushoutEquiv _ _ _ _ (idEquiv A) e (idEquiv B) (λ i x → fst e (α x)) λ i x → g x))) k
                 ≃ Pushout (λ x₁ → strict≡Gen α e x₁ k) g)
            (idEquiv _)
            e'
  strict≡GenT' {A = A} {B} {C} {D} {E} g =
    EquivJ (λ C e → (α : A → C) (e' : E ≃ Pushout (λ x₁ → α x₁) g)
    → PathP (λ k → ua (invEquiv (compEquiv {C = Pushout (fst e ∘ α) g} e'
                       (pushoutEquiv _ _ _ _ (idEquiv A) e (idEquiv B) (λ i x → fst e (α x)) λ i x → g x))) k
                 ≃ Pushout (λ x₁ → strict≡Gen α e x₁ k) g)
            (idEquiv _)
            e')
         λ a → EquivJ (λ E e' → PathP
      (λ k →
         ua
         (invEquiv
          (compEquiv e'
           (pushoutEquiv a g (λ z → idfun D (a z)) g (idEquiv A) (idEquiv D)
            (idEquiv B) (λ i x → idfun D (a x)) (λ i → g))))
         k
         ≃ Pushout (λ x₁ → strict≡Gen a (idEquiv D) x₁ k) g)
      (idEquiv (Pushout (λ x → idfun D (a x)) g)) e')
      (ΣPathPProp isPropIsEquiv
        (transport
          (λ k → PathP (λ i
            → (sym (lem g a) ∙ sym (cong (ua ∘ invEquiv) (compEquivIdEquiv ((pushoutEquiv a g
                 (λ z → idfun D (a z)) g (idEquiv A) (idEquiv D)
                   (idEquiv B) (λ i₁ x → idfun D (a x)) (λ i₁ → g)))))) k i
                             → Pushout (λ x₁ → strict≡GenId a x₁ (~ k) i) g)
                 (idfun _) (idfun _))
           (funExt (main _ _))))
    where
    strict≡GenId : ∀ {ℓ ℓ'} {A : Type ℓ} {C : Type ℓ'} (α : A → C)(x : A)
                 → strict≡Gen α (idEquiv C) x ≡ λ i → ua-gluePt (invEquiv (idEquiv C)) i (α x) 
    strict≡GenId {C = C} α x j i =
      hcomp (λ k → λ {(i = i0) → α x
                     ; (i = i1) → α x
                     ; (j = i1) → ua-gluePt (invEquiv (idEquiv C)) i (α x)})
            (ua-gluePt (invEquiv (idEquiv C)) i (α x))

    lem : (g : A → B) (α : A → D)
      → ua (invEquiv (pushoutEquiv α g α g (idEquiv A) (idEquiv D) (idEquiv B) refl refl))
      ≡ refl 
    lem g a = cong ua (cong invEquiv (Σ≡Prop isPropIsEquiv {v = idEquiv _}
      (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) j → rUnit (push a) (~ j) i}))
      ∙ invEquivIdEquiv _) ∙ uaIdEquiv

    main : (g : A → B) (α : A → D) (w : _)
      → PathP (λ i → Pushout (λ x₁ → ua-gluePt (invEquiv (idEquiv D)) i (α x₁)) g) w w
    main g α (inl x) i = inl (ua-gluePt (invEquiv (idEquiv D)) i x)
    main g α (inr x) i = inr x
    main g α (push a j) i = push a j

  strict≡α : (n : ℕ) (x : Fin (card B n)) (y : S⁻ n)
    → PathP (λ i → strictifyFam≡ n i)
              
              (strictifyFamα n (x , y))
              (α B n (x , y))
  strict≡α (suc n) x y = strict≡Gen (α B (suc n)) (strictifyFame (suc n)) (x , y)
  
  strict≡e : (n : ℕ) → PathP (λ i → strictifyFam≡ (suc n) i
                                     ≃ Pushout (λ x → strict≡α n (fst x) (snd x) i) fst)
                               (idEquiv _)
                               (e B n)
  strict≡e zero = ΣPathPProp (λ _ → isPropIsEquiv _)
    (symP (toPathP (funExt λ { (inl x) → ⊥.rec (B .snd .snd .snd .fst x)
      ; (inr x) → cong (transport (λ i → Pushout (λ x₁ → strict≡α zero (fst x₁) (snd x₁) (~ i)) fst))
                         ((cong (e B 0 .fst) (transportRefl (invEq (e B 0) (inr x)))
                         ∙ secEq (e B 0) (inr x)))
                     ∙ λ j → inr (transportRefl x j)})))
  strict≡e (suc n) = strict≡GenT' fst (strictifyFame (suc n)) (α B (suc n)) (e B (suc n))    

  strict≡ : strictCWskel ≡ B
  fst (strict≡ i) n = strictifyFam≡ n i
  fst (snd (strict≡ i)) = card B
  fst (snd (snd (strict≡ i))) n (x , y) = strict≡α n x y i
  fst (snd (snd (snd (strict≡ i)))) = fst (snd (snd (snd B)))
  snd (snd (snd (snd (strict≡ i)))) n = strict≡e n i


-- module _ {ℓ ℓ'} {B : CWskel ℓ} {C : CWskel ℓ'} (f : cellMap B C) where

--   open CWskel-fields
--   open SequenceMap renaming (map to ∣_∣)

--   toStrictCWFun : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → fst C n → strictifyFam C n
--   toStrictCWFun C n x = {!!}

--   strictCellMapFun : (n : ℕ) → strictifyFam B n → strictifyFam C n
--   strictCellMapFun zero s = ∣ f ∣ zero s
--   strictCellMapFun (suc n) (inl x) = inl (strictCellMapFun n x)
--   strictCellMapFun (suc n) (inr x) = fst (strictifyFame C (suc n)) (∣ f ∣ (suc n) (invEq (e B n) (inr x))) 
--   strictCellMapFun (suc n) (push a i) =
--     ({!refl!} ∙∙ push ({!a!} , snd a) ∙∙ {!!}) i

--   strictFun : cellMap (strictCWskel B) (strictCWskel C)
--   ∣_∣ strictFun = {!!}
--   comm strictFun = {!!}

module _ {ℓ ℓ'} {P : CWskel ℓ → Type ℓ'} (e : (B : CWskel ℓ) → P (strictCWskel B)) where
  elimStrictCW : (B : _) → P B
  elimStrictCW B = subst P (strict≡ B) (e B)

  elimStrictCWβ : (B : _) → elimStrictCW (strictCWskel B) ≡ e B
  elimStrictCWβ B =
    (λ j → subst P (λ i → H strictCWskel (funExt (λ x → sym (strict≡ x))) B i j) (e (strict≡ B j)))
    ∙ transportRefl (e B)
    where
    H : ∀ {ℓ} {A : Type ℓ}  (F : A → A) (s : (λ x → x) ≡ F) (a : A)
      → Square (λ i → F (s (~ i) a)) refl (λ i → s (~ i) (F a)) refl
    H = J> λ _ → refl

module _ {ℓ ℓ' ℓ''} {P : CWskel ℓ → CWskel ℓ' → Type ℓ''}
         (e : (B : CWskel ℓ) (C : CWskel ℓ') → P (strictCWskel B) (strictCWskel C)) where
  elim2StrictCW : (B : _) (C : _) → P B C
  elim2StrictCW = elimStrictCW (λ B → elimStrictCW (e B))

  elim2StrictCWβ : (B : _) (C : _)
    → elim2StrictCW (strictCWskel B) (strictCWskel C) ≡ e B C
  elim2StrictCWβ B C = funExt⁻ ((elimStrictCWβ {P = λ B → (C : _) → P B C}
                                 (λ B → elimStrictCW (e B))) B) (strictCWskel C)
                     ∙ elimStrictCWβ {P = P (strictCWskel B)} (e B) C

module _ {ℓ ℓ' ℓ'' ℓ'''} {P : CWskel ℓ → CWskel ℓ' → CWskel ℓ'' → Type ℓ'''}
         (e : (B : CWskel ℓ) (C : CWskel ℓ') (D : CWskel ℓ'') → P (strictCWskel B) (strictCWskel C) (strictCWskel D)) where
  elim3StrictCW : (B : _) (C : _) (D : _) → P B C D
  elim3StrictCW = elim2StrictCW λ B C → elimStrictCW (e B C)

  elim3StrictCWβ : (B : _) (C : _) (D : _)
    → elim3StrictCW (strictCWskel B) (strictCWskel C) (strictCWskel D)
     ≡ e B C D
  elim3StrictCWβ B C D =
     funExt⁻ (elim2StrictCWβ {P = λ B C → (D : _) → P B C D}
             (λ B C → elimStrictCW (e B C)) B C) (strictCWskel D)
    ∙ elimStrictCWβ {P = P (strictCWskel B) (strictCWskel C)} (e B C) D

module _ {ℓ ℓ' ℓ'' : Level} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
  (f : cellMap B C)
  (g : cellMap B D) where

  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)

  pushoutA : ℕ → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') 
  pushoutA zero = Lift {ℓ} {ℓ-max ℓ' ℓ''} (B .fst zero)
  pushoutA (suc n) =
    Pushout {A = fst B n} {B = fst C (suc n)} {C = fst D (suc n)}
       (∣ f ∣ (suc n) ∘ CW↪ B n) (∣ g ∣ (suc n) ∘ CW↪ B n)

  pushoutMapₛ : (n : ℕ) → (((A C (suc n)) ⊎ (A D (suc n))) ⊎ (A B n)) × (Susp (S⁻ n)) → pushoutA (suc n)
  pushoutMapₛ n (inl (inl c) , x) =  inl (α C (suc n) (c , (Iso.inv (IsoSphereSusp n) x)))
  pushoutMapₛ n (inl (inr d) , x) = inr (α D (suc n) (d , (Iso.inv (IsoSphereSusp n) x)))
  pushoutMapₛ n (inr b , north) = inl (∣ f ∣ (suc n) (invEq (e B n) (inr b)))
  pushoutMapₛ n (inr b , south) = inr (∣ g ∣ (suc n) (invEq (e B n) (inr b)))
  pushoutMapₛ n (inr b , merid x i) =
    ((λ i → inl (∣ f ∣ (suc n) (invEq (e B n) (push (b , x) (~ i)))))
    ∙∙ push (α B n (b , x))
    ∙∙ λ i → inr (∣ g ∣ (suc n) (invEq (e B n) (push (b , x) i)))) i

  pushoutMidCells : ℕ → ℕ
  pushoutMidCells zero = 0
  pushoutMidCells (suc n) = (card B n)
  

  pushoutCells : ℕ → ℕ
  pushoutCells n = (card C n) +ℕ (card D n) + pushoutMidCells n

  pushoutMap₀ : (Fin (pushoutCells zero)) × (S⁻ 0) → pushoutA 0
  pushoutMap₀ ()

  pushoutMap' : (n : ℕ) → (Fin (pushoutCells (suc n))) × (Susp (S⁻ n)) → pushoutA (suc n)
  pushoutMap' n (a , x) = pushoutMapₛ n (finSplit3 (card C (suc n)) (card D (suc n)) (card B n) a , x)

  pushoutα> : (n : ℕ) → Fin (card C (suc n) + card D (suc n) + card B n) × S₊ n
                       → pushoutA (suc n)
  pushoutα> n (x , y) =
    pushoutMapₛ n ((finSplit3 (card C (suc n)) (card D (suc n)) (card B n) x)
                 , Iso.fun (IsoSphereSusp n) y)

  Iso-Pushoutα-PushoutPushoutMapₛ : (n : ℕ)
    → Iso (Pushout (pushoutMapₛ n) fst)
           (Pushout (pushoutα> n) fst)
  Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ n) (inl x) = inl x
  Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ n) (inr x) = inr (invEq (finSplit3≃ _ _ _) x)
  Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ n) (push a i) =
    ((λ j → inl (pushoutMapₛ n (secEq  (finSplit3≃ _ _ _) (fst a) (~ j)
                               , Iso.rightInv (IsoSphereSusp n) (snd a) (~ j))))
      ∙ push ((invEq (finSplit3≃ _ _ _)  (fst a))
                , (Iso.inv (IsoSphereSusp n) (snd a)))) i
  Iso.inv (Iso-Pushoutα-PushoutPushoutMapₛ n) (inl x) = inl x
  Iso.inv (Iso-Pushoutα-PushoutPushoutMapₛ n) (inr x) = inr (finSplit3 _ _ _ x)
  Iso.inv (Iso-Pushoutα-PushoutPushoutMapₛ n) (push a i) =
    (push ((finSplit3 _ _ _ (fst a))
          , (Iso.fun (IsoSphereSusp n) (snd a)))) i
  Iso.rightInv (Iso-Pushoutα-PushoutPushoutMapₛ n) (inl x) = refl
  Iso.rightInv (Iso-Pushoutα-PushoutPushoutMapₛ n) (inr x) i =
    inr (retEq (finSplit3≃ _ _ _) x i)
  Iso.rightInv (Iso-Pushoutα-PushoutPushoutMapₛ n) (push a i) j = {!!}
  Iso.leftInv (Iso-Pushoutα-PushoutPushoutMapₛ n) x = {!!}
  {- pushoutIso _ _ _ _
    (Σ-cong-equiv (invEquiv (finSplit3≃ _ _ _))
      λ _ → isoToEquiv (invIso (IsoSphereSusp n)))
    (idEquiv _)
    (invEquiv (finSplit3≃ _ _ _))
    (funExt λ x → cong (pushoutMapₛ n) (ΣPathP
      (sym (secEq (finSplit3≃ _ _ _) (fst x))
      , sym (Iso.rightInv (IsoSphereSusp n) (snd x)))))
    refl
    -}

  pushoutMap : (n : ℕ) → (Fin (pushoutCells n)) × (S⁻ n) → pushoutA n
  pushoutMap zero = pushoutMap₀
  pushoutMap (suc n) = pushoutα> n

  PushoutA→PushoutPushoutMapL : (n : ℕ) → Pushout (α C (suc n)) fst → Pushout (pushoutMapₛ n) fst
  PushoutA→PushoutPushoutMapL n (inl x) = inl (inl x)
  PushoutA→PushoutPushoutMapL n (inr x) = inr ((inl (inl x)))
  PushoutA→PushoutPushoutMapL n (push a i) =
    ((λ i → inl (inl (α C (suc n) (fst a , Iso.leftInv (IsoSphereSusp n) (snd a) (~ i)))))
    ∙ push (((inl (inl (fst a)))) , Iso.fun (IsoSphereSusp n) (snd a))) i

  PushoutA→PushoutPushoutMapR : (n : ℕ) → Pushout (α D (suc n)) fst → Pushout (pushoutMapₛ n) fst
  PushoutA→PushoutPushoutMapR n (inl x) = inl (inr x)
  PushoutA→PushoutPushoutMapR n (inr x) = inr ((inl (inr x)))
  PushoutA→PushoutPushoutMapR n (push a i) =
    ((λ i → inl (inr (α D (suc n) (fst a , Iso.leftInv (IsoSphereSusp n) (snd a) (~ i)))))
    ∙ push (((inl (inr (fst a)))) , Iso.fun (IsoSphereSusp n) (snd a))) i

  PushoutA→PushoutPushoutMapLR : (n : ℕ) (b : Pushout (α B n) fst)
    → Path (Pushout (pushoutMapₛ n) fst)
            (inl (inl (∣ f ∣ (suc n) (invEq (e B n) b))))
            (inl (inr (∣ g ∣ (suc n) (invEq (e B n) b))))
  PushoutA→PushoutPushoutMapLR n (inl x) i = inl (push x i)
  PushoutA→PushoutPushoutMapLR n (inr x) = push ((inr x) , north) ∙∙ refl ∙∙ sym (push ((inr x) , south))
  PushoutA→PushoutPushoutMapLR n (push (t , s) i) j =
    hcomp (λ k → λ {(i = i0) → inl (doubleCompPath-filler (λ i → inl (∣ f ∣ (suc n) (invEq (e B n) (push (t , s) (~ i)))))
                                                           (push (α B n (t , s)))
                                                           (λ i → inr (∣ g ∣ (suc n) (invEq (e B n) (push (t , s) i)))) (~ k) j)
                   ; (i = i1) → doubleCompPath-filler (push ((inr t) , north)) refl (sym (push ((inr t) , south))) k j
                   ; (j = i0) → invSides-filler (push (inr t , north))
                                                 (λ i → inl (inl (∣ f ∣ (suc n) (invEq (e B n) (push (t , s) (~ i)))))) k i
                   ; (j = i1) → invSides-filler (push (inr t , south))
                                                 (λ i → inl (inr (∣ g ∣ (suc n) (invEq (e B n) (push (t , s) (~ i)))))) k i})
          ((push (inr t , merid s j)) i)


  PushoutA→PushoutPushoutMap : (n : ℕ) → (pushoutA (suc (suc n))) → (Pushout (pushoutMapₛ n) fst)
  PushoutA→PushoutPushoutMap n (inl x) = PushoutA→PushoutPushoutMapL n (fst (e C (suc n)) x)
  PushoutA→PushoutPushoutMap n (inr x) = PushoutA→PushoutPushoutMapR n (fst (e D (suc n)) x)
  PushoutA→PushoutPushoutMap n (push a i) =
       (cong (PushoutA→PushoutPushoutMapL n) (cong (fst (e C (suc n))) (sym (comm f (suc n) a))
                    ∙ secEq (e C (suc n)) (inl (∣ f ∣ (suc n) a)))
    ∙∙ (λ i → ((λ i → inl (inl (∣ f ∣ (suc n) (retEq (e B n) a (~ i)))))
    ∙∙ PushoutA→PushoutPushoutMapLR n (fst (e B n) a)
    ∙∙ λ i → inl (inr (∣ g ∣ (suc n) (retEq (e B n) a i)))) i)
    ∙∙ cong (PushoutA→PushoutPushoutMapR n) (sym (cong (fst (e D (suc n))) (sym (comm g (suc n) a))
                       ∙ secEq (e D (suc n)) (inl (∣ g ∣ (suc n) a))))) i


module _ {ℓ ℓ' ℓ'' : Level} {B' : CWskel ℓ} {C' : CWskel ℓ'} {D' : CWskel ℓ''}
  (f : cellMap (strictCWskel B') (strictCWskel C'))
  (g : cellMap (strictCWskel B') (strictCWskel D')) where
  private
    B = strictCWskel B'
    C = strictCWskel C'
    D = strictCWskel D'

  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)
  
  PushoutA→PushoutPushoutMapStrict : (n : ℕ)
    → (pushoutA f g (suc (suc n))) → (Pushout (pushoutMapₛ f g n) fst)
  PushoutA→PushoutPushoutMapStrict n (inl x) =
    PushoutA→PushoutPushoutMapL f g n (fst (e C (suc n)) x)
  PushoutA→PushoutPushoutMapStrict n (inr x) =
    PushoutA→PushoutPushoutMapR f g n (fst (e D (suc n)) x)
  PushoutA→PushoutPushoutMapStrict n (push a i) =
      (cong (PushoutA→PushoutPushoutMapL f g n)
        (cong (fst (e C (suc n))) (sym (comm f (suc n) a)))
    ∙∙ PushoutA→PushoutPushoutMapLR f g n (fst (e B n) a)
    ∙∙ cong (PushoutA→PushoutPushoutMapR f g n)
        (sym (cong (fst (e D (suc n))) (sym (comm g (suc n) a))))) i

  PushoutA→PushoutPushoutMapStrict≡ : (n : ℕ) (x : _)
    → PushoutA→PushoutPushoutMapStrict n x ≡ PushoutA→PushoutPushoutMap f g n x
  PushoutA→PushoutPushoutMapStrict≡ n (inl x) = refl
  PushoutA→PushoutPushoutMapStrict≡ n (inr x) = refl
  PushoutA→PushoutPushoutMapStrict≡ n (push a i) j =
    (cong (PushoutA→PushoutPushoutMapL f g n)
          (rUnit (cong (fst (e C (suc n))) (sym (comm f (suc n) a))) j)
    ∙∙ rUnit (PushoutA→PushoutPushoutMapLR f g n (fst (e B n) a)) j
    ∙∙ cong (PushoutA→PushoutPushoutMapR f g n)
        (sym (rUnit ((cong (fst (e D (suc n))) (sym (comm g (suc n) a)))) j))) i

{-

  mapBack : (n : ℕ) → Pushout (pushoutMapₛ f g n) fst → pushoutA f g (suc (suc n))
  mapBack n (inl (inl x)) = inl (inl x)
  mapBack n (inl (inr x)) = inr (inl x)
  mapBack n (inl (push a i)) = ((λ i → inl (comm f (suc n) (inl a) i)) ∙∙ push (inl a) ∙∙ λ i → inr (comm g (suc n) (inl a) (~ i))) i
  mapBack n (inr (inl (inl x))) = inl (inr x)
  mapBack n (inr (inl (inr x))) = inr (inr x)
  mapBack n (inr (inr x)) = inl (inl (∣ f ∣ (suc n) (inr x)))
  mapBack n (push (inl (inl x) , t) i) = inl ((push (x , Iso.inv (IsoSphereSusp n) t )) i)
  mapBack n (push (inl (inr x) , t) i) = inr ((push (x , Iso.inv (IsoSphereSusp n) t )) i)
  mapBack n (push (inr x , north) i) = inl (inl (∣ f ∣ (suc n) (inr x)))
  mapBack n (push (inr x , south) i) =
    ((λ i → inr (comm g (suc n) (inr x) i))
    ∙∙ sym (push (inr x))
    ∙∙ λ i → inl (comm f (suc n) (inr x) (~ i))) i
  mapBack n (push (inr x , merid a i) j) = {!!}
-}

sphereBouquetIso : (n : ℕ) {a b c : ℕ}
  → Iso (SphereBouquet (suc n) (Fin (a + b + c))) (SphereBouquet (suc n) ((Fin a ⊎ Fin b) ⊎ Fin c))
Iso.fun (sphereBouquetIso n) (inl x) = inl x
Iso.fun (sphereBouquetIso n) (inr (x , y)) = inr ((fst (finSplit3≃ _ _ _) x) , y)
Iso.fun (sphereBouquetIso n) (push a i) = push (fst (finSplit3≃ _ _ _) a) i
Iso.inv (sphereBouquetIso n) (inl x) = inl x
Iso.inv (sphereBouquetIso n) (inr (x , y)) = inr ((invEq (finSplit3≃ _ _ _) x) , y)
Iso.inv (sphereBouquetIso n) (push a i) = push (invEq (finSplit3≃ _ _ _) a) i
Iso.rightInv (sphereBouquetIso n) (inl x) = refl
Iso.rightInv (sphereBouquetIso n) (inr (x , y)) i = inr ((secEq (finSplit3≃ _ _ _) x i) , y)
Iso.rightInv (sphereBouquetIso n) (push a i) j = push (secEq (finSplit3≃ _ _ _) a j) i
Iso.leftInv (sphereBouquetIso n) (inl x) = refl
Iso.leftInv (sphereBouquetIso n) (inr (x , y)) i = inr ((retEq (finSplit3≃ _ _ _) x i) , y)
Iso.leftInv (sphereBouquetIso n) (push a i) j = push (retEq (finSplit3≃ _ _ _) a j) i

SplitBouquet : (n : ℕ) (a b c : ℕ) → Type ℓ-zero
SplitBouquet n a b c = (SphereBouquet∙ (suc n) (Fin a) ⋁∙ₗ SphereBouquet∙ (suc n) (Fin b))
                                          ⋁ SphereBouquet∙ (suc n) (Fin c)

module _ (n : ℕ) {a b c : ℕ} where
  sumSphereBouquet→SplitBouquet : (SphereBouquet (suc n) ((Fin a ⊎ Fin b) ⊎ Fin c))
     → SplitBouquet n a b c
  sumSphereBouquet→SplitBouquet (inl x) = inl (inl (inl x))
  sumSphereBouquet→SplitBouquet (inr (inl (inl x) , y)) = inl (inl (inr (x , y)))
  sumSphereBouquet→SplitBouquet (inr (inl (inr x) , y)) = inl (inr (inr (x , y)))
  sumSphereBouquet→SplitBouquet (inr (inr x , y)) = inr (inr (x , y))
  sumSphereBouquet→SplitBouquet (push (inl (inl x)) i) = inl (inl (push x i))
  sumSphereBouquet→SplitBouquet (push (inl (inr x)) i) =
    inl (((λ i → push tt i) ∙ λ i → (inr (push x i))) i)
  sumSphereBouquet→SplitBouquet (push (inr x) i) = (push tt ∙ λ i → inr (push x i)) i

  SplitBouquet→sumSphereBouquet : SplitBouquet n a b c
    → SphereBouquet (suc n) ((Fin a ⊎ Fin b) ⊎ Fin c)
  SplitBouquet→sumSphereBouquet (inl (inl (inl x))) = inl x
  SplitBouquet→sumSphereBouquet (inl (inl (inr (x , y)))) = inr ((inl (inl x)) , y)
  SplitBouquet→sumSphereBouquet (inl (inl (push a i))) = push (inl (inl a)) i
  SplitBouquet→sumSphereBouquet (inl (inr (inl x))) = inl x
  SplitBouquet→sumSphereBouquet (inl (inr (inr (x , y)))) = inr ((inl (inr x)) , y)
  SplitBouquet→sumSphereBouquet (inl (inr (push a i))) = push (inl (inr a)) i
  SplitBouquet→sumSphereBouquet (inl (push a i)) = inl tt
  SplitBouquet→sumSphereBouquet (inr (inl x)) = inl x
  SplitBouquet→sumSphereBouquet (inr (inr (x , y))) = inr (inr x , y)
  SplitBouquet→sumSphereBouquet (inr (push a i)) = push (inr a) i
  SplitBouquet→sumSphereBouquet (push a i) = inl tt

  Iso-sumSphereBouquet-SplitBouquet : Iso (SphereBouquet (suc n) ((Fin a ⊎ Fin b) ⊎ Fin c))
                                          (SplitBouquet n a b c)
  Iso.fun Iso-sumSphereBouquet-SplitBouquet = sumSphereBouquet→SplitBouquet
  Iso.inv Iso-sumSphereBouquet-SplitBouquet = SplitBouquet→sumSphereBouquet
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inl (inl x))) = refl
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inl (inr x))) = refl
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inl (push a i))) = refl
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inr (inl x))) i = inl (push tt i)
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inr (inr x))) = refl
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inr (push a i))) j =
    inl (compPath-filler' (push tt) (λ i → inr (push a i)) (~ j) i)
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (push a i)) j = inl (push tt (i ∧ j))
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inr (inl x)) = push tt
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inr (inr x)) = refl
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inr (push a i)) j =
    compPath-filler' (push tt) (λ i → inr (push a i)) (~ j) i
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (push a i) j = push tt (i ∧ j)
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inl x) = refl
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inr (inl (inl x) , y)) = refl
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inr (inl (inr x) , y)) = refl
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inr (inr x , y)) = refl
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (push (inl (inl x)) i) = refl
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (push (inl (inr x)) i) j =
    SplitBouquet→sumSphereBouquet (inl (lUnit (λ i → inr (push x i)) (~ j) i))
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (push (inr x) i) j =
    SplitBouquet→sumSphereBouquet (compPath-filler' (push tt) (λ i → inr (push x i)) (~ j) i)


open import Cubical.Data.Nat.Order.Inductive
Pushout→Bouquet-pre∂ : ∀ {ℓ} (B : CWskel ℓ) (n : ℕ)
  → Fin (CWskel-fields.card B (suc n)) × S₊ n
  → SphereBouquet n (Fin (CWskel-fields.card B n))
Pushout→Bouquet-pre∂ B n x =
  (Pushout→Bouquet n (CWskel-fields.card B n)
        (CWskel-fields.α B n) (CWskel-fields.e B n)
          (fst (CWskel-fields.e B n) (CWskel-fields.α B (suc n) x)))

-- module _ where
--   open FinSequenceMap renaming (fmap to ∣_∣)
--   open CWskel-fields
--   preFunctImproved : ∀ {ℓ ℓ'} {C : CWskel ℓ} {D : CWskel ℓ'}
--     (m : ℕ) (f : finCellMap m C D) (n' : Fin m)
--     → SphereBouquet (fst n')
--         (Fin (CWskel-fields.card C (fst n')))
--     → SphereBouquet (fst n')
--         (Fin (CWskel-fields.card D (fst n')))
--   preFunctImproved m f n' (inl x) = inl tt
--   preFunctImproved {C = C} {D} (suc n) f (zero , p) (inr (x , w)) =
--     inr ((fst (CW₁-discrete D) (∣ f ∣ fone (invEq (e C 0) (inr x)))) , w)
--   preFunctImproved n f (suc zero , p) (inr (x , base)) = inl tt
--   preFunctImproved {C = C} {D = D} (suc (suc n)) f (suc zero , p) (inr (x , loop i)) =
--      (cong G (push (∣ f ∣ (1 , p) (α C 1 (x , false)))
--            ∙ (λ i → inr (fcomm f (1 , p) (α C 1 (x , false)) i)))
--     ∙∙ cong (G ∘ inr ∘ ∣ f ∣ (fsuc (1 , tt)) ∘ invEq (e C 1)) (push (x , false))
--       ∙ cong (G ∘ inr ∘ ∣ f ∣ (fsuc (1 , tt)) ∘ invEq (e C 1)) (sym (push (x , true)))
--     ∙∙ sym (cong G (push (∣ f ∣ (1 , p) (α C 1 (x , true)))
--            ∙ (λ i → inr (fcomm f (1 , p) (α C 1 (x , true)) i))))) i
--     where
--     G = BouquetFuns.CTB 1 (D .snd .fst 1) (D .snd .snd .fst 1)
--           (D .snd .snd .snd .snd 1)
--   preFunctImproved n f (suc (suc s) , p) (inr (x , north)) = inl tt
--   preFunctImproved n f (suc (suc s) , p) (inr (x , south)) = inl tt
--   preFunctImproved {C = C} {D = D} (suc n') f (suc (suc n) , p) (inr (x , merid a i)) =
--     (cong G ((push (∣ f ∣ (suc (suc n) , <ᵗ-trans-suc p) (α C (suc (suc n)) (x , a)))
--             ∙ λ i → inr (fcomm f (suc (suc n) , p) (α C (suc (suc n)) (x , a)) i)))
--     ∙ cong G (λ j → inr (∣ f ∣ (fsuc (suc (suc n) , p))
--                       (invEq (e C (suc (suc n))) (push (x , a) j))))
--     ∙ {!!}) i
--     where
--     G = BouquetFuns.CTB (suc (suc n)) (D .snd .fst (suc (suc n))) (D .snd .snd .fst (suc (suc n)))
--           (D .snd .snd .snd .snd (suc (suc n)))
--   preFunctImproved {C = C} {D = D} (suc m) f (zero , p) (push a i) =
--     push (fst (CW₁-discrete D) (∣ f ∣ fone (invEq (e C 0) (inr a)))) i
--   preFunctImproved m f (suc zero , p) (push a i) = inl tt
--   preFunctImproved m f (suc (suc s) , p) (push a i) = inl tt

pre∂Improved : ∀ {ℓ} (B : CWskel ℓ) (n : ℕ)
      → SphereBouquet (suc n) (Fin (preboundary.An+1 (strictCWskel B) n))
      → SphereBouquet (suc n) (Fin (preboundary.An (strictCWskel B) n))
pre∂Improved B n (inl x) = inl tt
pre∂Improved B zero (inr (x , base)) = inl tt
pre∂Improved B zero (inr (x , loop i)) =
  (cong (Iso.fun sphereBouquetSuspIso₀)
    (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B zero)) (λ _ → S₊∙ zero)
      (Pushout→Bouquet-pre∂ B zero (x , false)))
  ∙ sym (cong (Iso.fun sphereBouquetSuspIso₀)
    (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B zero)) (λ _ → S₊∙ zero)
      (Pushout→Bouquet-pre∂ B zero (x , true))))) i
pre∂Improved B (suc n) (inr (x , north)) = inl tt
pre∂Improved B (suc n) (inr (x , south)) = inl tt
pre∂Improved B (suc n) (inr (x , merid a i)) =
    Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n))) (λ _ → S₊∙ (suc n))
      (Pushout→Bouquet-pre∂ B (suc n) (x , a)) i
pre∂Improved B zero (push a i) = inl tt
pre∂Improved B (suc n) (push a i) = inl tt

pre∂Improved≡ : ∀ {ℓ} (B : CWskel ℓ) (n : ℕ)
  (x : SphereBouquet (suc n) (Fin (preboundary.An+1 B n)))
  → preboundary.pre∂ B n x ≡ pre∂Improved B n x
pre∂Improved≡ B zero (inl x) = refl
pre∂Improved≡ B (suc n) (inl x) = refl
pre∂Improved≡ B zero (inr (x , base)) = refl
pre∂Improved≡ B zero (inr (x , loop i)) j =
  hcomp (λ k →
    λ {(i = i0) → Iso.fun sphereBouquetSuspIso₀ (w (push (preboundary.αn+1 B 0 (x , false)) (~ k ∧ ~ j)))
     ; (i = i1) → Iso.fun sphereBouquetSuspIso₀ (w (push (preboundary.αn+1 B 0 (x , true)) (~ k)))
     ; (j = i0) → Iso.fun sphereBouquetSuspIso₀
                   (w (doubleCompPath-filler
                     (push (preboundary.αn+1 B 0 (x , false)))
                     (λ i → inr (invEq (CWskel-fields.e B (suc zero))
                       ((push (x , false) ∙ sym (push (x , true))) i)))
                     (sym (push (preboundary.αn+1 B 0 (x , true)))) k i))})
        (Iso.fun sphereBouquetSuspIso₀ (w (push (preboundary.αn+1 B 0 (x , false)) (~ j ∨ i))))
  where
  w = (SuspBouquet→Bouquet (Fin (preboundary.An B 0)) (λ _ → S₊∙ zero))
       ∘ (suspFun (preboundary.isoCofBouquet B 0))
       ∘  (suspFun (to 0 cofibCW B))
       ∘ (δ-pre (CW↪ B 1))

pre∂Improved≡ B (suc n) (inr (x , north)) = refl
pre∂Improved≡ B (suc n) (inr (x , south)) =
   (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
      (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , ptSn (suc n))))
pre∂Improved≡ B (suc n) (inr (x , merid a i)) j = h j i
  where
  open preboundary B (suc n)
  h : Square (λ i → preboundary.pre∂ B (suc n) (inr (x , merid a i)))
             (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
                (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , a)))
             refl ((Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
      (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , ptSn (suc n)))))
  h = cong-∙∙ (SuspBouquet→Bouquet (Fin An) (λ _ → S₊∙ (suc n))
            ∘ suspFun isoCofBouquet
            ∘ suspFun (to suc n cofibCW B)
            ∘ δ-pre (CW↪ B (suc (suc n))))
            (push (αn+1 (x , a))) _ (sym (push (αn+1 (x , ptSn (suc n)))))
    ∙ doubleCompPath≡compPath _ _ _ -- 
    ∙ cong₂ _∙_ refl ((sym (lUnit _))) -- cong₂ _∙_ refl (sym (lUnit _)) ∙ refl
    ◁ symP (compPath-filler (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
                         (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , a)))
                        (sym (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
                         (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , ptSn (suc n))))))
pre∂Improved≡ B zero (push a i) = refl
pre∂Improved≡ B (suc n) (push a i) = refl

module _ (isEquivPushoutA→PushoutPushoutMapStrict : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''} (f : cellMap (strictCWskel B) (strictCWskel C)) (g : cellMap (strictCWskel B) (strictCWskel D))
            → (n : ℕ) → isEquiv (PushoutA→PushoutPushoutMapStrict f g n)) where

  isEquivPushoutA→PushoutPushoutMap : ∀ {ℓ ℓ' ℓ''} (B : CWskel ℓ) (C : CWskel ℓ') (D : CWskel ℓ'')
    (f : cellMap B C) (g : cellMap B D) (n : ℕ)
    → isEquiv (PushoutA→PushoutPushoutMap f g n)
  isEquivPushoutA→PushoutPushoutMap = elim3StrictCW λ B C D f g n
    → subst isEquiv (funExt (PushoutA→PushoutPushoutMapStrict≡ f g n))
            (isEquivPushoutA→PushoutPushoutMapStrict f g n)

  PushoutCWSkel : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
    (f : cellMap B C) (g : cellMap B D) → CWskel _
  fst (PushoutCWSkel f g) = pushoutA f g
  fst (snd (PushoutCWSkel f g)) = pushoutCells f g
  fst (snd (snd (PushoutCWSkel f g))) = pushoutMap f g
  fst (snd (snd (snd ((PushoutCWSkel {B = B}) f g)))) (lift t) =
    fst (snd (snd (snd B))) t
  snd (snd (snd (snd (PushoutCWSkel {B = B} {C = C} {D} f g)))) zero =
    compEquiv (compEquiv (symPushout _ _)
      (compEquiv (invEquiv (pushoutEquiv _ _ _ _
        (propBiimpl→Equiv (λ())
          (λ x → ⊥.rec (fst (snd (snd (snd B))) x)) (λ()) (fst (snd (snd (snd B)))))
        (idEquiv _) (idEquiv _) (funExt λ()) (funExt λ())))
        (compEquiv (invEquiv (isoToEquiv Pushout-⊎-Iso))
        (compEquiv
          (compEquiv (invEquiv ⊎-IdR-⊥-≃)
            (isoToEquiv (⊎Iso (compIso (compIso
              (⊎Iso (equivToIso (CW₁-discrete D))
                (equivToIso (CW₁-discrete C))) ⊎-swap-Iso)
                  (Iso-Fin⊎Fin-Fin+))
                    (iso (λ()) (λ()) (λ()) λ()))))
          (isoToEquiv (Iso-Fin⊎Fin-Fin+ {m = zero}))))))
      (compEquiv (isoToEquiv (PushoutEmptyFam (λ())
        λ {(lift t) → fst (snd (snd (snd B))) t}))
        (symPushout _ _))
  snd (snd (snd (snd (PushoutCWSkel f g)))) (suc n) =
    compEquiv (PushoutA→PushoutPushoutMap f g n
             , isEquivPushoutA→PushoutPushoutMap _ _ _ f g n)
              (isoToEquiv (Iso-Pushoutα-PushoutPushoutMapₛ  f g n))



  open import Cubical.Data.Unit
  UnitCWskel : CWskel ℓ-zero
  fst UnitCWskel zero = ⊥
  fst UnitCWskel (suc n) = Unit
  fst (snd UnitCWskel) zero = 1
  fst (snd UnitCWskel) (suc n) = 0
  fst (snd (snd UnitCWskel)) zero ()
  fst (snd (snd UnitCWskel)) (suc n) t = tt
  fst (snd (snd (snd UnitCWskel))) ()
  snd (snd (snd (snd UnitCWskel))) zero =
    compEquiv (isoToEquiv Iso-Unit-Fin1)
      (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _))
  snd (snd (snd (snd UnitCWskel))) (suc n) =
    isoToEquiv (PushoutEmptyFam (λ()) λ())


  terminalCW : ∀ {ℓ} {C : CWskel ℓ} → cellMap C UnitCWskel
  SequenceMap.map (terminalCW {C = C}) zero = fst (snd (snd (snd C)))
  SequenceMap.map terminalCW (suc n) _ = tt
  SequenceMap.comm terminalCW _ _ = refl


  module _ {ℓ ℓ' ℓ'' : Level} {B' : CWskel ℓ} {C' : CWskel ℓ'} {D' : CWskel ℓ''}
    (f : cellMap (strictCWskel B') (strictCWskel D')) where
    private
      B = strictCWskel B'
      D = strictCWskel D'
      C = UnitCWskel

    open CWskel-fields
    open SequenceMap renaming (map to ∣_∣)
    open import Cubical.HITs.Wedge
    open import Cubical.Foundations.Pointed

    cofibCWskel : CWskel _
    cofibCWskel = PushoutCWSkel terminalCW f


    PushoutA→PushoutPushoutMap' : (n : ℕ) → pushoutA terminalCW f (suc (suc n))
                       → Pushout (pushoutMapₛ terminalCW f n) (λ r → fst r)
    PushoutA→PushoutPushoutMap' n (inl x) = inl (inl x)
    PushoutA→PushoutPushoutMap' n (inr x) =
      PushoutA→PushoutPushoutMapR terminalCW f n x
    PushoutA→PushoutPushoutMap' n (push a i) =
      (PushoutA→PushoutPushoutMapLR terminalCW f n a
     ∙ cong (PushoutA→PushoutPushoutMapR terminalCW f n) (comm f (suc n) a)) i

    PushoutA→PushoutPushoutMap'≡ : (n : ℕ) (x : _)
      → PushoutA→PushoutPushoutMap terminalCW f n x ≡ PushoutA→PushoutPushoutMap' n x
    PushoutA→PushoutPushoutMap'≡ n (inl x) = refl
    PushoutA→PushoutPushoutMap'≡ n (inr x) = refl
    PushoutA→PushoutPushoutMap'≡ n (push a i) k = help k i
      where
      help : cong (PushoutA→PushoutPushoutMap terminalCW f n) (push a) ≡ cong (PushoutA→PushoutPushoutMap' n) (push a)
      help = cong₃ _∙∙_∙∙_
        (cong (cong (PushoutA→PushoutPushoutMapL terminalCW f n)) (sym (rUnit refl)))
        (sym (rUnit _))
        ((cong (sym ∘ cong (PushoutA→PushoutPushoutMapR terminalCW f n)) (sym (rUnit _))))

    module _ (n : ℕ) where
      F1 = preboundary.isoSuspBouquet cofibCWskel n
      F2↓ = preboundary.isoCofBouquet cofibCWskel n

      F2 = suspFun (preboundary.isoCofBouquet cofibCWskel n)
      F3 = suspFun (to n cofibCW cofibCWskel)
      F4 = δ (suc n) cofibCWskel
      F5 = preboundary.isoCofBouquetInv↑ cofibCWskel n

    SphereBouquetCellIso : (n m : ℕ) → Iso (SphereBouquet (suc n) (Fin (card cofibCWskel m)))
                                             (SplitBouquet n (card C m) (card D m) (pushoutMidCells terminalCW f m))
    SphereBouquetCellIso n m = compIso (sphereBouquetIso n) (Iso-sumSphereBouquet-SplitBouquet n) --  -- 

    sphereBouquetSuspIso∙ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → Iso.fun (sphereBouquetSuspIso {A = A} {n}) north ≡ inl tt
    sphereBouquetSuspIso∙ {n = zero} = refl
    sphereBouquetSuspIso∙ {n = suc n} = refl

    open import Hurewicz.random
    open import Cubical.HITs.SphereBouquet.Degree

    

    ∂L ∂R : (n : ℕ) → SplitBouquet (suc n) (card C (suc (suc n)))
                       (card D (suc (suc n))) (card (strictCWskel B') (suc n))
         → SplitBouquet (suc n) (card C (suc n)) (card D (suc n))
             (card (strictCWskel B') n)
    ∂L n = Iso.fun (SphereBouquetCellIso (suc n) _)
                        ∘ preboundary.pre∂ cofibCWskel (suc n)
                        ∘ Iso.inv (SphereBouquetCellIso (suc n) _)
    ∂R n = ((((λ x → inl (inr x))
                          , (λ i → inl (push tt (~ i))) ∙ push tt)
                           ∘∙ (preboundary.pre∂ D (suc n) , sphereBouquetSuspIso∙))
                           ∘∙ foldR∙)
                       ∨→ SphereBouquet∙Π
                            (((λ x → inl (inr x)) , (λ i → inl (push tt (~ i))) ∙ push tt)
                              ∘∙ (bouquetSusp→ (prefunctoriality.bouquetFunct _ (cellMap→finCellMap (suc (suc n)) f) flast) , refl))
                            (((inr , refl) ∘∙ (bouquetSusp→ (preboundary.pre∂ B n) , refl)))

    ∂L' ∂R' : (n : ℕ) → SplitBouquet (suc n) (card C (suc (suc n)))
                       (card D (suc (suc n))) (card (strictCWskel B') (suc n))
         → SphereBouquet (suc (suc n)) (Fin (card cofibCWskel (suc n)))
    ∂L' n =  preboundary.pre∂ cofibCWskel (suc n)
                        ∘ Iso.inv (SphereBouquetCellIso (suc n) _)
    ∂R' n x = Iso.inv (SphereBouquetCellIso (suc n) _) (∂R n x)



    L1 :  (n : ℕ) (x : _) (a : _)
      → cong (F1 (suc n))
              (merid (preboundary.isoCofBouquet cofibCWskel (suc n)
                (inr (pushoutMapₛ terminalCW f (suc n) ((finSplit3 _ _ _ (invEq (finSplit3≃ _ _ _) x))
            , (Iso.fun (IsoSphereSusp (suc n)) a))))))
      ≡ Bouquet→ΩBouquetSusp (Fin (card D (suc n) + card B n)) (λ _ → S₊∙ (suc n))
              ((preboundary.isoCofBouquet cofibCWskel (suc n)
                (inr (pushoutMapₛ terminalCW f (suc n) (x
            , (Iso.fun (IsoSphereSusp (suc n)) a))))))
    L1 n x a i = cong (F1 (suc n))
              (merid (preboundary.isoCofBouquet cofibCWskel (suc n)
                (inr (pushoutMapₛ terminalCW f (suc n)
               (secEq (finSplit3≃ _ _ _) x i
            , (Iso.fun (IsoSphereSusp (suc n)) a))))))

    congSphereBouquetCellIsoLemma : (n : ℕ) (x : _) → preboundary.isoCofBouquet cofibCWskel (suc n) (inr (inr x))
                   ≡ Iso.inv (SphereBouquetCellIso n (suc n)) (inl (inr
                       (Pushout→Bouquet (suc n)
                         (preboundary.An (strictCWskel D') (suc n))
                         (preboundary.αn (strictCWskel D') (suc n))
                         (idEquiv (fst (strictCWskel D') (suc (suc n)))) x)))
    congSphereBouquetCellIsoLemma n (inl x) = refl
    congSphereBouquetCellIsoLemma n (inr x) = refl
    congSphereBouquetCellIsoLemma n (push a i) j = help j i
      where
      T = Pushout→Bouquet (suc n)
                      (preboundary.An (PushoutCWSkel terminalCW f) (suc n))
                      (preboundary.αn (PushoutCWSkel terminalCW f) (suc n))
                      (compEquiv
                       (PushoutA→PushoutPushoutMap terminalCW f n ,
                        isEquivPushoutA→PushoutPushoutMap (strictCWskel B') UnitCWskel
                        (strictCWskel D') terminalCW f n)
                       (isoToEquiv (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n)))
      help : cong (λ x → preboundary.isoCofBouquet cofibCWskel (suc n) (inr (inr x))) (push a)
           ≡ cong (λ x → Iso.inv (SphereBouquetCellIso n (suc n)) (inl (inr x)))
                  (push (a .fst) ∙ (λ i₁ → inr (a .fst , σSn n (a .snd) i₁)))
      help = (cong-∙ (T ∘ Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n .Iso.fun)
                     _ _)
           ∙ (cong₂ _∙_ (λ _ _ → inl tt)
                        (cong-∙ T _ _
                        ∙ (sym (lUnit _)
                       ∙ cong₂ _∙_ refl
                          λ i → cong (λ x₁ → Iso.inv (SphereBouquetCellIso n (suc n)) (inl (inr x₁)))
                            (λ i₁ → inr (a .fst , σSn n (Iso.leftInv (IsoSphereSusp n) (snd a) i) i₁)))
                        ∙ sym (cong-∙ (λ x → Iso.inv (SphereBouquetCellIso n (suc n)) (inl (inr x))) _ _))
           ∙ sym (lUnit (cong
              (λ x₁ → Iso.inv (SphereBouquetCellIso n (suc n)) (inl (inr x₁)))
              (push (a .fst) ∙ (λ i₁ → inr (a .fst , σSn n (a .snd) i₁))))))


    congSphereBouquetCellIsoLemma2 : (n : ℕ) (x : _)
      → Bouquet→ΩBouquetSusp (Fin (card D (suc n) +ℕ card B n))
              (λ _ → S₊∙ (suc n)) (Iso.inv (SphereBouquetCellIso n (suc n)) (inl (inr x)))
      ≡ cong (λ x → Iso.inv (SphereBouquetCellIso (suc n) (suc n)) (inl (inr x)))
             (Bouquet→ΩBouquetSusp (Fin (preboundary.An D (suc n)))
              (λ _ → S₊∙ (suc n)) x)
    congSphereBouquetCellIsoLemma2 n = ⋁→Homogeneous≡ _ _ (λ _ → isHomogeneousPath _ _)
              refl
              λ {(x , y)
              → sym (cong-∙∙ (λ x₂ → Iso.inv (SphereBouquetCellIso (suc n) (suc n)) (inl (inr x₂))) _ _ _)}

    congSphereBouquetCellIsoLemma3 : (n : ℕ) (x : _)
      → Bouquet→ΩBouquetSusp (Fin (card D (suc n) +ℕ card B n))
              (λ _ → S₊∙ (suc n))
              (Iso.inv (SphereBouquetCellIso n (suc n)) (inr x))
      ≡ cong (λ x → Iso.inv (SphereBouquetCellIso (suc n) (suc n)) (inr x))
             (Bouquet→ΩBouquetSusp (Fin (preboundary.An B n)) (λ _ → S₊∙ (suc n)) x)
    congSphereBouquetCellIsoLemma3 n = ⋁→Homogeneous≡ _ _ (λ _ → isHomogeneousPath _ _)
              refl
              λ {(x , y)
              → sym (cong-∙∙ (λ x₂ → Iso.inv (SphereBouquetCellIso (suc n) (suc n)) (inr x₂)) _ _ _)}

    ∂L'≡∂R'-inr : (n : _) (x : _) (a : _)
      → cong (∂L' n) (λ i → inr (inr (x , (merid a i))))
      ≡ cong (∂R' n) (λ i → inr (inr (x , (merid a i))))
    ∂L'≡∂R'-inr n x a =
         cong-∙∙ (F1 (suc n) ∘ F2 (suc n) ∘ F3 (suc n) ∘ F4 (suc n)) _ _ _
      ∙∙ cong₃ _∙∙_∙∙_ (L1 n (inr x) a) (λ _ _ → inl tt)
                       (cong sym (L1 n (inr x) (ptSn (suc n)) ∙ L1-vanish n x))
      ∙∙ (sym (compPath≡compPath' _ _)
       ∙ sym (rUnit _))
      ∙∙ cong ((Bouquet→ΩBouquetSusp (Fin (card D (suc n) +ℕ card B n))) (λ _ → S₊∙ (suc n)))
              (f1f2lem n x a)
      ∙ Bouquet→ΩBouquetSuspPresStr n (f1 n x) (f2 n x) a
      ∙∙ cong₂ _∙_ ((refl
                   ∙ congSphereBouquetCellIsoLemma2 n _)
                   ∙ rUnit _
                  ∙ cong₃ _∙∙_∙∙_ (sym (cong sym p₁≡)) refl (sym p₁≡)
                  ∙ sym (cong-∙∙ (Iso.inv (SphereBouquetCellIso (suc n) _)) _ _ _))
                   (congSphereBouquetCellIsoLemma3 n _)
      ∙∙ sym (cong-∙ (Iso.inv (SphereBouquetCellIso (suc n) _)) _ _)
      ∙∙ cong (cong (Iso.inv (SphereBouquetCellIso (suc n) _))) (sym r')
      where
      f1 f2 : (n : ℕ) (x : _) → S₊∙ (suc n) →∙ ⋁gen∙ (Fin (card D (suc n) +ℕ card B n)) (λ _ → S₊∙ (suc n))
      fst (f1 n x) a = Iso.inv (SphereBouquetCellIso n (suc n))
        (inl (inr (prefunctoriality.bouquetFunct (suc (suc n))
                   (cellMap→finCellMap (suc (suc n)) f) flast (inr (x , a)))))
      snd (f1 zero x) = refl
      snd (f1 (suc n) x) = refl
      fst (f2 n x) a = Iso.inv (SphereBouquetCellIso n (suc n)) (inr (preboundary.pre∂ B n (inr (x , a))))
      snd (f2 zero x) = refl
      snd (f2 (suc n) x) = refl

      EQ : (n : ℕ) → _ ≃ _
      EQ n = (compEquiv
                         (PushoutA→PushoutPushoutMap terminalCW f n ,
                          isEquivPushoutA→PushoutPushoutMap (strictCWskel B') UnitCWskel
                          (strictCWskel D') terminalCW f n)
                         (isoToEquiv (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n)))

      PB : (n : ℕ) → _
      PB n = Pushout→Bouquet (suc n)
                          (preboundary.An (PushoutCWSkel terminalCW f) (suc n)) 
                          (preboundary.αn (PushoutCWSkel terminalCW f) (suc n)) (EQ n)

      compL : (n : _) (x : _) (a : _)
        → cong (λ w → preboundary.isoCofBouquet cofibCWskel (suc n)
                            (inr (pushoutMapₛ terminalCW f (suc n) (inr x , w)))) (merid a)
        ≡ cong (PB n ∘ Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n .Iso.fun)
                 (PushoutA→PushoutPushoutMapLR terminalCW f n (α B (suc n) (x , a)))
       ∙ cong (PB n ∘ Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n .Iso.fun)
              (cong (PushoutA→PushoutPushoutMapR terminalCW f n)
                        (comm f (suc n) (α B (suc n) (x , a))
                       ∙ cong (∣ f ∣ (suc (suc n))) (push (x , a))))
      compL n x a =
                  cong (cong (PB n))
                        (cong (cong (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n .Iso.fun))
                          λ j i → PushoutA→PushoutPushoutMap'≡  n
                                    (pushoutMapₛ terminalCW f (suc n) (inr x , merid a i)) j )
                ∙ cong-∙ (PB n
                         ∘ Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n .Iso.fun
                         ∘ PushoutA→PushoutPushoutMap' n) _ _
                ∙ cong₂ _∙_ (cong-∙ (PB n ∘ Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n .Iso.fun) _ _
                            ∙ refl)
                            refl
                ∙ sym (assoc _ _ _)
                ∙ cong₂ _∙_ refl
                  (sym (cong-∙ (PB n
                       ∘ Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n .Iso.fun
                       ∘ PushoutA→PushoutPushoutMapR terminalCW f n)
                        ((comm f (suc n) (α B (suc n) (x , a))))
                        (cong (∣ f ∣ (suc (suc n))) (push (x , a))))
                  ∙ refl)

      CTB' : (n : ℕ) → _
      CTB' n = BouquetFuns.CTB (suc n)
                (card (strictCWskel D') (suc n))
                (α (strictCWskel D') (suc n))
                (idEquiv _)

      f1f2lemPre : (n : _) (x : _) (a : _)
        → preboundary.isoCofBouquet cofibCWskel (suc n)
             (inr
              (pushoutMapₛ terminalCW f (suc n)
               (inr x , a)))
         ≡ ∙Π (f1 n x) (f2 n x) .fst (Iso.inv (IsoSucSphereSusp n) a)
      f1f2lemPre n x = λ { north → L n x ; south → R n x
                       ; (merid a i) j → LR n x a j i}
        where
        L : (n : ℕ) (x : _) → inl tt ≡ ∙Π (f1 n x) (f2 n x) .fst (Iso.inv (IsoSucSphereSusp n) north)
        L zero x = refl
        L (suc n) x = refl

        Rr :  (n : ℕ) (x : _) → ∙Π (f1 n x) (f2 n x) .fst (Iso.inv (IsoSucSphereSusp n) south) ≡ inl tt
        Rr zero x = refl
        Rr (suc n) x = refl

        R : (n : ℕ) (x : _) → preboundary.isoCofBouquet cofibCWskel (suc n)
                                 (inr (inr (∣ f ∣ (suc (suc n)) (inr x))))
                            ≡ ∙Π (f1 n x) (f2 n x) .fst (Iso.inv (IsoSucSphereSusp n) south)
        R n x = cong (λ x → preboundary.isoCofBouquet cofibCWskel (suc n) (inr (inr x)))
            (cong (∣ f ∣ (suc (suc n))) (sym (push (x , ptSn n)))
            ∙ sym (comm f (suc n) (α B (suc n) (x , ptSn n))))
           ∙ sym (Rr n x)

        LRmain : (n : ℕ) (x : _) (a : _)
          → Square (cong (PB n ∘ Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n)
                                ∘ PushoutA→PushoutPushoutMap terminalCW f n)
                                  (push (α (strictCWskel B') (suc n) (x , a)))
                  ∙ cong (PB n ∘ Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n)
                                ∘ PushoutA→PushoutPushoutMap terminalCW f n)
                          λ i → inr (∣ f ∣ (suc (suc n)) ((push (x , a) i))))
                    (cong (∙Π (f1 n x) (f2 n x) .fst
                         ∘ Iso.inv (IsoSucSphereSusp n)) (merid a))
                    (L n x) (R n x)
        LRmain zero x a = {!!}
        LRmain (suc n) x a = {!cong (PB (suc n) ∘ Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n))
                                ∘ PushoutA→PushoutPushoutMap terminalCW f (suc n))
                                  (push (α (strictCWskel B') (suc (suc n)) (x , a))) i1!}
          ▷ cong₂ _∙_
            (((rUnit _ ∙ cong₂ _∙_ (λ _ → cong (f1 (suc n) x .fst) (merid a))
                    (sym ((λ i j → Iso.inv (SphereBouquetCellIso (suc n) (suc (suc n)))
                                     (inl (inr (T2 i (~ j))))))))
            ∙ sym (cong-∙ (f1 (suc n) x .fst) (merid a) (sym (merid (ptSn (suc n))))))
            ∙ rUnit _)
            ((rUnit _ ∙ cong₂ _∙_ (λ _ → cong (f2 (suc n) x .fst) (merid a))
                    (sym (cong-∙∙ W _ _ _
                       ∙ cong₃ _∙∙_∙∙_ refl
                         (cong sym (cong-∙ (λ x → W (inr x)) (push (x , ptSn (suc n)))
                           (sym (push (x , ptSn (suc n)))) ∙ rCancel _)) refl
                       ∙ ∙∙lCancel _))
            ∙ sym (cong-∙ (f2 (suc n) x .fst) (merid a) (sym (merid (ptSn (suc n))))))
            ∙ rUnit _)
          where
          P1 : cong
                (PB (suc n) ∘ Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n)) ∘
                 PushoutA→PushoutPushoutMap terminalCW f (suc n))
                (push (α (strictCWskel B') (suc (suc n)) (x , a)))
                ≡ (refl ∙∙ (λ i → f1 (suc n) x .fst (merid a i)) ∙∙ {!!})
          P1 = {!!}

          W = Iso.inv (SphereBouquetCellIso (suc n) (suc (suc n)))
              ∘ inr ∘ SuspBouquet→Bouquet (Fin (preboundary.An B (suc n)))
                 (λ _ → S₊∙ (suc n))
                ∘ (suspFun (preboundary.isoCofBouquet B (suc n)))
                ∘ (suspFun (to suc n cofibCW B))
                ∘ (δ-pre (CW↪ B (suc (suc n))))
          T2 : cong (λ a → prefunctoriality.bouquetFunct (suc (suc (suc n)))
                 (cellMap→finCellMap (suc (suc (suc n))) f) flast (inr (x , a)))
                   (merid (ptSn (suc n)))
             ≡ refl
          T2 = cong-∙∙ (CTB' (suc n) ∘ prefunctoriality.fn+1/fn _ (cellMap→finCellMap (suc (suc (suc n))) f) flast) _ _ _
             ∙ cong₃ _∙∙_∙∙_ refl
                  (cong-∙ (λ x → (CTB' (suc n) (prefunctoriality.fn+1/fn _
                                   (cellMap→finCellMap (suc (suc (suc n))) f) flast (inr x)))) _ _
                                ∙ rCancel _) refl
             ∙ ∙∙lCancel _


        LR : (n : ℕ) (x : _) (a : _)
          → Square (λ i → preboundary.isoCofBouquet cofibCWskel (suc n)
                             (inr (pushoutMapₛ terminalCW f (suc n) (inr x , merid a i))))
                    (cong (∙Π (f1 n x) (f2 n x) .fst
                         ∘ Iso.inv (IsoSucSphereSusp n)) (merid a))
                    (L n x) (R n x)
        LR n x a =
         --  (((λ j i → PB n (Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n)
         --             (PushoutA→PushoutPushoutMap'≡ n
         --               (pushoutMapₛ terminalCW f (suc n) (inr x , merid a i)) j))))
         -- ∙
           cong-∙ (PB n ∘ Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f n)
                        ∘ PushoutA→PushoutPushoutMap terminalCW f n) _ _
         ◁ (LRmain n x a)

      f1f2lem : (n : _) (x : _) (a : _) → preboundary.isoCofBouquet cofibCWskel (suc n)
                                             (inr
                                              (pushoutMapₛ terminalCW f (suc n)
                                               (inr x , Iso.fun (IsoSucSphereSusp n) a)))
                                             ≡ ∙Π (f1 n x) (f2 n x) .fst a
      f1f2lem n x a = {!!}

      L1-vanish : (n : ℕ) (x : _) → L1 n (inr x) (ptSn (suc n)) i1 ≡ refl
      L1-vanish zero x = refl
      L1-vanish (suc n) x = refl
      bouquetSusp→merid-pt : ∀ {ℓ} {A B : Type ℓ} (n : ℕ) (a : A) 
        (f : SphereBouquet (suc n) A → SphereBouquet (suc n) B)
        (fp : f (inl tt) ≡ inl tt)
        → cong (bouquetSusp→ f) (λ i → inr (a , merid (ptSn (suc n)) i))
        ≡ refl
      bouquetSusp→merid-pt {B = B} n a f fp =
        cong (Bouquet→ΩBouquetSusp B (λ _ → S₊∙ (suc n))) (cong f (sym (push a)) ∙ fp)
        ∙ refl

      p₁ : Path (SplitBouquet (suc n) (card C (suc n)) (card D (suc n)) (card (strictCWskel B') n)) _ _
      p₁ =  (λ i → inl (push tt (~ i))) ∙ push tt

      p₁≡ : cong (Iso.inv (SphereBouquetCellIso (suc n) (suc n))) p₁ ≡ refl
      p₁≡ = cong-∙ (Iso.inv (SphereBouquetCellIso (suc n) (suc n))) (λ i → inl (push tt (~ i))) _ ∙ sym (lUnit _) ∙ refl
      r' : cong (∂R n) (λ i → inr (inr (x , (merid a i))))
        ≡ (sym p₁
        ∙∙ (λ i → inl (inr (bouquetSusp→
            (prefunctoriality.bouquetFunct (suc (suc n))
             (cellMap→finCellMap (suc (suc n)) f) flast)
               (inr (x , merid a i)))))
         ∙∙ p₁)
        ∙ λ i → inr (bouquetSusp→ (preboundary.pre∂ B n) (inr (x , merid a i)))
      r' = cong₂ _∙_ (cong₃ _∙∙_∙∙_ (cong sym (sym (lUnit _) ∙ sym (lUnit p₁) ∙ refl))
                     (cong-∙ (λ w → inl (inr
                                      (bouquetSusp→
                                       (prefunctoriality.bouquetFunct (suc (suc n))
                                        (cellMap→finCellMap (suc (suc n)) f) flast)
                                       (inr (x , w))))) (merid a) (sym (merid (ptSn (suc n))))
                   ∙ cong₂ _∙_ refl
                     (cong sym
                       λ i j → inl (inr (bouquetSusp→merid-pt n x
                        (prefunctoriality.bouquetFunct (suc (suc n))
                          (cellMap→finCellMap (suc (suc n)) f) flast)
                            refl i j)))
                   ∙ sym (rUnit _))
                     (sym (lUnit _) ∙ sym (lUnit p₁) ∙ refl)
                   ∙ refl)
                   (cong₃ _∙∙_∙∙_
                     (cong sym (sym (lUnit _) ∙ sym (rUnit _)
                     ∙ refl))
                     (cong-∙ (λ w → inr (bouquetSusp→ (preboundary.pre∂ B n) (inr (x , w))))
                             (merid a) (sym (merid (ptSn (suc n))))
                   ∙ cong₂ _∙_ refl
                     (cong sym (λ i j → inr (bouquetSusp→merid-pt n x (preboundary.pre∂ B n)
                                             sphereBouquetSuspIso∙ i j) ))
                   ∙ sym (rUnit _))
                     (sym (lUnit _) ∙ sym (rUnit _)
                     ∙ refl)
                 ∙∙ sym (rUnit _)
                 ∙∙ refl)

    ∂L'≡∂R' : (n : _) (x : _) (a : _)
      → cong (∂L' n) (λ i → inl (inr (inr (x , (merid a i)))))
      ≡ cong (∂R' n) (λ i → inl (inr (inr (x , (merid a i)))))
    ∂L'≡∂R' n x a =
      cong-∙∙ (F1 (suc n) ∘ F2 (suc n) ∘ F3 (suc n) ∘ F4 (suc n)) _ _ _
         ∙ cong₃ _∙∙_∙∙_ (L1 n (inl (inr x)) a) (λ _ _ → inl tt)
                         (cong sym (L1 n (inl (inr x)) (ptSn (suc n))))
         ∙ refl
     ∙ (cong₃ _∙∙_∙∙_
                   (cong (Bouquet→ΩBouquetSusp (Fin (card D (suc n) +ℕ card B n)) (λ _ → S₊∙ (suc n)))
                         ((λ i → preboundary.isoCofBouquet cofibCWskel (suc n)
                                    (inr (inr (α (strictCWskel D') (suc (suc n))
                                       (x , Iso.leftInv (IsoSucSphereSusp n) a i)))))
                         ∙ congSphereBouquetCellIsoLemma n _)
                  ∙ congSphereBouquetCellIsoLemma2 n _)
         refl
         (cong sym (cong (Bouquet→ΩBouquetSusp (Fin (card D (suc n) +ℕ card B n)) (λ _ → S₊∙ (suc n)))
                         ((λ i → preboundary.isoCofBouquet cofibCWskel (suc n)
                                    (inr (inr (α (strictCWskel D') (suc (suc n))
                                       (x , Iso.leftInv (IsoSucSphereSusp n) (ptSn (suc n)) i)))))
                         ∙ congSphereBouquetCellIsoLemma n _)
                  ∙ congSphereBouquetCellIsoLemma2 n _))
     ∙ sym (cong-∙∙ (Iso.inv (SphereBouquetCellIso (suc n) _)) _ _ _))
     ∙ cong (cong (Iso.inv (SphereBouquetCellIso (suc n) _)))
            (((sym (cong-∙∙ (λ x → inl (inr (SuspBouquet→Bouquet (Fin (preboundary.An D (suc n)))
                                (λ _ → S₊∙ (suc n))
                                (suspFun (preboundary.isoCofBouquet D (suc n))
                                 (suspFun (to suc n cofibCW D)
                                  (δ-pre (CW↪ D (suc (suc n))) x))))))
                           (push (preboundary.αn+1 D (suc n) (x , a)))
                           (λ i → inr ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) i))
                           (sym (push (preboundary.αn+1 D (suc n) (x , ptSn (suc n)))))))
            ∙ (λ _ i → inl (inr (preboundary.pre∂ D (suc n) (inr (x , merid a i))))))
            ∙ (λ _ → cong (∂R n) (λ i → inl (inr (inr (x , (merid a i)))))))




    charac∂ : (n : ℕ) (x : _)
      → ∂L' n x ≡ ∂R' n x
    charac∂ n (inl (inl (inl tt))) = refl
    charac∂ n (inl (inr (inl tt))) = refl
    charac∂ n (inl (inr (inr (x , north)))) = refl
    charac∂ n (inl (inr (inr (x , south)))) = refl
    charac∂ n (inl (inr (inr (x , merid a i)))) j = ∂L'≡∂R' n x a j i
    charac∂ n (inl (inr (push a i))) = refl
    charac∂ n (inl (push a i)) = refl
    charac∂ n (inr (inl x)) = refl
    charac∂ n (inr (inr (x , north))) = refl
    charac∂ n (inr (inr (x , south))) = refl
    charac∂ n (inr (inr (x , merid a i))) = {!!}
    charac∂ n (inr (push a i)) = refl
    charac∂ n (push tt i) = {!∂R' n (push tt i)!}


  -- module _ {ℓ ℓ' ℓ'' : Level} {B' : CWskel ℓ} {C' : CWskel ℓ'} {D' : CWskel ℓ''}
  --   (f : cellMap (strictCWskel B') (strictCWskel C'))
  --   (g : cellMap (strictCWskel B') (strictCWskel D')) where
  --   private
  --     B = strictCWskel B'
  --     C = strictCWskel C'
  --     D = strictCWskel D'

  --   open CWskel-fields
  --   open SequenceMap renaming (map to ∣_∣)
  --   open import Cubical.HITs.Wedge
  --   open import Cubical.Foundations.Pointed



  --   open import Hurewicz.random
  --   open import Cubical.HITs.SphereBouquet.Degree

  --   SphereBouquetCellIso : (n m : ℕ) → Iso (SphereBouquet (suc n) (Fin (pushoutCells f g m)))
  --                                        (SplitBouquet n (card C m) (card D m) (pushoutMidCells f g m))
  --   SphereBouquetCellIso n m = compIso (sphereBouquetIso n) (Iso-sumSphereBouquet-SplitBouquet n) -- 



  --   projC : {n m : ℕ} → SphereBouquet (suc n) (Fin (pushoutCells f g m))
  --         → SphereBouquet (suc n) (Fin (card C m))
  --   projC {n = n} {m} = (foldL ∘ foldL) ∘ Iso.fun (SphereBouquetCellIso n m)

  --   sphereBouquetSuspIso∙ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → Iso.fun (sphereBouquetSuspIso {A = A} {n}) north ≡ inl tt
  --   sphereBouquetSuspIso∙ {n = zero} = refl
  --   sphereBouquetSuspIso∙ {n = suc n} = refl

  --   bouquetSusp→∙ : (n : ℕ) → bouquetSusp→
  --       (prefunctoriality.bouquetFunct (suc n)
  --        (cellMap→finCellMap (suc n) f) flast)
  --       (snd (SphereBouquet∙ (suc n) (Fin (pushoutMidCells f g (suc n)))))
  --       ≡ inl tt
  --   bouquetSusp→∙ zero = refl
  --   bouquetSusp→∙ (suc n) = refl

  --   Test : (n : ℕ) (x : Fin (preboundary.An+1 (PushoutCWSkel f g) (suc n)))
  --     → fst (S₊∙ (suc (suc n))) → Susp (fst (PushoutCWSkel f g) (suc (suc n)))
  --   Test n x z = δ-pre (CW↪ (PushoutCWSkel f g) (suc (suc n)))
  --     (preBTC (suc (suc n)) (preboundary.An+1 (PushoutCWSkel f g) (suc n))
  --         (preboundary.αn+1 (PushoutCWSkel f g) (suc n))
  --         (snd (PushoutCWSkel f g) .snd .snd .snd (suc (suc n))) x .fst z)

  --   mainFun : (n : ℕ) (x : Fin (card C (suc (suc n))))
  --     → SplitBouquet (suc n) (card C (suc (suc n)))
  --       (card D (suc (suc n))) (card B (suc n)) -- S₊ (suc (suc n))
  --     → SphereBouquet (suc (suc n)) (Fin (preboundary.An (PushoutCWSkel f g) (suc n)))
  --   mainFun n x = (preboundary.pre∂ (PushoutCWSkel f g) (suc n) ∘
  --           Iso.inv (SphereBouquetCellIso (suc n) (suc (suc n))))

  --   pushoutMapₛ-inr∙ : (n : ℕ) (x : _) → (pushoutMapₛ f g) (suc n) (x , north) ≡ inl {!∣ f ∣ (suc (suc n)) (invEq !}
  --   pushoutMapₛ-inr∙ = {!!}

  --   mainFun' :  (n : ℕ) (x : Fin (card C (suc (suc n))))
  --     → S₊ (suc (suc n)) → SphereBouquet (suc (suc n)) (Fin (preboundary.An (PushoutCWSkel f g) (suc n)))
  --   mainFun' n x y = {!!} -- inr (invEq (finSplit3≃ {!!} {!!} {!!}) {!inl (inl x)!} , y)

  --   Test* : (n : ℕ) (x : Fin (preboundary.An+1 (PushoutCWSkel f g) (suc n))) (a : _)
  --     → cong (suspFun (preboundary.isoCofBouquet (PushoutCWSkel f g) (suc n)))
  --         (cong (suspFun (to suc n cofibCW (PushoutCWSkel f g))) (cong (Test n x) (merid a)))
  --      ≡ {!!}
  --   Test* n x a =
  --     cong (cong (suspFun (preboundary.isoCofBouquet (PushoutCWSkel f g) (suc n))))
  --      (cong (cong (suspFun (to suc n cofibCW (PushoutCWSkel f g))))
  --     (cong-∙∙ (δ-pre (CW↪ (PushoutCWSkel f g) (suc (suc n)))) _ _ _
  --               ∙ (λ i → merid (preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , a))
  --                            ∙∙ ( λ j → merid (preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , ptSn (suc n))) (~ j ∨ ~ i))
  --                            ∙∙ λ j → merid (preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , ptSn (suc n))) (~ j ∧ ~ i))
  --               ∙ sym (compPath≡compPath' _ _)
  --               ∙ cong₂ _∙_ refl (cong (sym ∘ merid) (cong ((pushoutMapₛ f g) (suc n)) (ΣPathP (refl
  --                 , sym (cong (Iso.fun (IsoSucSphereSusp n)) (IsoSucSphereSusp∙ n))
  --                   ∙ Iso.rightInv ((IsoSucSphereSusp n)) north)) ∙ refl)))
  --               ∙ cong-∙ (suspFun (to suc n cofibCW (PushoutCWSkel f g)))
  --                   (merid (preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , a)))
  --                   (sym (merid ((pushoutMapₛ f g) (suc n) (Iso.fun (⊎Iso (invIso Iso-Fin⊎Fin-Fin+) idIso)
  --                                                 (Iso.inv Iso-Fin⊎Fin-Fin+ x) , north))))
  --              ∙ refl)
  --     ∙ cong-∙ (suspFun (preboundary.isoCofBouquet (PushoutCWSkel f g) (suc n)))
  --              (merid (inr (preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , a))))
  --              (sym (merid (inr ((pushoutMapₛ f g) (suc n)
  --                                 (Iso.fun (⊎Iso (invIso Iso-Fin⊎Fin-Fin+) idIso)
  --                                  (Iso.inv Iso-Fin⊎Fin-Fin+ x)
  --                                  , north)))))
  --     ∙ cong₂ _∙_ (cong merid
  --         {!Pushout→Bouquet (suc n)
  --           (preboundary.An (PushoutCWSkel f g) (suc n))
  --           (preboundary.αn (PushoutCWSkel f g) (suc n))
  --           (e (PushoutCWSkel f g) (suc n)) !}) -- λ _ → Pushout→Bouquet (suc n) ? ? ? ?)
  --                 {!preboundary.isoCofBouquet (PushoutCWSkel f g) (suc n)
  --       (inr (preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , a)))!}
  --     ∙ {!!}
  --     where
  --     l1 : (a : _) → fst (e (PushoutCWSkel f g) (suc n))
  --               (preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , a))
  --        ≡ {!!} 
  --     l1 = {!!}
  --     FC = Pushout→Bouquet (suc n)
  --           (preboundary.An (PushoutCWSkel f g) (suc n))
  --           (preboundary.αn (PushoutCWSkel f g) (suc n))
  --           (e (PushoutCWSkel f g) (suc n))
  --     -- FC = ?

  --     F = Pushout→Bouquet (suc n)
  --           (preboundary.An (PushoutCWSkel f g) (suc n))
  --           (preboundary.αn (PushoutCWSkel f g) (suc n))
  --           (e (PushoutCWSkel f g) (suc n))
  --     help : (a : _)
  --       → F (fst (e (PushoutCWSkel f g) (suc n))
  --               (preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , a)))
  --       ≡ {!!}
  --     help a = cong F (cong (Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ f g n))
  --                     (sym (PushoutA→PushoutPushoutMapStrict≡ f g n
  --                       (preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , a)))))
  --            ∙ {!(preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , a))!} -- preboundary.αn+1 (PushoutCWSkel f g) (suc n) (x , a) 

  --   altT : (n : ℕ) (x : Fin (preboundary.An+1 (PushoutCWSkel f g) (suc n)))
  --     → fst (S₊∙ (suc (suc n))) → Susp (fst (PushoutCWSkel f g) (suc (suc n)))
  --   altT n x north = {!!}
  --   altT n x south = {!!}
  --   altT n x (merid a i) = {!!}


  --   module _ (n : ℕ) where
  --     F1 = preboundary.isoSuspBouquet (PushoutCWSkel f g) n
  --     F2↓ = preboundary.isoCofBouquet (PushoutCWSkel f g) n

  --     F2 = suspFun (preboundary.isoCofBouquet (PushoutCWSkel f g) n)
  --     F3 = suspFun (to n cofibCW (PushoutCWSkel f g))
  --     F4 = δ (suc n) (PushoutCWSkel f g)
  --     F5 = preboundary.isoCofBouquetInv↑ (PushoutCWSkel f g) n

  --   F2↓' : (n : ℕ) → _
  --   F2↓' n = BouquetFuns.CTB (suc n) (preboundary.An (PushoutCWSkel f g) (suc n))
  --            (preboundary.αn (PushoutCWSkel f g) (suc n))
  --            (compEquiv (PushoutA→PushoutPushoutMapStrict f g n
  --                       , isEquivPushoutA→PushoutPushoutMapStrict f g n)
  --             (isoToEquiv (Iso-Pushoutα-PushoutPushoutMapₛ f g n)))

  --   F2↓≡ : (n : ℕ) → F2↓ (suc n) ≡ {!F2↓' n!} -- F2↓' n
  --   F2↓≡ n = {!BouquetFuns.CTB (suc n) (preboundary.An (PushoutCWSkel f g) (suc n))
  --            (preboundary.αn (PushoutCWSkel f g) (suc n))
  --            (compEquiv (PushoutA→PushoutPushoutMapStrict f g n
  --                       , isEquivPushoutA→PushoutPushoutMapStrict f g n)
  --             (isoToEquiv (Iso-Pushoutα-PushoutPushoutMapₛ f g n)))!}

  --   F6 : (n : ℕ) → _
  --   F6 n = Pushout→Bouquet n
  --                       (preboundary.An (PushoutCWSkel f g) n)
  --                       (preboundary.αn (PushoutCWSkel f g) n)
  --                       (snd (snd (snd (snd (PushoutCWSkel f g)))) n)

  --   charac∂-inr : (n : ℕ) (x : Fin (card B (suc n))) (a : S₊ (suc n))
  --       → cong (F1 (suc n) ∘ F2 (suc n) ∘ F3 (suc n) ∘ F4 (suc n) ∘ F5 (suc n))
  --                           (λ i → inr (invEq (finSplit3≃
  --                              (card C (suc (suc n))) (card D (suc (suc n)))
  --                              (pushoutMidCells f g (suc (suc n)))) (inr x) , merid a i))
  --       ≡ Bouquet→ΩBouquetSusp
  --           (Fin (preboundary.An (PushoutCWSkel f g) (suc n)))
  --           (λ _ → S₊∙ (suc n))
  --           (Pushout→Bouquet (suc n)
  --            (preboundary.An (PushoutCWSkel f g) (suc n))
  --            (preboundary.αn (PushoutCWSkel f g) (suc n))
  --            (snd (snd (snd (snd (PushoutCWSkel f g)))) (suc n))
  --            {!!})
  --   charac∂-inr n x a =
  --        cong-∙∙ (F1 (suc n) ∘ F2 (suc n) ∘ F3 (suc n) ∘ F4 (suc n)) _ _ _
  --     ∙∙ cong₃ _∙∙_∙∙_
  --              (cong (cong (F1 (suc n)))
  --                     (cong merid
  --                       (cong (F6 (suc n))
  --                         ((cong (Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ  f g n))
  --                    ((sym (PushoutA→PushoutPushoutMapStrict≡ f g n
  --                      (pushoutMapₛ f g (suc n)
  --                        (secEq (finSplit3≃ (card C (suc (suc n)))
  --                                 (card D (suc (suc n))) (pushoutMidCells f g (suc (suc n))))
  --                                  (inr x) i0
  --                        , Iso.fun (IsoSphereSusp (suc n)) a)))))
  --                      ∙ cong (Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ f g n)) (cong (PushoutA→PushoutPushoutMapStrict f g n)
  --                          (cong (pushoutMapₛ f g (suc n))
  --                            (ΣPathP (secEq (finSplit3≃ (card C (suc (suc n)))
  --                                 (card D (suc (suc n))) (pushoutMidCells f g (suc (suc n))))
  --                                  (inr x) , refl))))
  --                       ∙ refl))
  --                       ∙ refl))
  --             ∙ refl)
  --              (λ _ _ → inl tt)
  --              ({!!} ∙ (λ _ _ → inl tt))
  --     ∙∙ (sym (compPath≡compPath' _ _)
  --     ∙ (λ i j → rUnit (λ i → F1 (suc n)
  --        (merid
  --         (F6 (suc n)
  --          (Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ f g n)
  --           (PushoutA→PushoutPushoutMapStrict f g n
  --            (pushoutMapₛ f g (suc n)
  --             (inr x , Iso.fun (IsoSucSphereSusp n) a)))))
  --         i)) (~ i) j)
  --     ∙ {!(PushoutA→PushoutPushoutMapStrict f g n
  -- (pushoutMapₛ f g (suc n)
  --  (inr x , Iso.fun (IsoSucSphereSusp n) a)))!}
  --     ∙ {!!})

  --   -- charac∂-inl-inl-inr : (n : ℕ) (x : Fin (card C (suc (suc n)))) (a : S₊ (suc n))
  --   --     → cong (F1 (suc n) ∘ F2 (suc n) ∘ F3 (suc n) ∘ F4 (suc n) ∘ F5 (suc n))
  --   --                         (λ i → inr (invEq (finSplit3≃
  --   --                            (card C (suc (suc n))) (card D (suc (suc n)))
  --   --                            (pushoutMidCells f g (suc (suc n)))) (inl (inl x)) , merid a i))
  --   --     ≡ λ i → Iso.inv (SphereBouquetCellIso (suc n) _)
  --   --               (inl (inl (preboundary.pre∂ C (suc n) (inr (x , merid a i)))))
  --   -- charac∂-inl-inl-inr n x a =
  --   --   cong-∙∙ (F1 (suc n) ∘ F2 (suc n) ∘ F3 (suc n) ∘ F4 (suc n)) _ _ _
  --   --   ∙  cong₃ _∙∙_∙∙_
  --   --            (cong (cong (F1 (suc n)))
  --   --              (cong merid (cong (F6 (suc n))
  --   --                (cong (Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ  f g n))
  --   --                  (sym (PushoutA→PushoutPushoutMapStrict≡ f g n
  --   --                    (pushoutMapₛ f g (suc n)
  --   --                      (secEq (finSplit3≃ (card C (suc (suc n)))
  --   --                               (card D (suc (suc n))) (pushoutMidCells f g (suc (suc n))))
  --   --                                (inl (inl x)) i0
  --   --                      , Iso.fun (IsoSphereSusp (suc n)) a)))
  --   --                ∙ cong (PushoutA→PushoutPushoutMapStrict f g n)
  --   --                        (cong (pushoutMapₛ f g (suc n))
  --   --                          (ΣPathP (secEq (finSplit3≃ (card C (suc (suc n)))
  --   --                               (card D (suc (suc n))) (pushoutMidCells f g (suc (suc n))))
  --   --                                (inl (inl x)) , refl)))
  --   --                      ∙ cong (PushoutA→PushoutPushoutMapL f g n ∘ α (strictCWskel C') (suc (suc n)))
  --   --                             (ΣPathP (refl , Iso.leftInv (IsoSucSphereSusp n) a)))
  --   --                       ∙ cong (Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ f g n))
  --   --                          (refl ∙ refl))
  --   --                       ∙ refl))
  --   --                       ∙ refl)
  --   --            (λ _ _ → inl tt)
  --   --            ({!!} ∙ (λ _ _ → inl tt))
  --   --   ∙ (sym (compPath≡compPath' _ _) ∙ sym (rUnit _))
  --   --   ∙ cong (Bouquet→ΩBouquetSusp (Fin (card (PushoutCWSkel f g) (suc n)))
  --   --            λ _ → S₊∙ (suc n))
  --   --          (λ _ → F6 (suc n)
  --   --        (Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ f g n)
  --   --         (PushoutA→PushoutPushoutMapL f g n
  --   --           (α (strictCWskel C') (suc (suc n)) (x , a)))))
  --   --   {- (λ j i → SuspBouquet→Bouquet
  --   --                {!SuspBouquet→Bouquet (isoToPath (sphereBouquetIso (suc n) {a = card C (suc n)} {b = card D (suc n)} {c = card B n}) i) (λ _ → S₊∙ (suc n)) ?!}
  --   --                (λ _ → S₊∙ (suc n))
  --   --                {! -- (Fin (preboundary.An (PushoutCWSkel f g) (suc n)))!})
  --   --                -}
  --   --   ∙ cong (Bouquet→ΩBouquetSusp (Fin (card (PushoutCWSkel f g) (suc n)))
  --   --           (λ _ → S₊∙ (suc n)))
  --   --           (MAI (α (strictCWskel C') (suc (suc n)) (x , a)))
  --   --   ∙ L _
  --   --   ∙ sym (sym (compPath≡compPath' _ _) ∙ sym (rUnit _))
  --   --   ∙ cong₃ _∙∙_∙∙_ refl (λ _ _ → inl tt) ((λ _ _ → inl tt) ∙ {!preboundary.pre∂ (PushoutCWSkel f g) n!})
  --   --   ∙ sym (cong-∙∙ H _ _ _)
  --   --   where
  --   --   MAI : (x : _)
  --   --     → F6 (suc n)
  --   --           (Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ f g n)
  --   --            (PushoutA→PushoutPushoutMapL f g n x)) ≡ Iso.inv (SphereBouquetCellIso n (suc n))
  --   --           (inl
  --   --            (inl
  --   --             (Pushout→Bouquet (suc n) (preboundary.An (strictCWskel C') (suc n))
  --   --              (preboundary.αn (strictCWskel C') (suc n))
  --   --              (idEquiv (Pushout (strictifyFamα C' (suc n)) (λ r → fst r))) x)))
  --   --   MAI (inl x) = refl
  --   --   MAI (inr x) = refl
  --   --   MAI (push a i) j = sick j i
  --   --     where
  --   --     sick : cong (F6 (suc n) ∘ Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ f g n))
  --   --                 ((λ i → inl (inl (α (strictCWskel C') (suc n) (fst a , Iso.leftInv (IsoSphereSusp n) (snd a) (~ i)))))
  --   --                 ∙ push (inl (inl (fst a)) , Iso.fun (IsoSphereSusp n) (snd a)) )
  --   --        ≡ cong (Iso.inv (SphereBouquetCellIso n (suc n)))
  --   --               (λ j → inl (inl ((push (a .fst) ∙ (λ i₁ → inr (a .fst , σSn n (a .snd) i₁))) j)))
  --   --     sick = cong-∙ (F6 (suc n) ∘ Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ f g n))
  --   --                   (λ i → inl (inl (α (strictCWskel C') (suc n)
  --   --                               (fst a , Iso.leftInv (IsoSphereSusp n) (snd a) (~ i)))))
  --   --                   ( push (inl (inl (fst a)) , Iso.fun (IsoSphereSusp n) (snd a)))
  --   --          ∙ sym (lUnit _)
  --   --          ∙ cong-∙ (F6 (suc n))
  --   --              (λ i → (inl (pushoutMapₛ f g n (secEq
  --   --                       (finSplit3≃ (card (strictCWskel C') (suc n))
  --   --                        (card (strictCWskel D') (suc n)) (card (strictCWskel B') n))
  --   --                       (inl (inl (fst a))) (~ i)
  --   --                   , Iso.rightInv (IsoSphereSusp n) (Iso.fun (IsoSphereSusp n) (snd a)) (~ i)))))
  --   --              (push (invEq (finSplit3≃ (card (strictCWskel C') (suc n))
  --   --                     (card (strictCWskel D') (suc n))
  --   --                     (card (strictCWskel B') n)) (inl (inl (fst a)))
  --   --             , Iso.inv (IsoSphereSusp n) (Iso.fun (IsoSphereSusp n) (snd a))))
  --   --          ∙ sym (lUnit _) -- cong (cong (F6 (suc n)) ∘ push) (λ i → invEq (finSplit3≃ _ _ _) (inl (inl (fst a))) , Iso.leftInv (IsoSphereSusp n) (snd a) i)
  --   --          ∙ (cong (cong (F6 (suc n)) ∘ push) (ΣPathP (refl , Iso.leftInv (IsoSphereSusp n) (snd a)))
  --   --          ∙ cong₂ _∙_ refl refl)
  --   --          ∙ sym (cong-∙ (λ x → Iso.inv (SphereBouquetCellIso n (suc n)) (inl (inl x))) (push (fst a))
  --   --                (λ i₁ → inr (a .fst , σSn n (a .snd) i₁)))

  --   --   L : (x : _) → Bouquet→ΩBouquetSusp (Fin (card (PushoutCWSkel f g) (suc n)))
  --   --                   (λ _ → S₊∙ (suc n)) (Iso.inv (SphereBouquetCellIso n (suc n)) (inl (inl x)))
  --   --               ≡ cong (Iso.inv (SphereBouquetCellIso (suc n) (suc n)))
  --   --                      λ j → inl (inl (Bouquet→ΩBouquetSusp (Fin (card C (suc n))) (λ _ → S₊∙ (suc n)) x j))
  --   --   L (inl x) = refl
  --   --   L (inr x) = {!!}
  --   --   L (push a i) = {!!}

  --   --   H : (x : _) → _
  --   --   H x = Iso.inv (SphereBouquetCellIso (suc n) (suc n))
  --   --            (inl (inl (SuspBouquet→Bouquet (Fin (preboundary.An C (suc n)))
  --   --              (λ _ → S₊∙ (suc n))
  --   --            (suspFun (preboundary.isoCofBouquet C (suc n))
  --   --             (suspFun (to suc n cofibCW C)
  --   --             (δ-pre (CW↪ C (suc (suc n))) x))))))
  --   --   HH : (a : S₊ (suc n)) → SphereBouquet (suc n) (Fin (preboundary.An (PushoutCWSkel f g) (suc n)))
  --   --   HH a = inr ({!sphereBouquetIso -- sphereBouquetIso -- SphereBouquetCellIso (suc n) (suc n) -- α (strictCWskel C') (suc (suc n)) (x , a)!} , a)

  --   -- charac∂' : (n : ℕ) → Iso.fun (SphereBouquetCellIso n _)
  --   --                     ∘ preboundary.pre∂ (PushoutCWSkel f g) n
  --   --                     ∘ Iso.inv (SphereBouquetCellIso n _)
  --   --                 ≡ ((∨→∙ (((λ x → inl (inl x)) , refl)
  --   --                        ∘∙ (preboundary.pre∂ C n , sphereBouquetSuspIso∙))
  --   --                         (((λ x → inl (inr x)) , λ i → inl (push tt (~ i)))
  --   --                      ∘∙ (preboundary.pre∂ D n , sphereBouquetSuspIso∙)))
  --   --                    ∨→ (SphereBouquet∙Π (((λ x → inl (inl x)) , refl)
  --   --                                          ∘∙ (bouquetSusp→ (prefunctoriality.bouquetFunct (suc n)
  --   --                                                        (cellMap→finCellMap (suc n) f) flast) , {!!}))
  --   --                                         {!bouquetSusp→!})) -- _ SphereBouquet∙Π
  --   --                 {- ((∨→∙ (((λ x → inl (inl x)) , refl) ∘∙ (preboundary.pre∂ C n , sphereBouquetSuspIso∙))
  --   --                          ((((λ x → inl (inr x)) , λ i → inl (push tt (~ i)))
  --   --                      ∘∙ (preboundary.pre∂ D n , sphereBouquetSuspIso∙))))
  --   --                     ∨→ {!SphereBouquet∙Π ((bouquetSusp→ (prefunctoriality.bouquetFunct (suc n)
  --   --                                            (cellMap→finCellMap (suc n) f) flast) , bouquetSusp→∙ n))
  --   --                                          ((bouquetSusp→ (prefunctoriality.bouquetFunct (suc n)
  --   --                                            (cellMap→finCellMap (suc n) g) flast) , bouquetSusp→∙ n))!})

  --   --                 -}
  --   -- charac∂' n = {!!}

  --   -- -- charac∂ : (n : ℕ) → Iso.fun (SphereBouquetCellIso n _)
  --   -- --                     ∘ preboundary.pre∂ (PushoutCWSkel f g) n
  --   -- --                     ∘ Iso.inv (SphereBouquetCellIso n _)
  --   -- --                     ≡ ((((λ x → inl (inl x)) , refl)
  --   -- --                     ∘∙ ((preboundary.pre∂ C n , sphereBouquetSuspIso∙) ∘∙ foldL∙))
  --   -- --                     ∨→ ((((λ x → inl (inl x)) , refl))
  --   -- --                       ∘∙ (bouquetSusp→ (prefunctoriality.bouquetFunct (suc n)
  --   -- --                         (cellMap→finCellMap (suc n) f) flast) , bouquetSusp→∙ n)))
  --   -- -- charac∂ zero = {!!}
  --   -- -- charac∂ (suc n) =
  --   -- --   funExt λ { (inl (inl (inl x))) → refl -- refl
  --   -- --            ; (inl (inl (inr (x , north)))) → refl -- refl
  --   -- --            ; (inl (inl (inr (x , south)))) → refl -- refl
  --   -- --            ; (inl (inl (inr (x , merid a i)))) → {!!} -- refl
  --   -- --            {-
  --   -- --            ; (inl (inl (inr (x , south)))) → refl
  --   -- --            ; (inl (inl (inr (x , merid a i)))) j
  --   -- --              → (cong (cong (projC ∘ preboundary.pre∂ (PushoutCWSkel f g) (suc n)))
  --   -- --                      (λ j i → inr (mok x , merid a i))
  --   -- --                   ∙ {!invEq (snd (PushoutCWSkel f g) .snd .snd .snd (suc (suc n))) (push ? i) -- preboundary.isoCofBouquetInv↑ (PushoutCWSkel f g) (suc n) (inr (? , merid a i))!}) j i
  --   -- --                   -}
  --   -- --              {- (cong (cong (projC ∘ preboundary.pre∂ (PushoutCWSkel f g) (suc n)))
  --   -- --                      (λ j i → inr ({!!} , merid a i))
  --   -- --                   ∙ {!!}) j i
  --   -- --                   -}
  --   -- --            ; (inl (inl (push a i))) → {!preboundary.isoCofBouquet (PushoutCWSkel f g) (suc n) (inr ?)!}
  --   -- --             ; (inl (inr x)) → {!x!}
  --   -- --             ; (inl (push a i)) → {!!}
  --   -- --             ; (inr (inl x)) → {!!} -- refl
  --   -- --             ; (inr (inr (x , north))) →  refl -- refl
  --   -- --             ; (inr (inr (x , south))) → refl -- refl
  --   -- --             ; (inr (inr (x , merid a i))) → {!a!}
  --   -- --             ; (inr (push a i)) → {!!} -- _ preBTC
  --   -- --             ; (push a i) → {!!}}
  --   -- --    where
  --   -- --    mok : (x : Fin (card C (suc (suc n)))) → Fin (preboundary.An+1 (PushoutCWSkel f g) (suc n))
  --   -- --    mok x = Iso.fun Iso-Fin⊎Fin-Fin+ (inl (Iso.fun Iso-Fin⊎Fin-Fin+ (inl x)))
