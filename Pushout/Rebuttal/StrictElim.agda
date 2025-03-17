{-# OPTIONS --cubical --lossy-unification #-}
module Pushout.Rebuttal.StrictElim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.CW.Base
open import Cubical.CW.Map

open import Cubical.Data.Empty as ⊥
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

SphereBouquet' : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Type ℓ
SphereBouquet' n A = ⋁gen A λ _ → Susp (S⁻ n) , north

open import Cubical.Foundations.Path
module _ {ℓ} {A : Type ℓ}
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  {a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁}
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  {a₁₋₋ : Square a₁₀₋ a₁₁₋ a₁₋₀ a₁₋₁}
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  {a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁}
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  {a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁}
  {a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀}
  {a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁}
  where
  cubePermute-ijk↦jik : Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁ → Cube a₋₀₋ a₋₁₋ a₀₋₋ a₁₋₋ (flipSquare a₋₋₀) (flipSquare a₋₋₁) 
  cubePermute-ijk↦jik c i j k = c j i k

  cubePermute-ijk↦kji : Cube a₀₋₋ a₁₋₋ a₋₀₋ a₋₁₋ a₋₋₀ a₋₋₁
    → Cube (flipSquare a₋₋₀) (flipSquare a₋₋₁) (flipSquare a₋₀₋) (flipSquare a₋₁₋) (flipSquare a₀₋₋) (flipSquare a₁₋₋)
  cubePermute-ijk↦kji c i j k = c k j i

PushoutRec : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
  {f : A → B} {g : A → C} (inl* : B → D) (inr* : C → D) (comm : (c : A) → inl* (f c) ≡ inr* (g c))
  → Pushout f g → D
PushoutRec inl* inr* comm (inl x) = inl* x
PushoutRec inl* inr* comm (inr x) = inr* x
PushoutRec inl* inr* comm (push a i) = comm a i


open SequenceMap renaming (map to ∣_∣)
open CWskel-fields


-- Strictification of CW skels
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

-- Associated elimination principle
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

-- Strictification of cell maps
module _ {ℓ ℓ'} {C : CWskel ℓ} {D : CWskel ℓ'} (f : cellMap (strictCWskel C) (strictCWskel D)) where

  mutual
    strictMapFun : (n : ℕ) → strictifyFam C n → strictifyFam D n
    strictMapComm : (n : ℕ) (x : strictifyFam C n) →
        strictMapFun n x ≡ ∣ f ∣ n x
    strictMapFun zero x = ∣ f ∣ 0 x
    strictMapFun (suc n) (inl x) = inl (strictMapFun n x)
    strictMapFun (suc n) (inr x) = ∣ f ∣ (suc n) (inr x)
    strictMapFun (suc (suc n)) (push c i) =
      (((λ i → inl (strictMapComm (suc n) (α (strictCWskel C) (suc n) c) i))
          ∙ comm f (suc n) (α (strictCWskel C) (suc n) c))
          ∙ cong (∣ f ∣ (suc (suc n))) (push c)) i
    strictMapComm zero x = refl
    strictMapComm (suc n) (inl x) = (λ i → inl (strictMapComm n x i)) ∙ comm f n x
    strictMapComm (suc n) (inr x) = refl
    strictMapComm (suc (suc n)) (push c i) j =
      compPath-filler' ((λ i → inl (strictMapComm (suc n) (α (strictCWskel C) (suc n) c) i))
          ∙ comm f (suc n) (α (strictCWskel C) (suc n) c))
          (cong (∣ f ∣ (suc (suc n))) (push c)) (~ j) i


  strictCwMap : cellMap (strictCWskel C) (strictCWskel D)
  SequenceMap.map strictCwMap = strictMapFun
  SequenceMap.comm strictCwMap n x = refl

  strictCwMap≡ : strictCwMap ≡ f
  ∣_∣ (strictCwMap≡ i) n x = strictMapComm n x i
  comm (strictCwMap≡ i) n x j =
   compPath-filler ((λ i₁ → inl (strictMapComm n x i₁))) (comm f n x) j i
