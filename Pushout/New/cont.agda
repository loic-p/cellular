{-# OPTIONS --cubical --lossy-unification #-}
module Pushout.New.cont where

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
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive.Base
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
open import Cubical.Data.Empty as ⊥
open import Cubical.Foundations.Pointed
open import Cubical.HITs.Wedge
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Data.Fin.Inductive.Properties


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


data Susp' {ℓ} (A : Pointed ℓ) : Type ℓ where
  𝕤 : Susp' A
  𝕝 : fst A → 𝕤 ≡ 𝕤
  𝕔 : 𝕝 (pt A) ≡ refl



SphereBouquet' : ∀ {ℓ} (n : ℕ) (A : Type ℓ) → Type ℓ
SphereBouquet' n A = ⋁gen A λ _ → Susp (S⁻ n) , north


open import Cubical.Data.Empty
open import Pushout.New.finaltry

-Susp : {ℓ : Level} {ℓ' : Level} (A : Pointed ℓ) {B : Pointed ℓ'}
       → Susp∙ (typ A) →∙ B → Susp∙ (typ A) →∙ B
-Susp = {!!}

-- module _ {ℓ : Level} {A : Type ℓ}
--        (u : (i j k : I) → _)
--        {u0 : (i j : I) →  A [ ~ i ∨ i ∨ ~ j ∨ j ↦ u i j i0 ]}
--        {us : (i k : I) →  A [ ~ i ∨ i ∨ ~ k ∨ k ↦ u i i0 k ]}
--        {us2 : (i k : I) →  A [ ~ i ∨ i ∨ ~ k ∨ k ↦ u i i1 k ]}
--        {us3 : (j k : I) →  A [ ~ j ∨ j ∨ ~ k ∨ k ↦ u i0 j k ]}
--        {us4 : (j k : I) →  A [ ~ j ∨ j ∨ ~ k ∨ k ↦ u i1 j k ]}
       
       
       
--        ---------------------------
--   where
--   bot' : (i j : I) → A
--   bot' i j = hcomp (u i j) (outS (u0 i j))

--   full : (i j : I) → A
--   full i j = hcomp (λ k → λ {(i = i0) → {!!}
--                         ; (i = i1) → {!!}
--                         ; (j = i0) → {!!}
--                         ;  (j = i1) → hcomp {!!} {!!}})
--                (bot' i j)

  -- hcgen : A
  -- hcgen = hcomp (λ r → λ {(i = i0) → {!!} ; (i = i1) → {!!}}) (outS {!!})


-- module _ {ℓ : Level} {A : Type ℓ}
--        {φ : I}
--        {u : ∀ i → Partial φ A}
--        {u0 : A [ φ ↦ u i0 ]}
--        ---------------------------
--   where
--   hcgen : A
--   hcgen = hcomp ((λ j → λ { (φ = i1) → u j 1=1}))
--                 (outS u0)


test : ∀ {ℓ} {A : Type ℓ} {x y : A} → (p : x ≡ y) → p ≡ p
test {x = x} {y} p i j = {!!} -- hcgen {u = λ r → λ {(i = i0) → {!!} ; (i = i1) → {!!} ; (j = i0) → {!!} ; (j = i1) → {!!}}} {u0 = {!x!}}


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



-- elimPushout : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f : A → B} {g : A → C}  {D : Pushout f g → Type ℓ'''}
--   (inl* : (x : B) → D (inr* x)) (inr* : C → D) (comm : (c : A) → inl* (f c) ≡ inr* (g c))
-- elimPushout = ?


PushoutRec : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
  {f : A → B} {g : A → C} (inl* : B → D) (inr* : C → D) (comm : (c : A) → inl* (f c) ≡ inr* (g c))
  → Pushout f g → D
PushoutRec inl* inr* comm (inl x) = inl* x
PushoutRec inl* inr* comm (inr x) = inr* x
PushoutRec inl* inr* comm (push a i) = comm a i

-- PushoutRec : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
--   {f : A → B} {g : A → C} (inl* : B → D) (inr* : C → D) (comm : (c : A) → inl* (f c) ≡ inr* (g c))
--   → Pushout f g → D
-- PushoutRec inl* inr* comm (inl x) = inl* x
-- PushoutRec inl* inr* comm (inr x) = inr* x
-- PushoutRec inl* inr* comm (push a i) = comm a i


open SequenceMap renaming (map to ∣_∣)
open CWskel-fields



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




cong-hcomp : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B)
  {a₀₀₀ a₀₀₁ : A} {a₀₀₋ : a₀₀₀ ≡ a₀₀₁}
  {a₀₁₀ a₀₁₁ : A} {a₀₁₋ : a₀₁₀ ≡ a₀₁₁}
  {a₀₋₀ : a₀₀₀ ≡ a₀₁₀} {a₀₋₁ : a₀₀₁ ≡ a₀₁₁}
  {a₀₋₋ : Square a₀₀₋ a₀₁₋ a₀₋₀ a₀₋₁}
  {a₁₀₀ a₁₀₁ : A} {a₁₀₋ : a₁₀₀ ≡ a₁₀₁}
  {a₁₁₀ a₁₁₁ : A} {a₁₁₋ : a₁₁₀ ≡ a₁₁₁}
  {a₁₋₀ : a₁₀₀ ≡ a₁₁₀} {a₁₋₁ : a₁₀₁ ≡ a₁₁₁}
  {a₋₀₀ : a₀₀₀ ≡ a₁₀₀} {a₋₀₁ : a₀₀₁ ≡ a₁₀₁}
  {a₋₀₋ : Square a₀₀₋ a₁₀₋ a₋₀₀ a₋₀₁}
  {a₋₁₀ : a₀₁₀ ≡ a₁₁₀} {a₋₁₁ : a₀₁₁ ≡ a₁₁₁}
  {a₋₁₋ : Square a₀₁₋ a₁₁₋ a₋₁₀ a₋₁₁}
  {a₋₋₀ : Square a₀₋₀ a₁₋₀ a₋₀₀ a₋₁₀}
  {a₋₋₁ : Square a₀₋₁ a₁₋₁ a₋₀₁ a₋₁₁}
  → Cube (λ i j → f (hcomp (λ k → λ {(i = i0) → a₋₀₋ k j
                                      ; (i = i1) → a₋₁₋ k j
                                      ; (j = i0) → a₋₋₀ k i
                                      ; (j = i1) → a₋₋₁ k i})
                             (a₀₋₋ i j)))
         (λ i j → hcomp (λ k → λ {(i = i0) → f (a₋₀₋ k j)
                                      ; (i = i1) → f (a₋₁₋ k j)
                                      ; (j = i0) → f (a₋₋₀ k i)
                                      ; (j = i1) → f (a₋₋₁ k i)})
                             (f (a₀₋₋ i j)))
          (λ i j → f (a₁₀₋ j)) (λ _ j → f (a₁₁₋ j))
          (λ _ i → f (a₁₋₀ i)) λ _ i → f (a₁₋₁ i)
cong-hcomp f {a₀₋₋ = a₀₋₋}  {a₋₀₋ = a₋₀₋} {a₋₁₋ = a₋₁₋} {a₋₋₀ = a₋₋₀} {a₋₋₁ = a₋₋₁} r i j =
  hcomp (λ k → λ {(i = i0) → f (a₋₀₋ k j)
                 ; (i = i1) → f (a₋₁₋ k j)
                 ; (j = i0) → f (a₋₋₀ k i)
                 ; (j = i1) → f (a₋₋₁ k i)
                 ; (r = i0) → f (hfill (λ k → λ {(i = i0) → a₋₀₋ k j
                                      ; (i = i1) → a₋₁₋ k j
                                      ; (j = i0) → a₋₋₀ k i
                                      ; (j = i1) → a₋₋₁ k i})
                             (inS (a₀₋₋ i j)) k)})
        ((f (a₀₋₋ i j)))

cong-invSides-filler : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (f : A → B) {x y z : A} (p : x ≡ y) (q : x ≡ z)
  → (λ i j → f (invSides-filler p q i j)) ≡ (invSides-filler (cong f p) (cong f q))
cong-invSides-filler f p q = cong-hcomp f



invSides-filler-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) (i j k : I) → A
invSides-filler-filler {x = x} p q i j k =
  hfill (λ k → λ { (i = i0) → p (k ∧ j)
                 ; (i = i1) → q (~ j ∧ k)
                 ; (j = i0) → q (i ∧ k)
                 ; (j = i1) → p (~ i ∧ k)})
       (inS x) k


private
  pathlem : ∀ {ℓ} {A : Type ℓ} {x : A}  (Fx : x ≡ x) (Fpt : refl ≡ Fx) (p q : Fx ≡ Fx)
     → Square (rUnit Fx ∙ cong (Fx ∙_) Fpt)
               (rUnit Fx ∙ cong (Fx ∙_) Fpt)
               (p ∙ q) (cong₂ _∙_ p q)
  pathlem = J> λ p q → sym (rUnit _)
    ◁ flipSquare (((λ i → (λ j → rUnit (p j) i) ∙ λ j → lUnit (q j) i)
    ▷ sym (cong₂Funct _∙_ p q)))
    ▷ rUnit _

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





module _ {ℓ : Level} {B' C' D' : CWskel ℓ}
  (f' : cellMap (strictCWskel B') (strictCWskel C'))
  (g' : cellMap (strictCWskel B') (strictCWskel D')) where
  private
    B = strictCWskel B'
    C = strictCWskel C'
    D = strictCWskel D'
    f = strictCwMap f'
    g = strictCwMap g'


  open LoicPush ℓ B C D f g


--  pushoutIsoₛ : (n : ℕ) → Iso (strictPushout n) (Pushout (pushoutMapₛ n) fst)
--  pushoutIsoₛ n = iso (pushoutIsoₛ-fun n) (pushoutIsoₛ-inv n) (pushoutIsoₛ-rightInv n) (pushoutIsoₛ-leftInv n)



  open import Cubical.Foundations.Equiv.HalfAdjoint
  -- module _ (E' : CWskel ℓ) (n : ℕ) where
  --   private
  --     E = strictCWskel E'

  --     HA : (n : ℕ) → _ 
  --     HA n = equiv→HAEquiv (isoToEquiv (IsoSphereSusp n))

  --     IsoSphereSusp' : (n : ℕ) → Iso _ _
  --     IsoSphereSusp' n = isHAEquiv→Iso (HA n .snd)

  --   strict²A→ : (strict²A E' (2+ n)) → (fst E (suc (suc n)))
  --   strict²A→ (inl x) = inl x
  --   strict²A→ (inr x) = inr x
  --   strict²A→ (push a i) = push ((fst a) , Iso.inv (IsoSphereSusp n) (snd a)) i

  --   strict²A← : (fst E (suc (suc n))) → (strict²A E' (2+ n)) 
  --   strict²A← (inl x) = inl x
  --   strict²A← (inr x) = inr x
  --   strict²A← (push a i) =
  --     ((λ i → inl (α E  (suc n) (fst a , Iso.leftInv (IsoSphereSusp' n) (snd a) (~ i))))
  --     ∙ push ((fst a) , Iso.fun (IsoSphereSusp n) (snd a))) i

  --   strictPushoutIso : Iso (strict²A E' (2+ n))  (fst E (suc (suc n)))
  --   Iso.fun strictPushoutIso = strict²A→
  --   Iso.inv strictPushoutIso = strict²A←
  --   Iso.rightInv strictPushoutIso (inl x) = refl
  --   Iso.rightInv strictPushoutIso (inr x) = refl
  --   Iso.rightInv strictPushoutIso (push a i) j = h j i
  --     where
  --     h : cong strict²A→ (cong (Iso.inv strictPushoutIso) (push a)) ≡ push a
  --     h = cong-∙ strict²A→ (λ i → inl (α E (suc n) (fst a
  --                       , Iso.leftInv (IsoSphereSusp' n) (snd a) (~ i))))
  --         (push (fst a , Iso.fun (IsoSphereSusp n) (snd a)))
  --         ∙ (λ i → (λ j → inl (α E (suc n) ((fst a)
  --                  , (Iso.leftInv (IsoSphereSusp' n) (snd a) (i ∨ ~ j)))))
  --                 ∙ push (fst a , Iso.leftInv (IsoSphereSusp' n) (snd a) i))
  --         ∙ sym (lUnit _)

  --   Iso.leftInv strictPushoutIso (inl x) = refl
  --   Iso.leftInv strictPushoutIso (inr x) = refl
  --   Iso.leftInv strictPushoutIso (push a i) j = help j i -- 
  --     where
  --     PP : Square (λ _ → Iso.inv (IsoSphereSusp n) (snd a)) (λ i → Iso.inv (IsoSphereSusp n) (Iso.rightInv (IsoSphereSusp' n) (snd a) i))
  --                 (sym (Iso.leftInv (IsoSphereSusp' n) (Iso.inv (IsoSphereSusp' n) (snd a)))) refl
  --     PP = (λ i j → Iso.leftInv (IsoSphereSusp' n) (Iso.inv (IsoSphereSusp' n) (snd a)) (~ i ∨ j))
  --        ▷ sym (isHAEquiv.com-op (snd (HA n)) (snd a))

  --     help : Path (Path (strict²A E' (2+ n)) _ _) (cong strict²A← (push (fst a , Iso.inv (IsoSphereSusp n) (snd a)))) (push a) 
  --     help = (λ i → (λ j → inl (α E (suc n) ((fst a) , PP j i)))
  --                   ∙ push (fst a , Iso.rightInv (IsoSphereSusp' n) (snd a) i))
  --          ∙ sym (lUnit _)


  pushoutA* : ℕ → Type ℓ
  pushoutA* zero = B .fst zero
  pushoutA* (suc n) = Pushout {A = B .fst n} {B = fst C (suc n)} {C = fst D (suc n)} (inl ∘ ∣ f ∣ n) (inl ∘ ∣ g ∣ n)

  bEq : (n : ℕ) → Iso (B .fst (suc n))  (strictA B (suc n))
  Iso.fun (bEq n) x = x
  Iso.inv (bEq n) x = x
  Iso.rightInv (bEq n) x = refl
  Iso.leftInv (bEq n) x = refl
  -- pushoutEquiv _ _ _ _ (idEquiv _) (idEquiv _) (idEquiv _) (λ _ x → α B n x) λ i x → fst x


  open import Cubical.Foundations.Equiv.HalfAdjoint
  module _ (E' : CWskel ℓ) (n : ℕ) where
    private
      E = strictCWskel E'

      HA : (n : ℕ) → _ 
      HA n = equiv→HAEquiv (isoToEquiv (IsoSphereSusp n))

      IsoSphereSusp' : (n : ℕ) → Iso _ _
      IsoSphereSusp' n = isHAEquiv→Iso (HA n .snd)

    strict²A→ : (strict²A E (2+ n)) → (fst E (suc (suc n)))
    strict²A→ (inl x) = inl x
    strict²A→ (inr x) = inr x
    strict²A→ (push a i) = push ((fst a) , Iso.inv (IsoSphereSusp n) (snd a)) i

    strict²A← : (fst E (suc (suc n))) → (strict²A E (2+ n)) 
    strict²A← (inl x) = inl x
    strict²A← (inr x) = inr x
    strict²A← (push a i) =
      ((λ i → inl (α E  (suc n) (fst a , Iso.leftInv (IsoSphereSusp' n) (snd a) (~ i))))
      ∙ push ((fst a) , Iso.fun (IsoSphereSusp n) (snd a))) i

    strictPushoutIso : Iso (strict²A E (2+ n))  (fst E (suc (suc n)))
    Iso.fun strictPushoutIso = strict²A→
    Iso.inv strictPushoutIso = strict²A←
    Iso.rightInv strictPushoutIso (inl x) = refl
    Iso.rightInv strictPushoutIso (inr x) = refl
    Iso.rightInv strictPushoutIso (push a i) j = h j i
      where
      h : cong strict²A→ (cong (Iso.inv strictPushoutIso) (push a)) ≡ push a
      h = cong-∙ strict²A→ (λ i → inl (α E (suc n) (fst a
                        , Iso.leftInv (IsoSphereSusp' n) (snd a) (~ i))))
          (push (fst a , Iso.fun (IsoSphereSusp n) (snd a)))
          ∙ (λ i → (λ j → inl (α E (suc n) ((fst a)
                   , (Iso.leftInv (IsoSphereSusp' n) (snd a) (i ∨ ~ j)))))
                  ∙ push (fst a , Iso.leftInv (IsoSphereSusp' n) (snd a) i))
          ∙ sym (lUnit _)

    Iso.leftInv strictPushoutIso (inl x) = refl
    Iso.leftInv strictPushoutIso (inr x) = refl
    Iso.leftInv strictPushoutIso (push a i) j = help j i -- 
      where
      PP : Square (λ _ → Iso.inv (IsoSphereSusp n) (snd a)) (λ i → Iso.inv (IsoSphereSusp n) (Iso.rightInv (IsoSphereSusp' n) (snd a) i))
                  (sym (Iso.leftInv (IsoSphereSusp' n) (Iso.inv (IsoSphereSusp' n) (snd a)))) refl
      PP = (λ i j → Iso.leftInv (IsoSphereSusp' n) (Iso.inv (IsoSphereSusp' n) (snd a)) (~ i ∨ j))
         ▷ sym (isHAEquiv.com-op (snd (HA n)) (snd a))

      help : Path (Path (strict²A E (2+ n)) _ _) (cong strict²A← (push (fst a , Iso.inv (IsoSphereSusp n) (snd a)))) (push a) 
      help = (λ i → (λ j → inl (α E (suc n) ((fst a) , PP j i)))
                    ∙ push (fst a , Iso.rightInv (IsoSphereSusp' n) (snd a) i))
           ∙ sym (lUnit _)

  strictPushoutIsoL : (n : ℕ) → Iso  (strict²A C (2+ n)) (fst C (suc (suc n)))
  strictPushoutIsoL n = strictPushoutIso C' n

  strictPushoutIsoR : (n : ℕ) → Iso  (strict²A D (2+ n)) (fst D (suc (suc n)))
  strictPushoutIsoR n = strictPushoutIso D' n


  -- strictPushoutIsoR : (n : ℕ) → Iso  (strict²A D' (2+ n)) (fst D (suc (suc n)))
  -- strictPushoutIsoR n = {!!} -- strictPushoutIso D' n


  cohL : (n : ℕ) (x : B .fst (suc n)) → strictMap f (suc n) x ≡ strictMapFun f' (suc n) x
  cohL n (inl x) = refl
  cohL n (inr x) = refl
  cohL n (push a i) j = lUnit (cong (strictMapFun f' (suc n)) (push a)) (~ j) i

  cohR : (n : ℕ) (x : B .fst (suc n)) → strictMap g (suc n) x ≡ strictMapFun g' (suc n) x
  cohR n (inl x) = refl
  cohR n (inr x) = refl
  cohR n (push a i) j = lUnit (cong (strictMapFun g' (suc n)) (push a)) (~ j) i

  strictPushoutA*Iso : (n : ℕ) → Iso (pushoutA* (suc (suc n))) (strictPushout n)
  strictPushoutA*Iso n = {!!}
  {- pushoutIso _ _ _ _ (idEquiv _)
    (invEquiv (isoToEquiv (strictPushoutIsoL n))) (invEquiv (isoToEquiv (strictPushoutIsoR n)))
      (funExt (cohL n)) (funExt (cohR n))
-}
  
  strictPushoutA*Iso' : (n : ℕ) → Iso  (strictPushout n) (pushoutA* (suc (suc n)))
  strictPushoutA*Iso' n = pushoutIso _ _ _ _ (idEquiv _)
    ( (isoToEquiv (strictPushoutIsoL n))) ( (isoToEquiv (strictPushoutIsoR n)))
      (λ i x → inl (cohL n x i)) λ i x → inl (cohR n x i)

  -- strictPushoutA*Iso'altFun : (n : ℕ) →  (strictPushout n) → (pushoutA* (suc (suc n)))
  -- strictPushoutA*Iso'altFun n (inl x) = {!Iso.fun (strictPushoutIsoL n)!}
  -- strictPushoutA*Iso'altFun n (inr x) = {!!}
  -- strictPushoutA*Iso'altFun n (push a i) = {!!}


  -- myMap : (n : ℕ) → pushoutA* (suc (suc n)) → Pushout (pushoutMapₛ n) fst
  -- myMap n (inl (inl x)) = inl (inl x)
  -- myMap n (inl (inr x)) = inr (inl (inl x))
  -- myMap zero (inl (push (a , false) i)) =  push (inl (inl a) , south) i
  -- myMap zero (inl (push (a , true) i)) =  push (inl (inl a) , north) i
  -- myMap (suc zero) (inl (push (a , b) i)) = {!!}
  -- myMap (suc (suc n)) (inl (push (a , b) i)) = push (inl (inl a) , b) i
  -- myMap n (inr (inl x)) = inl (inr x)
  -- myMap n (inr (inr x)) = inr (inr x)
  -- myMap zero (inr (push (a , false) i)) = push (inr a , south) i
  -- myMap zero (inr (push (a , true) i)) = push (inr a , north) i
  -- myMap (suc zero) (inr (push (a , b) i)) =
  --   ((λ j → inl (inr (α D 2 (a , S¹→SuspBool→S¹ b (~ j)))))
  --   ∙ push (inr a , Iso.fun (IsoSphereSusp 1) b)) i
  -- myMap (suc (suc n)) (inr (push (a , b) i)) = push (inr a , b) i
  -- myMap n (push (inl x) i) = inl (push x i)
  -- myMap n (push (inr x) i) = inl {!!} -- ((push (inl (inr x) , north) ∙∙ refl ∙∙ (λ i → push (inl (inr x) , south) (~ i)))) i
  -- myMap n (push (push a i₁) i) = {!!}

  pushoutMapₛ* : (n : ℕ) → (((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n))) × (Susp (S⁻ n)) → pushoutA* (suc n)
  pushoutMapₛ* n = pushoutMapₛ n


  CardPush : (n : ℕ) → Type
  CardPush zero = ((A C zero)) ⊎ (A D zero)
  CardPush (suc n) = ((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n))

  S' : (n : ℕ) → Type
  S' zero = ⊥
  S' (suc n) = Susp (S⁻ n)

  pushoutMapₛfull : (n : ℕ) → CardPush n × (S' n) → pushoutA* n
  pushoutMapₛfull (suc n) = pushoutMapₛ n

  
  pushoutIsoₛ' : (n : ℕ) → Iso (strictPushout n) (Pushout (pushoutMapₛ* n) fst)
  pushoutIsoₛ' n = iso (pushoutIsoₛ-fun n) (pushoutIsoₛ-inv n) (pushoutIsoₛ-rightInv n) (pushoutIsoₛ-leftInv n)


  mainIso : (n : ℕ) → Iso (pushoutA* (suc n)) (Pushout (pushoutMapₛfull n) fst)
  mainIso zero = compIso {!Iso.inv (mainIso ?)!} {!Pushout⊎!} -- (PushoutEmptyFam (λ()) λ())
  mainIso (suc n) = compIso (invIso (strictPushoutA*Iso' n)) (pushoutIsoₛ' n)


  improveMainL : (n : ℕ) → pushoutA* n → pushoutA* (suc n)
  improveMainL zero x = inl (inl (∣ f ∣ 0 x))
  improveMainL (suc n) (inl x) = inl (inl x)
  improveMainL (suc n) (inr x) = inr (inl (x))
  improveMainL (suc n) (push a i) = push (inl a) i


  improveMainR : (n : ℕ) → CardPush n → pushoutA* (suc n)
  improveMainR zero (inl x) = inl (inr x)
  improveMainR zero (inr x) = inr (inr x)
  improveMainR (suc n) (inl (inl x)) = inl (inr x)
  improveMainR (suc n) (inl (inr x)) = push (inr x) i0
  improveMainR (suc n) (inr x) = inr (inr x)

  improveMainFillerS : (n : ℕ) (x : _) (b : _) → (i j k : I) → pushoutA* (suc (suc (suc n)))
  improveMainFillerS n x b i j k =
    hfill (λ r → λ {(i = i0) → push (inl (α B (suc n) (b , x))) (~ j)
                   ; (i = i1) → push (inr b) (~ j)
                   ; (j = i0) → inr (inl (lUnit (cong (∣ g ∣ (suc (suc n)) ) (push (b , x))) r i))
                   ; (j = i1) → inl (inl (∣ f ∣ (suc (suc n)) (push (b , x) i)))})
                   (inS (push (push (b , x) i) (~ j))) k

  improveMainFiller : (n : ℕ) (x : _) (b : _) → (i j k : I) → pushoutA* (suc (suc (suc n)))
  improveMainFiller n x b i j k =
    hfill (λ r → λ {(i = i0) → inl (inl (lUnit (cong (∣ f ∣ (suc (suc n)) ) (push (b , x))) (~ j) r))
                   ; (i = i1) → improveMainFillerS n x b r j i1
                   ; (j = i0) → improveMainL (suc (suc n))
                                   (doubleCompPath-filler ((λ i → inl (strictMap {B} {C} f (suc (suc n)) (push (b , x) (~ i)))))
                                   (push (α B (suc n) (b , x)))
                                   (λ i → inr (strictMap {B} {D} g (suc (suc n)) (push (b , x) i))) r i)
                   ; (j = i1) → inl (inl (∣ f ∣ (suc (suc n)) (push (b , x) r)))})
                   (inS (push (inl (α B (suc n) (b , x))) (i ∧ ~ j))) k

  improveMain : (n : ℕ) → Pushout (pushoutMapₛfull n) fst → pushoutA* (suc n)
  improveMain n (inl x) = improveMainL n x
  improveMain n (inr x) = improveMainR n x
  improveMain (suc n) (push (inl (inl x) , s) i) = inl (push (x , Iso.inv (IsoSphereSusp n) s) i)
  improveMain (suc n) (push (inl (inr x) , north) i) = push (inr x) i0
  improveMain (suc n) (push (inl (inr x) , south) i) = push (inr x) (~ i)
  improveMain (suc (suc n)) (push (inl (inr b) , merid x i) j) =
    improveMainFiller n x b i j i1
  improveMain (suc n) (push (inr x , s) i) = inr (push (x , Iso.inv (IsoSphereSusp n) s) i)

  improveMain≡ : (n : ℕ) (x : _) → improveMain n x ≡ Iso.inv (mainIso n) x
  improveMain≡ n x = {!!}


  mainEquiv : (n : ℕ) → (Pushout (pushoutMapₛfull n) fst) ≃ (pushoutA* (suc n))
  fst (mainEquiv n) = improveMain n
  snd (mainEquiv n) = isE
    where
    isE : isEquiv (improveMain n)
    isE = subst isEquiv (funExt (λ x → sym (improveMain≡ n x)))
      (invEquiv (isoToEquiv (mainIso n)) .snd)


  pushoutA*↑ : (n : ℕ) → pushoutA* n → pushoutA* (suc n)
  pushoutA*↑ n x = fst (mainEquiv n) (inl x)

  
  -- isEquivImproveMain : ?


  
  -- C
  cofibCW∙ : (n : ℕ) (C : CWskel ℓ)  → Pointed _
  cofibCW∙ n C = cofibCW n C , inl tt

  -- non-strict quotiented by non-strict
  -- Pₙ₊₁/Pₙ
  cofibPush : (n : ℕ) → Type _
  cofibPush n = cofib (pushoutA*↑ n)

  -- strict quotiented by non-strict
  -- Pₙ₊₁∼/Pₙ
  cofibPush' : (n : ℕ) → Type _
  cofibPush' n = cofib {A = pushoutA* n} {B = Pushout (pushoutMapₛfull n) fst} inl

  -- These are equuivalent
  cofibsIso : (n : ℕ) → cofibPush' n ≃ (cofibPush n)
  cofibsIso n = pushoutEquiv _ _ _ _ (idEquiv _) (idEquiv _) (mainEquiv n) (λ _ _ → tt) λ i x → improveMain n (inl x)

  ΣSphereBouquet' : (n : ℕ) → Type
  ΣSphereBouquet' n = Susp (SphereBouquet' n ((Fin (card C (suc n)) ⊎ Fin (card B n)) ⊎ Fin (card D (suc n))))

  data 𝟛 : Type where
    𝕔 𝕕 𝕓 : 𝟛

  BouquetDecompFam : (n : ℕ) → 𝟛 → Pointed _
  BouquetDecompFam n 𝕔 = cofibCW∙ (suc n) C
  BouquetDecompFam n 𝕕 = cofibCW∙ (suc n) D
  BouquetDecompFam n 𝕓 = Susp∙ (cofibCW n B)

  
  -- Cₙ₊₁/Cₙ ∨ Dₙ₊₁ ∨ Σ Bₙ/Bₙ₋₁
  BouquetDecomp : (n : ℕ) → Type ℓ
  BouquetDecomp n = ⋁gen 𝟛 (BouquetDecompFam n)

 -- ΣSphereBouquet'→ : ?

  ΣBouquetDecomp : (n : ℕ) → ΣSphereBouquet' n → BouquetDecomp n 
  ΣBouquetDecomp n north = inl tt
  ΣBouquetDecomp n south = inl tt
  ΣBouquetDecomp n (merid (inl x) i) = {!!}
  ΣBouquetDecomp n (merid (inr (inl (inl x) , y)) i) =
    (push 𝕔
    ∙∙ ((λ j → inr (𝕔 , push (α C (suc n) (x , Iso.inv (IsoSphereSusp n) y)) j))
    ∙∙ (λ j → inr (𝕔 , inr ((push (x , Iso.inv (IsoSphereSusp n) y) ∙ push (x , ptSn n) ⁻¹) j)))
    ∙∙ λ j → inr (𝕔 , push (α C (suc n) (x , ptSn n)) (~ j)))
    ∙∙ (push 𝕔 ⁻¹)) i
  ΣBouquetDecomp n (merid (inr (inl (inr x) , y)) i) =
    (push 𝕓
    ∙∙ (λ i → inr (𝕓 , toSusp (_ , inl tt) (inr {!suspFun (curry (α B n) x) y!}) i))
    ∙∙ push 𝕓 ⁻¹) i
  ΣBouquetDecomp n (merid (inr (inr x , y)) i) =
     (push 𝕕
    ∙∙ ((λ j → inr (𝕕 , push (α D (suc n) (x , Iso.inv (IsoSphereSusp n) y)) j))
    ∙∙ (λ j → inr (𝕕 , inr ((push (x , Iso.inv (IsoSphereSusp n) y) ∙ push (x , ptSn n) ⁻¹) j)))
    ∙∙ λ j → inr (𝕕 , push (α D (suc n) (x , ptSn n)) (~ j)))
    ∙∙ (push 𝕕 ⁻¹)) i
  ΣBouquetDecomp n (merid (push a i) j) = {!a!}

--   -- strict map to ΣBouquet Pₙ₊₁∼ → Σ⋁
--   cofib→sphereBouquet : (n : ℕ) → cofibPush' (suc n) → ΣSphereBouquet' n
--   cofib→sphereBouquet n (inl x) = north
--   cofib→sphereBouquet n (inr (inl x)) = north
--   cofib→sphereBouquet n (inr (inr x)) = south
--   cofib→sphereBouquet n (inr (push (w  , b) i)) = merid (inr (w , b)) i
--   cofib→sphereBouquet n (push a i) = north

--   private
--     cofib'→sphereBouquetFiller : (n : ℕ) (a : _) (s : _)
--       → (i j k : I) → ΣSphereBouquet' (suc n)
--     cofib'→sphereBouquetFiller n a s i j k =
--         hfill (λ k → λ {(i = i0) → north
--                      ; (i = i1) → merid (inr (inl (inr a) , merid (ptSn n) j)) (~ k)
--                      ; (j = i0) → merid (inr (inl (inr a) , north)) (i ∧ ~ k)
--                      ; (j = i1) → merid (inr (inl (inr a) , south)) (i ∧ ~ k)})
--             (inS (merid (inr ((inl (inr a)) , merid s j)) i)) k

--   -- non-strict to ΣBouquet  Pₙ₊₁ → Σ⋁
--   cofib'→sphereBouquet : (n : ℕ) → cofibPush (suc n) → ΣSphereBouquet' n
--   cofib'→sphereBouquet n (inl tt) = north
--   cofib'→sphereBouquet n (inr (inl (inl x))) = north
--   cofib'→sphereBouquet n (inr (inl (inr x))) = south
--   cofib'→sphereBouquet n (inr (inl (push (a , s) i))) =
--     merid (inr (inl (inl a) , Iso.fun (IsoSphereSusp n) s)) i
--   cofib'→sphereBouquet n (inr (inr (inl x))) = north
--   cofib'→sphereBouquet n (inr (inr (inr x))) = south
--   cofib'→sphereBouquet n (inr (inr (push (a , s) i))) =
--     merid (inr ((inr a) , (Iso.fun (IsoSphereSusp n) s))) i
--   cofib'→sphereBouquet n (inr (push (inl x) i)) = north
--   cofib'→sphereBouquet zero (inr (push (inr x) i)) =
--     (merid (inr (inl (inr x) , north)) ∙ sym (merid (inr (inl (inr x) , south)))) i
--   cofib'→sphereBouquet (suc n) (inr (push (inr x) i)) = north
--   cofib'→sphereBouquet (suc n) (inr (push (push (a , s) i) j)) =
--     cofib'→sphereBouquetFiller n a s i j i1
--   cofib'→sphereBouquet n (push (inl x) i) = north
--   cofib'→sphereBouquet n (push (inr x) i) = north
--   cofib'→sphereBouquet n (push (push a i₁) i) = north


--   -- proof that these maps are the same (modulo the their equivalence)
--   module AgreeOnΣSphereBoquet where
--     cofSphereInl : (n : ℕ) (x : _)
--       → cofib'→sphereBouquet n (fst (cofibsIso (suc n)) (inr (inl x))) ≡ cofib→sphereBouquet n (inr (inl x))
--     cofSphereInl n (inl x) = refl
--     cofSphereInl n (inr x) = refl
--     cofSphereInl n (push a i) = refl

--     cofSphereInr : (n : ℕ) (x : _) → cofib'→sphereBouquet n (fst (cofibsIso (suc n)) (inr (inr x))) ≡ cofib→sphereBouquet n (inr (inr x))
--     cofSphereInr n (inl (inl x)) = refl
--     cofSphereInr n (inl (inr x)) = merid (inl tt)
--     cofSphereInr n (inr x) = refl

--     sq1 : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (q : x ≡ y) → p ≡ q → (i j k : I) → A
--     sq1 {x = x} p q r i j k =
--       hfill (λ k → λ {(i = i0) → x ; (i = i1) → r (~ k) j ; (j = i0) → x ; (j = i1) → q i})
--         (inS (q (i ∧ j))) k

--     sq2 : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (q q' : x ≡ y) → p ≡ q → q ≡ q' → (i j k : I) → A
--     sq2 {x = x} p q q' r w i j k =
--       hfill (λ k → λ {(i = i0) → x ; (i = i1) → r (~ k) j ; (j = i0) → x ; (j = i1) → w k i})
--         (inS (q (i ∧ j))) k

--     -- main
--     cofSphere : (n : ℕ) (x : cofibPush' (suc n)) → cofib'→sphereBouquet n (fst (cofibsIso (suc n)) x) ≡ cofib→sphereBouquet n x
--     cofSphere n (inl x) = refl
--     cofSphere n (inr (inl x)) = cofSphereInl n x
--     cofSphere n (inr (inr x)) = cofSphereInr n x
--     cofSphere n (inr (push (inl (inl x) , s) i)) j = merid (inr (inl (inl x) , Iso.rightInv (IsoSphereSusp n) s j)) i
--     cofSphere n (inr (push (inl (inr x) , north) i)) j =
--       sq1 (merid (inl tt)) (merid (inr (inl (inr x) , north))) (cong merid (push (inl (inr x)))) i j i1
--     cofSphere zero (inr (push (inl (inr x) , south) i)) j =
--       hcomp (λ k → λ {(i = i0) → merid (inr (inl (inr x) , south)) (~ k)
--                      ; (i = i1) → merid (inl tt) j
--                      ; (j = i0) → compPath-filler (merid (inr (inl (inr x) , north))) (sym (merid (inr (inl (inr x) , south)))) k (~ i)
--                      ; (j = i1) → merid (inr (inl (inr x) , south)) (~ k ∨ i)})
--         (sq1 (sym (merid (inl tt))) (sym (merid (inr (inl (inr x) , north))))
--              (cong (sym ∘ merid) (push (inl (inr x)))) i (~ j)  i1)
--     cofSphere (suc n) (inr (push (inl (inr x) , south) i)) j =
--         sq2 (merid (inl tt)) (merid (inr (inl (inr x) , north)))
--           (merid (inr (inl (inr x) , south))) (cong merid (push (inl (inr x))))
--           (λ i → merid (inr (inl (inr x) , merid (ptSn n) i))) i j i1
--     cofSphere (suc n) (inr (push (inl (inr b) , merid x i) j)) k =
--       hcomp (λ r → λ {(j = i0) → cofSphereInl (suc n)
--                                     (doubleCompPath-filler (λ i → inl (strictMap {B} {C} f (suc (suc n)) (push (b , x) (~ i))))
--                                          (push (α B (suc n) (b , x)))
--                                          (λ i → inr (strictMap {B} {D} g (suc (suc n)) (push (b , x) i))) r i) k
--                      ; (j = i1) → merid (push (inl (inr b)) (~ r)) k
--                      ; (k = i0) → cofib'→sphereBouquet (suc n) (inr (improveMainFiller n x b i j r))
--                      ; (k = i1) → merid (inr (inl (inr b) , merid x (i ∧ r))) j
--                      ; (i = i0) → (i=i0 _ _  ( (merid (inr (inl (inr b) , north)))) ( (merid (inl tt)))
--                           (sym (cong (merid) (push (inl (inr b))))))  r j k
--                      ; (i = i1) → i=i1 r j k})
--             ( (merid (inr (inl (inr b) , north)) (k ∧ j)))
--       where -- r j k
--       i=i0 : ∀ {ℓ} {A : Type ℓ} (x y : A) (pn ps : x ≡ y) (mx : pn ≡ ps)
--            → Cube (λ j k → pn (k ∧ j))
--                    (λ j k → sq1 ps pn (sym mx) j k i1)
--                    (λ k r → x) (λ r k → mx r k)
--                    (λ r j → x)
--                   λ r j → pn j
--       i=i0 = λ x → J> (J> (rUnit refl))
--       i=i1 : Cube (λ j k → merid (inr (inl (inr b) , north)) (k ∧ j))
--                   ((λ j k → sq2 (merid (inl tt)) (merid (inr (inl (inr b) , north)))
--                                      (merid (inr (inl (inr b) , south))) (cong merid (push (inl (inr b))))
--                                      (λ i → merid (inr (inl (inr b) , merid (ptSn n) i))) j k i1))
--                  (λ _ _ → north) (λ r k → merid (push (inl (inr b)) (~ r)) k)
--                  (λ r j → cofib'→sphereBouquet (suc n) (inr (improveMainFiller n x b i1 j r)))
--                  λ r j →  merid (inr (inl (inr b) , merid x r)) j
--       i=i1 r j k =
--         hcomp (λ i → λ {(j = i0) → north -- north
--                      ; (j = i1) → merid (push (inl (inr b)) (~ r ∨ ~ i)) k
--                      ; (k = i0) → cofib'→sphereBouquet (suc n) (inr (improveMainFillerS n x b r j i))
--                      ; (k = i1) → compPath-filler (λ i → merid (inr (inl (inr b) , merid x i)))
--                                 (λ i → merid (inr (inl (inr b) , merid (ptSn n) (~ i)))) (~ i) r j
--                      ; (r = i0) → merid (inr (inl (inr b) , north)) (k ∧ j)
--                      ; (r = i1) → sq2 (merid (inl tt)) (merid (inr (inl (inr b) , north)))
--                                      (merid (inr (inl (inr b) , south))) (cong merid (push (inl (inr b))))
--                                      (λ i → merid (inr (inl (inr b) , merid (ptSn n) i))) j k i
--                      })
--          (help _ _ (merid (inr (inl (inr b) , north))) (merid (inr (inl (inr b) , south)))
--                    (λ i → merid (inr (inl (inr b) , merid (ptSn n) i)))
--                    (λ i → merid (inr (inl (inr b) , merid x i))) k j r)
--          where
--          help : ∀ {ℓ} {A : Type ℓ} (x y : A) (pn ps : x ≡ y) (mpt : pn ≡ ps) (mx : pn ≡ ps)
--            → Cube (λ j i → hcomp (λ k → λ {(i = i0) → x
--                                             ; (i = i1) → mpt (~ j) (~ k)
--                                             ; (~ j = i0) → pn (i ∧ ~ k)
--                                             ; (~ j = i1) → ps (i ∧ ~ k)})
--                                    (mx (~ j) i))
--                    (λ j r → (mx ∙ sym mpt) r j)
--                    (λ k r → x) (λ k r → pn k)
--                    (λ k j → pn (k ∧ j))
--                    (λ k j → pn (k ∧ j))
--          help x = J> (J> λ mx → (λ i j k →
--            hcomp (λ r → λ {(j = i0) → x 
--                      ; (j = i1) → x
--                      ; (i = i1) → mx k j
--                      ; (k = i0) → x
--                      ; (k = i1) → x}
--                      ) (sym≡flipSquare mx i j k)) ▷ λ i j r → rUnit (mx) i r j)
--     cofSphere n (inr (push (inr x , s) i)) j = merid (inr (inr x , Iso.rightInv (IsoSphereSusp n) s j)) i
--     cofSphere n (push a i) j = main j i
--       where
--       mm : (n : ℕ) (a : _) → Square (cong (cofib'→sphereBouquet n) (push a))
--                                       (cong (cofib→sphereBouquet n) (push a))
--                                       refl (cofSphereInl n a)
--       mm n (inl x) = refl
--       mm n (inr x) = refl
--       mm n (push a i) = refl
--       main : Square (cong (cofib'→sphereBouquet n) (cong (fst (cofibsIso (suc n))) (push a)))
--                     (cong (cofib→sphereBouquet n) (push a))
--                     refl (cofSphereInl n a)
--       main = (cong-∙∙ (cofib'→sphereBouquet n) _ _ _ ∙ sym (rUnit _)) ◁ mm n a



-- --   WedgeDecomp : (n : ℕ) → Type ℓ
-- --   WedgeDecomp n = ((cofibCW∙ (suc n) C) ⋁∙ᵣ (Susp' (cofibCW∙ n B) , 𝕤)) ⋁ cofibCW∙ (suc n) D

-- --   -- WedgeDecompS : (n : ℕ) → Type ℓ
-- --   -- WedgeDecompS n = (Susp∙ (cofibCW (suc n)) C ⋁∙ᵣ Susp∙ (Susp (cofibCW n B))) ⋁ cofibCW∙ (suc n) D

-- --   Bloop : (n : ℕ) → B .fst (suc n) → Path (WedgeDecomp n) (inl (inl (inl tt))) (inr (inl tt))
-- --   Bloop n x = (λ i → inl (push tt i)) ∙∙ (λ i → inl (inr (𝕝 (inr x) i))) ∙∙ push tt

-- --   pushoutA*→WedgeDecompF : (n : ℕ) (a :  B .fst (suc n)) → (i j : I) → WedgeDecomp n
-- --   pushoutA*→WedgeDecompF n a i j =
-- --     doubleCompPath-filler {_} {WedgeDecomp n}
-- --       (λ j → inl (((λ j → inl (push (strictMapFun f' (suc n) a) (~ j))) ∙ push tt) j))
-- --      (λ i → inl (inr (𝕝 (inr a) i)))
-- --      (((push tt ∙ λ j → inr (push (strictMapFun g' (suc n) a) j)))) j i
  
-- --   pushoutA*→WedgeDecomp : (n : ℕ) → pushoutA* (suc (suc n)) → WedgeDecomp n
-- --   pushoutA*→WedgeDecomp n (inl x) = inl (inl (inr x))
-- --   pushoutA*→WedgeDecomp n (inr x) = inr (inr x)
-- --   pushoutA*→WedgeDecomp n (push a i) = pushoutA*→WedgeDecompF n a i i1

-- --   pushoutA*→WedgeDecomp' : {!!}
-- --   pushoutA*→WedgeDecomp' = {!!}

-- --   pushoutA*→WedgeDecompVanish'∙ : (n : ℕ) (x : pushoutA* (suc n)) → WedgeDecomp n
-- --   pushoutA*→WedgeDecompVanish'∙ n (inl x) = inl (inl  (inl tt)) -- inl (inl (inl tt))
-- --   pushoutA*→WedgeDecompVanish'∙ n (inr x) = inr (inl tt)
-- --   pushoutA*→WedgeDecompVanish'∙ n (push a i) = ((λ i → inl (push tt i)) ∙ push tt ) i 

-- --   pushoutA*→WedgeDecompVanish' : (n : ℕ) (x : _) → pushoutA*→WedgeDecompVanish'∙ n x ≡ pushoutA*→WedgeDecomp n (pushoutA*↑ (suc n) x)
-- --   pushoutA*→WedgeDecompVanish' n (inl x) i = inl (inl (push x i))
-- --   pushoutA*→WedgeDecompVanish' n (inr x) i = inr (push x i)
-- --   pushoutA*→WedgeDecompVanish' n (push a i) j = {!!}

-- --   pushoutA*→WedgeDecompVanish : (n : ℕ) (x : _) → inl (inr 𝕤) ≡ pushoutA*→WedgeDecomp n (pushoutA*↑ (suc n) x)
-- --   pushoutA*→WedgeDecompVanish n (inl x) i = inl (((λ j → inl (push x (~ j))) ∙ (push tt)) (~ i))
-- --   pushoutA*→WedgeDecompVanish n (inr x) = (push tt ∙ λ j → inr (push x j))
-- --   pushoutA*→WedgeDecompVanish n (push a i) j =
-- --     hcomp (λ k → λ {(i = i0) → pushoutA*→WedgeDecompF n (inl a) i0 j
-- --                    ; (i = i1) → pushoutA*→WedgeDecompF n (inl a) i1 j
-- --                    ; (j = i0) → inl (inr ((sym 𝕔 ∙ cong 𝕝 (push a)) (~ k) i))
-- --                    ; (j = i1) → pushoutA*→WedgeDecompF n (inl a) i i1})
-- --           (pushoutA*→WedgeDecompF n (inl a) i j)

-- --   toWedgeDecomp : (n : ℕ) → cofibPush (suc n) → WedgeDecomp n
-- --   toWedgeDecomp n (inl x) = (inl (inr 𝕤))
-- --   toWedgeDecomp n (inr x) = pushoutA*→WedgeDecomp n x
-- --   toWedgeDecomp n (push x i) = pushoutA*→WedgeDecompVanish n x i

-- --   WedegeDecompFunMid : {!!}
-- --   WedegeDecompFunMid = {!!}

-- --   -- precofibToSusp : (n : ℕ) → Pushout (pushoutMapₛfull (suc n)) fst → Susp (pushoutA* (suc n)) 
-- --   -- precofibToSusp n (inl x) = 𝕤
-- --   -- precofibToSusp n (inr x) = 𝕤
-- --   -- precofibToSusp n (push a i) = merid {!!} i

-- --   ↓P : (n : ℕ) → cofibPush (suc n) → Susp' (cofibPush n , inl tt)
-- --   ↓P n (inl x) = 𝕤
-- --   ↓P n (inr x) = 𝕤
-- --   ↓P n (push a i) = 𝕝 (inr a) i

-- --   functL : (n : ℕ) → cofibCW n B → cofibCW n C
-- --   functL n (inl x) = inl tt
-- --   functL n (inr x) = inr (∣ f ∣ (suc n) x)
-- --   functL n (push a i) = push (∣ f ∣ n a) i

-- --   functR : (n : ℕ) → cofibCW n B → cofibCW n D
-- --   functR n (inl x) = inl tt
-- --   functR n (inr x) = inr (∣ g ∣ (suc n) x)
-- --   functR n (push a i) = push (∣ g ∣ n a) i

-- --   Susp→Susp' : ∀ {ℓ} {A : Pointed ℓ} → Susp (typ A) → Susp' A
-- --   Susp→Susp' north = 𝕤
-- --   Susp→Susp' south = 𝕤
-- --   Susp→Susp' (merid a i) = 𝕝 a i

-- --   WedegeDecompFun : (n : ℕ) → WedgeDecomp (suc n) → Susp' (WedgeDecomp n , (inl (inr 𝕤)))
-- --   WedegeDecompFun n (inl (inl (inl x))) = 𝕤
-- --   WedegeDecompFun n (inl (inl (inr x))) = 𝕤
-- --   WedegeDecompFun n (inl (inl (push a i))) = 𝕝 (inl (inl (inr a))) i
-- --   WedegeDecompFun n (inl (inr 𝕤)) = 𝕤
-- --   WedegeDecompFun n (inl (inr (𝕝 a i))) = (𝕝 (inl (inl (functL (suc n) a)))
-- --                                       ∙∙ 𝕝 (inl (inr (Susp→Susp' ((suspFun inr ∘ δ-pre _) a)))) ⁻¹
-- --                                       ∙∙ 𝕝 (inr (functR (suc n) a)) ⁻¹) i
-- --   WedegeDecompFun n (inl (inr (𝕔 i j))) =
-- --     (cong₃ _∙∙_∙∙_ (cong 𝕝 (λ i → inl (push tt i))) (λ _ → 𝕝 (inl (inr 𝕤)) ⁻¹) (cong (sym ∘ 𝕝) (sym (push tt)))
-- --     ∙ cong₃ _∙∙_∙∙_ 𝕔 (cong sym 𝕔) (cong sym 𝕔)
-- --     ∙ sym (rUnit refl)) i j
-- --   WedegeDecompFun n (inl (push a i)) = 𝕤
-- --   WedegeDecompFun n (inr (inl x)) = 𝕤
-- --   WedegeDecompFun n (inr (inr x)) = 𝕤
-- --   WedegeDecompFun n (inr (push a i)) = 𝕝 (inr (inr a)) i
-- --   WedegeDecompFun n (push a i) = 𝕤

-- --   compWithProjB : (n : ℕ) → WedgeDecomp (suc n) → Susp' (Susp' (cofibCW∙ n B) , 𝕤)
-- --   compWithProjB n (inl (inl x)) = 𝕤
-- --   compWithProjB n (inl (inr 𝕤)) = 𝕤
-- --   compWithProjB n (inl (inr (𝕝 x i))) = 𝕝 ( (Susp→Susp' ((suspFun inr ∘ δ-pre _) x))) (~ i)
-- --   compWithProjB n (inl (inr (𝕔 i i₁))) = 𝕔 i (~ i₁)
-- --   compWithProjB n (inl (push a i)) = 𝕤
-- --   compWithProjB n (inr x) = 𝕤
-- --   compWithProjB n (push a i) = 𝕤

-- -- -- projOutB n (WedegeDecompFun

-- --   comms-sideF : (n : ℕ) (a : _) (i j k : I)  → Susp' (WedgeDecomp n , inl (inr 𝕤))
-- --   comms-sideF n a i j k =
-- --     hfill (λ k → λ {(i = i0) → WedegeDecompFun n
-- --                                   (inl (compPath-filler (λ j → inl (push (∣ f ∣ (suc (suc n)) a) (~ j))) (push tt) (~ j) (~ k)))
-- --                    ; (i = i1) → WedegeDecompFun n (compPath-filler' (push tt) (λ j → inr (push (∣ g ∣ (suc (suc n)) a) j)) (~ j) k)
-- --                    ; (j = i0) → WedegeDecompFun n (pushoutA*→WedgeDecompF (suc n) a i k)
-- --                    ; (j = i1) → doubleCompPath-filler (𝕝 (inl (inl (inr (∣ f ∣ (suc (suc n)) a))))) (sym refl) (𝕝 (inr (inr (∣ g ∣ (suc (suc n)) a))) ⁻¹) (~ k) i
-- --                    })
-- --           (inS (((𝕝 (inl (inl (inr (∣ f ∣ (suc (suc n)) a)))))
-- --            ∙∙ 𝕔 j  ⁻¹
-- --            ∙∙ (𝕝 (inr (inr (∣ g ∣ (suc (suc n)) a))) ⁻¹)) i)) k

-- --   comms-side : (n : ℕ) (x : _) → WedegeDecompFun n (pushoutA*→WedgeDecomp (suc n) x) ≡ 𝕤
-- --   comms-side n (inl x) = refl
-- --   comms-side n (inr x) = refl
-- --   comms-side n (push a i) j = comms-sideF n a i j i1
-- --   {-
-- --     WedegeDecompFun n (hcomp (λ k → λ {(i = i0) → pushoutA*→WedgeDecompF (suc n) a i0 j
-- --                    ; (i = i1) → pushoutA*→WedgeDecompF (suc n) a i1 j
-- --                    ; (j = i0) → ?
-- --                    ; (j = i1) → pushoutA*→WedgeDecompF (suc n) a i i1})
-- --           (pushoutA*→WedgeDecompF (suc n) a i j))
-- -- -}


  

-- --   suspFun' : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Type ℓ'} → (f : fst A → B) → Susp' A → Susp' (B , f (pt A))
-- --   suspFun' f 𝕤 = 𝕤
-- --   suspFun' f (𝕝 x i) = 𝕝 (f x) i
-- --   suspFun' f (𝕔 i i₁) = 𝕔 i i₁

-- --   projOutB' :  (n : ℕ)  → WedgeDecomp n → (Susp' (cofibCW∙ n B))
-- --   projOutB' n (inl (inl x)) = 𝕤
-- --   projOutB' n (inl (inr x)) = x
-- --   projOutB' n (inl (push a i)) = 𝕤
-- --   projOutB' n (inr x) = 𝕤
-- --   projOutB' n (push a i) = 𝕤

-- --   projOutB : (n : ℕ) → Susp' (WedgeDecomp n , inl (inr 𝕤)) → Susp' (Susp' (cofibCW∙ n B) , 𝕤)
-- --   projOutB n 𝕤 = 𝕤
-- --   projOutB n  (𝕝 x₁ i) = 𝕝 (projOutB' n x₁) i
-- --   projOutB n  (𝕔 i i₁) = 𝕔 i i₁



-- --   comms? : (n : ℕ) (x : _) → compWithProjB n (toWedgeDecomp (suc n) x)
-- --                              ≡ projOutB n (suspFun' (toWedgeDecomp n) (↓P (suc n) x))
-- --   comms? n (inl x) = refl
-- --   comms? n (inr (inl x)) = refl
-- --   comms? n (inr (inr x)) = refl
-- --   comms? n (inr (push a i)) = {!!}
-- --   comms? n (push (inl x) i) j = {!!}
-- --   comms? n (push (inr x) i) j = {!!}
-- --   comms? n (push (push a j) k) w = {!!}
  

-- -- --   comms? : (n : ℕ) (x : _) → projOutB n (WedegeDecompFun n (toWedgeDecomp (suc n) x))
-- -- --                              ≡ projOutB n (suspFun' (toWedgeDecomp n) (↓P (suc n) x))
-- -- --   comms? n (inl x) = refl
-- -- --   comms? n (inr (inl x)) = refl
-- -- --   comms? n (inr (inr x)) = refl
-- -- --   comms? n (inr (push x i)) = {!!}
-- -- --     where
-- -- --     help : cong (λ x → projOutB n (WedegeDecompFun n (toWedgeDecomp (suc n) (inr x)))) (push x) -- (push x)
-- -- --          ≡ (λ i → projOutB n (suspFun' (toWedgeDecomp n) (↓P (suc n) (inr (push x i)))))
-- -- --     help = {!!} ∙ {!!}
-- -- --   comms? n (push (inl x) i) = {!!}
-- -- --   comms? n (push (inr x) i) = {!!}
-- -- --   comms? n (push (push a i₁) i) = {!!}


-- -- -- --   comms? n (inl x) = refl
-- -- -- --   comms? n (inr x) = comms-side n x
-- -- -- --   comms? n (push (inl x) i) j =
-- -- -- --     WedegeDecompFun n (inl (compPath-filler (λ j → inl (push x (~ j))) (push tt) (~ j) (~ i)))
-- -- -- --   comms? n (push (inr x) i) j =
-- -- -- --     WedegeDecompFun n (compPath-filler' (push tt) (λ j → inr (push x j)) (~ j) i)
-- -- -- --   comms? n (push (push a i) j) k =
-- -- -- --     hcomp (λ r → λ {(i = i0) → WedegeDecompFun n (inl
-- -- -- --                                  (compPath-filler (λ j → inl (push (inl (∣ f ∣ (suc n) a)) (~ j)))
-- -- -- --                                  (push tt) (~ k) (~ j ∨ ~ i1))) 
-- -- -- --                   ; (i = i1) → WedegeDecompFun n (compPath-filler' (push tt) (λ j → inr (push (inl (∣ g ∣ (suc n) a)) j)) (~ k) (j ∧ i1)) -- 
-- -- -- --                   ; (j = i0) → 𝕤
-- -- -- --                   ; (j = i1) → comms-sideF n (inl a) i k i1 -- comms-sideF n (inl a) i k r
-- -- -- --                   ; (k = i0) → rewrLeft (~ r) i j
-- -- -- --                   ; (k = i1) → rewrRight (~ r) i j}) -- 𝕝 (pushoutA*→WedgeDecompF n a i r) j})
-- -- -- --    (
-- -- -- --     hcomp (λ r → λ {(i = i0) → WedegeDecompFun n (inl (compPath-filler (λ j → inl (push (inl (∣ f ∣ (suc n) a)) (~ j))) (push tt) (~ k ) (~ j ∨ ~ r)))  -- 
-- -- -- --                   ; (i = i1) → WedegeDecompFun n (compPath-filler' (push tt) (λ j → inr (push (inl (∣ g ∣ (suc n) a)) j)) (~ k) (j ∧ r)) --  -- 
-- -- -- --                   ; (j = i0) → WedegeDecompFun n (inl (inr (𝕔 r i)))
-- -- -- --                   ; (j = i1) → comms-sideF n (inl a) i k r
-- -- -- --                   ; (k = i0) → k0 r i j
-- -- -- --                   ; (k = i1) → {! -- comms-sideF n (inl a) i k r!}
-- -- -- --                   }) -- comms-sideF n (inl a) i k r} -- comms-sideF n (inl a) i k r}) -- 𝕝 (pushoutA*→WedgeDecompF n a i r) j})
-- -- -- --           ((𝕝 (inl (inl (push (∣ f ∣ (suc n) a) j)))
-- -- -- --           ∙∙ sym (𝕔 (k ∧ j))
-- -- -- --           ∙∙ (𝕝 ( (inr (push (∣ g ∣ (suc n) a) j))) ⁻¹)) i))
-- -- -- --      where -- r i j
-- -- -- --      rewrLeft : Path (Square _ _ _ _) (λ i j → WedegeDecompFun n (toWedgeDecomp (suc n) (push (push a i) j)))
-- -- -- --                                       _
-- -- -- --      rewrLeft = cong-hcomp (WedegeDecompFun n) ∙ refl

-- -- -- --      rewrRight : Path (Square {A = (Susp' (_ , inl (inr 𝕤)))} _ _ _ _) (cong 𝕝 (λ j → pushoutA*→WedgeDecompF n a j i1)) _
-- -- -- --      rewrRight = cong-∙∙ 𝕝 _ _ _

-- -- -- --      k0 : Cube (λ i j → (𝕝 (inl (inl (push (∣ f ∣ (suc n) a) j)))
-- -- -- --           ∙∙ sym (𝕝 (inl (inr 𝕤)))
-- -- -- --           ∙∙ (𝕝 ( (inr (push (∣ g ∣ (suc n) a) j))) ⁻¹)) i)
-- -- -- --                (λ i j → rewrLeft i1 i j)
-- -- -- --                (λ r j → WedegeDecompFun n
-- -- -- --                         (inl
-- -- -- --                          (compPath-filler (λ j₁ → inl (push (inl (∣ f ∣ (suc n) a)) (~ j₁)))
-- -- -- --                           (push tt) (~ i0) (~ j ∨ ~ r))) )
-- -- -- --                (λ r j → WedegeDecompFun n
-- -- -- --                           (compPath-filler' (push tt)
-- -- -- --                            (λ j₂ → inr (push (inl (∣ g ∣ (suc n) a)) j₂)) (~ i0) (j ∧ r)))
-- -- -- --                (λ r i → WedegeDecompFun n (inl (inr (𝕔 r i))))
-- -- -- --                 (λ r i → comms-sideF n (inl a) i i0 r)
               
-- -- -- --      k0 r i j = hcomp (λ k → λ {(i = i0) → {!!}
-- -- -- --                   ; (i = i1) → {!!}
-- -- -- --                   ; (j = i0) → {!!}
-- -- -- --                   ; (j = i1) → {!!}
-- -- -- --                   ; (r = i0) → {!!}})
-- -- -- --             {!rewrLeft i1 i i1!}
  

-- -- -- --   {-

-- -- -- -- {-
-- -- -- -- strictPushout
-- -- -- -- -}

-- -- -- --   strictPushoutIso : (n : ℕ) → Iso (strictPushout n) (pushoutA* (suc (suc n)))
-- -- -- --   Iso.fun (strictPushoutIso n) (inl (inl x)) = inl (inl x)
-- -- -- --   Iso.fun (strictPushoutIso n) (inl (inr x)) = inl (inr x)
-- -- -- --   Iso.fun (strictPushoutIso n) (inl (push (a , b) i)) = inl (push (a , Iso.inv (IsoSphereSusp n) b) i)
-- -- -- --   Iso.fun (strictPushoutIso n) (inr (inl x)) = inr (inl x)
-- -- -- --   Iso.fun (strictPushoutIso n) (inr (inr x)) = inr (inr x)
-- -- -- --   Iso.fun (strictPushoutIso n) (inr (push (a , b) i)) = inr (push ( (a , Iso.inv (IsoSphereSusp n) b)) i)
-- -- -- --   Iso.fun (strictPushoutIso n) (push (inl x) i) = push (inl x) i
-- -- -- --   Iso.fun (strictPushoutIso n) (push (inr x) i) = push (inr x) i
-- -- -- --   Iso.fun (strictPushoutIso n) (push (push (a , s) j) i) =
-- -- -- --     hcomp (λ k → λ {(i = i0) → {!inl (inl (strictMap f (suc n) (push (a , s) j)))!} ; (i = i1) → {!!} ; (j = i0) → {!!} ; (j = i1) → {!!}})
-- -- -- --       (push (push (a , s) j) i)
-- -- -- --   Iso.inv (strictPushoutIso n) x = {!!}
-- -- -- --   Iso.rightInv (strictPushoutIso n) = {!!}
-- -- -- --   Iso.leftInv (strictPushoutIso n) = {!!}
-- -- -- -- -}
