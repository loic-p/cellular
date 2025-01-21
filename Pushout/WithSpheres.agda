{-# OPTIONS --cubical --lossy-unification --allow-unsolved-metas #-}
module Pushout.WithSpheres where

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

module _ where
PushoutA→PushoutPushoutMapLRGen0 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (inl* : A → B) {x : A}
  → {fml fmr frr : A}  (f-l : x ≡ fml) (f-m : fml ≡ fmr) (f-r : fmr ≡ frr)
  → {tml tmr : A}  (t-l : x ≡ tml) (t-m : tml ≡ tmr) (t-r : tmr ≡ frr)
  {t : B}
  (push-inr-base  : inl* x ≡ t)
  (bot : Square (sym push-inr-base) (sym push-inr-base) refl
                (cong inl* ((f-l ∙∙ f-m ∙∙ f-r) ∙∙ refl ∙∙ sym (t-l ∙∙ t-m ∙∙ t-r))))
  → (i j k : I) → B
PushoutA→PushoutPushoutMapLRGen0 inl* f-l f-m f-r t-l t-m t-r push-inr-base bot i j k =
  hfill (λ k → λ {(i = i0) → invSides-filler push-inr-base (cong inl* ((f-l ∙∙ f-m ∙∙ f-r))) j (~ k)
                 ; (i = i1) → invSides-filler push-inr-base (cong inl* ((t-l ∙∙ t-m ∙∙ t-r))) j (~ k)
                 ; (j = i0) → push-inr-base (~ k)
                 ; (j = i1) → inl* (doubleCompPath-filler
                                      (f-l ∙∙ f-m ∙∙ f-r)
                                      refl
                                      (sym (t-l ∙∙ t-m ∙∙ t-r)) (~ k) i)})
        (inS (bot i j))
        k
cong-PushoutA→PushoutPushoutMapLRGen0 : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (f : B → C) (inl* : A → B) {x : A}
  → {fml fmr frr : A}  (f-l : x ≡ fml) (f-m : fml ≡ fmr) (f-r : fmr ≡ frr)
  → {tml tmr : A}  (t-l : x ≡ tml) (t-m : tml ≡ tmr) (t-r : tmr ≡ frr)
     {t : B}
     (push-inr-base  : inl* x ≡ t)
     (bot : Square (sym push-inr-base) (sym push-inr-base) refl
                   (cong inl* ((f-l ∙∙ f-m ∙∙ f-r) ∙∙ refl ∙∙ sym (t-l ∙∙ t-m ∙∙ t-r))))
     → Cube {A = C}
            (λ i j → f (PushoutA→PushoutPushoutMapLRGen0 inl* f-l f-m f-r t-l t-m t-r
                         push-inr-base bot i j i1))
            (λ i j → PushoutA→PushoutPushoutMapLRGen0 (f ∘ inl*)
                         f-l f-m f-r t-l t-m t-r (cong f push-inr-base) (λ i j → f (bot i j)) i j i1)
            refl refl (λ _ _ → f (inl* x)) λ _ _ → f (inl* frr)
cong-PushoutA→PushoutPushoutMapLRGen0 f inl*
  f-l f-m f-r t-l t-m t-r push-inr-base bot = cong-hcomp f
    ∙ λ r i j → hcomp (λ k
              → λ {(i = i0) → cong-invSides-filler f push-inr-base (cong inl* ((f-l ∙∙ f-m ∙∙ f-r))) r j (~ k)
                  ; (i = i1) → cong-invSides-filler f push-inr-base (cong inl* ((t-l ∙∙ t-m ∙∙ t-r))) r j (~ k)
                  ; (j = i0) → f (push-inr-base (~ k))
                  ; (j = i1) → f (inl* (doubleCompPath-filler
                                       (f-l ∙∙ f-m ∙∙ f-r)
                                       refl
                                       (sym (t-l ∙∙ t-m ∙∙ t-r)) (~ k) i))})
         ((f (bot i j)))

PushoutA→PushoutPushoutMapLRGen>1 : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (inl* : A → B) {x y z w : A}
  → (inl-push-t-s : y ≡ x) (psh : y ≡ z) (inr-push-t-s : w ≡ z)
  {t : B}
  (push-inr-north  : inl* x ≡ t) (push-inr-south : inl* w ≡ t)
  (bot : Square push-inr-north push-inr-south (cong inl* (sym inl-push-t-s ∙∙ psh ∙∙ sym inr-push-t-s)) refl) -- 
  → (i j k : I) → B
PushoutA→PushoutPushoutMapLRGen>1 inl* inl-push-t-s psh inr-push-t-s {t = t} push-inr-north push-inr-south bot i j k =
  hfill (λ k → λ {(i = i0) → inl* (doubleCompPath-filler (sym inl-push-t-s) psh (sym inr-push-t-s) (~ k) j)
                 ; (i = i1) → doubleCompPath-filler push-inr-north refl (sym push-inr-south) k j
                 ; (j = i0) → invSides-filler push-inr-north (cong inl* (sym inl-push-t-s)) k i
                 ; (j = i1) → invSides-filler push-inr-south (cong inl* inr-push-t-s) k i}) -- (cong inl* inr-push-t-s) k i})
        (inS (bot j i))
        k

cong-PushoutA→PushoutPushoutMapLRGen>1 :
  ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : B → C) (inl* : A → B) {x y z w : A}
   (inl-push-t-s : y ≡ x) (psh : y ≡ z) (inr-push-t-s : w ≡ z)
   {t : B}
   (push-inr-north  : inl* x ≡ t) (push-inr-south : inl* w ≡ t)
   (bot : Square push-inr-north push-inr-south
                 (cong inl* (sym inl-push-t-s ∙∙ psh ∙∙ sym inr-push-t-s)) refl)
    → Cube {A = C} (λ i j → f (PushoutA→PushoutPushoutMapLRGen>1 inl* inl-push-t-s
                                psh inr-push-t-s {t = t} push-inr-north push-inr-south bot i j i1))
         (λ i j → PushoutA→PushoutPushoutMapLRGen>1 (f ∘ inl*)
                   inl-push-t-s psh inr-push-t-s (cong f push-inr-north) (cong f push-inr-south)
                     (λ i j → f (bot i j)) i j i1)
         (λ _ j → f (inl* (psh j)))
         (cong-∙∙ f push-inr-north refl (sym push-inr-south))
         (λ _ i → f (inl* (inl-push-t-s i)))
         λ _ i → f (inl* (inr-push-t-s (~ i)))
cong-PushoutA→PushoutPushoutMapLRGen>1 {C = C} f inl* inl-push-t-s psh inr-push-t-s push-inr-north push-inr-south bot i j k =
  hcomp (λ r → λ {(i = i0) → f (PushoutA→PushoutPushoutMapLRGen>1 inl* inl-push-t-s psh
                                 inr-push-t-s push-inr-north push-inr-south bot j k r)
                 ; (i = i1) → PushoutA→PushoutPushoutMapLRGen>1 (f ∘ inl*)
                                inl-push-t-s psh inr-push-t-s
                                (cong f push-inr-north) (cong f push-inr-south)
                                  (λ i j → f (bot i j)) j k r
                 ; (j = i0) → f (inl* (doubleCompPath-filler (λ i₁ → inl-push-t-s (~ i₁)) psh
                                      (λ i₁ → inr-push-t-s (~ i₁)) (~ r) k))
                 ; (k = i0) → slem i r j
                 ; (k = i1) → slem2 i r j})
          (f (bot k j))
   where
   slem : Path (Square {A = C} _ _ _ _)
     (λ r j → f
       (PushoutA→PushoutPushoutMapLRGen>1 inl* inl-push-t-s psh
        inr-push-t-s push-inr-north push-inr-south bot j i0 r))
     (λ r j → PushoutA→PushoutPushoutMapLRGen>1 (λ x₁ → f (inl* x₁))
       inl-push-t-s psh inr-push-t-s (λ i₁ → f (push-inr-north i₁))
       (λ i₁ → f (push-inr-south i₁)) (λ i₁ j₁ → f (bot i₁ j₁)) j i0 r)
   slem = cong-hcomp f

   slem2 : Path (Square {A = C} _ _ _ _)
     (λ r j → f
       (PushoutA→PushoutPushoutMapLRGen>1 inl* inl-push-t-s psh
        inr-push-t-s push-inr-north push-inr-south bot j i1 r))
     (λ r j → PushoutA→PushoutPushoutMapLRGen>1 (λ x₁ → f (inl* x₁))
       inl-push-t-s psh inr-push-t-s (λ i₁ → f (push-inr-north i₁))
       (λ i₁ → f (push-inr-south i₁)) (λ i₁ j₁ → f (bot i₁ j₁)) j i1 r)
   slem2 = cong-hcomp f


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

{-

    doubleCompPath-filler ((λ i → inl (∣ f ∣ (suc (suc zero)) (invEq (e B (suc zero)) (push (b , x) (~ i))))))
      {!!} -- (push (α B (suc zero) (b , x)))
      ((λ i → inl (∣ f ∣ (suc (suc zero)) (invEq (e B (suc zero)) (push (b , x) (~ i)))))) k i
-}

  -- pushoutMapₛ-filler₁ : (x : A B (suc zero)) (b : Bool)
  --                    → I → I → pushoutA (suc zero)
  -- pushoutMapₛ-filler₁ x b i k =
  --   {!doubleCompPath-filler (λ i → inl (∣ f ∣ 2 (invEq (e B 1) (push (x , b) (~ i)))))
  --    (λ i → ((push (α B (suc zero) (x , b))) i))
  --    (λ i → (inr (∣ g ∣ 2 (invEq (e B 1) (push (x , b) i))))) k i!}

  pushoutMapₛ-filler : (n : ℕ) → (A B (suc n)) → S₊ n
                     → I → I → pushoutA (suc (suc n))
  pushoutMapₛ-filler n b x i k =
    doubleCompPath-filler ((λ i → inl (∣ f ∣ (suc (suc n)) (invEq (e B (suc n)) (push (b , x) (~ i))))))
      (push (α B (suc n) (b , x)))
      (λ i → inr (∣ g ∣ (suc (suc n)) (invEq (e B (suc n)) (push (b , x) i)))) k i

  pushoutMapₛ : (n : ℕ) → (((A C (suc n)) ⊎ (A D (suc n))) ⊎ (A B n)) × S₊ n → pushoutA (suc n)
  pushoutMapₛ n (inl (inl x) , y) = inl (α C (suc n) (x , y))
  pushoutMapₛ n (inl (inr x) , y) = inr (α D (suc n) (x , y))
  pushoutMapₛ zero (inr x , false) = inl (∣ f ∣ (suc zero) (invEq (e B zero) (inr x)))
  pushoutMapₛ zero (inr x , true) = inr (∣ g ∣ (suc zero) (invEq (e B zero) (inr x)))
  pushoutMapₛ (suc zero) (inr x , base) = inl (∣ f ∣ (suc (suc zero)) (invEq (e B (suc zero)) (inr x)))
  pushoutMapₛ (suc zero) (inr x , loop i) =
     ((λ i → pushoutMapₛ-filler zero x false i i1) ∙∙ refl ∙∙ λ i → pushoutMapₛ-filler zero x true (~ i) i1) i
  pushoutMapₛ (suc (suc n)) (inr b , north) = inl (∣ f ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (inr b)))
  pushoutMapₛ (suc (suc n)) (inr b , south) = inr (∣ g ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (inr b)))
  pushoutMapₛ (suc (suc n)) (inr b , merid a i) = pushoutMapₛ-filler (suc n) b a i i1

  pushoutMidCells : ℕ → ℕ
  pushoutMidCells zero = 0
  pushoutMidCells (suc n) = (card B n)  

  pushoutCells : ℕ → ℕ
  pushoutCells n = (card C n) +ℕ (card D n) + pushoutMidCells n

  pushoutMap₀ : (Fin (pushoutCells zero)) × (S⁻ 0) → pushoutA 0
  pushoutMap₀ ()

  pushoutMap' : (n : ℕ) → (Fin (pushoutCells (suc n))) × (S₊ n) → pushoutA (suc n)
  pushoutMap' n (a , x) = pushoutMapₛ n (finSplit3 (card C (suc n)) (card D (suc n)) (card B n) a , x)

  pushoutα> : (n : ℕ) → Fin (card C (suc n) + card D (suc n) + card B n) × S₊ n
                       → pushoutA (suc n)
  pushoutα> n (x , y) =
    pushoutMapₛ n ((finSplit3 (card C (suc n)) (card D (suc n)) (card B n) x)
                 , y)

  Iso-Pushoutα-PushoutPushoutMapₛ : (n : ℕ)
    → Iso (Pushout (pushoutMapₛ n) fst)
           (Pushout (pushoutα> n) fst)
  Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ n) (inl x) = inl x
  Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ n) (inr x) = inr (invEq (finSplit3≃ _ _ _) x)
  Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ n) (push a i) =
    ((λ j → inl (pushoutMapₛ n (secEq  (finSplit3≃ _ _ _) (fst a) (~ j)
                               , snd a)))
      ∙ push ((invEq (finSplit3≃ _ _ _)  (fst a))
                , snd a)) i
  Iso.inv (Iso-Pushoutα-PushoutPushoutMapₛ n) (inl x) = inl x
  Iso.inv (Iso-Pushoutα-PushoutPushoutMapₛ n) (inr x) = inr (finSplit3 _ _ _ x)
  Iso.inv (Iso-Pushoutα-PushoutPushoutMapₛ n) (push a i) =
    (push ((finSplit3 _ _ _ (fst a))
          , (snd a))) i
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
    (push (((inl (inl (fst a)))) , snd a)) i

  PushoutA→PushoutPushoutMapR : (n : ℕ) → Pushout (α D (suc n)) fst → Pushout (pushoutMapₛ n) fst
  PushoutA→PushoutPushoutMapR n (inl x) = inl (inr x)
  PushoutA→PushoutPushoutMapR n (inr x) = inr ((inl (inr x)))
  PushoutA→PushoutPushoutMapR n (push a i) =
    (push (((inl (inr (fst a)))) , (snd a))) i





  PushoutA→PushoutPushoutMapLR-push-filler₀bot : (t : A B (suc zero)) (i j k : I) → Pushout (pushoutMapₛ (suc zero)) fst
  PushoutA→PushoutPushoutMapLR-push-filler₀bot t i j k =
    PushoutA→PushoutPushoutMapLRGen0 inl
      (λ i₁ → inl (∣ f ∣ 2 (invEq (e B 1) (push (t , false) (~ i₁)))))
      (push (α B 1 (t , false)))
      (λ i₁ → inr (∣ g ∣ 2 (invEq (e B 1) (push (t , false) i₁))))
      (λ i₁ → inl (∣ f ∣ 2 (invEq (e B 1) (push (t , true) (~ i₁)))))
      (push (α B 1 (t , true)))
      (λ i₁ → inr (∣ g ∣ 2 (invEq (e B 1) (push (t , true) i₁))))
      (push (inr t , base)) (λ i j → push (inr t , loop i) (~ j)) i j i1
  {-
        hfill (λ k → λ {(i = i0) → invSides-filler (push (inr t , base)) (λ i → inl (pushoutMapₛ-filler zero t false i i1)) j (~ k)
                   ; (i = i1) → invSides-filler (push (inr t , base)) (λ i → inl (pushoutMapₛ-filler zero t true i i1)) j (~ k)
                   ; (j = i0) →  push (inr t , base) (~ k)
                   ; (j = i1) → inl ((doubleCompPath-filler (λ i₁ → pushoutMapₛ-filler zero t false i₁ i1)
                                        refl
                                        (λ i₁ → pushoutMapₛ-filler zero t true (~ i₁) i1) (~ k) i))})
           (inS (push (inr t , loop i) (~ j)))
           k
           -}
  {-

-}
  PushoutA→PushoutPushoutMapLR-push-filler : (n : ℕ) (t : A B (suc n)) (s : S₊ n) → (i j k : I) → Pushout (pushoutMapₛ (suc n)) fst
  PushoutA→PushoutPushoutMapLR-push-filler zero t false i j k =
    hfill (λ k → λ {(i = i0) → inl (pushoutMapₛ-filler zero t false j (~ k))
                   ; (i = i1) → inl (pushoutMapₛ-filler zero t true j i1)
                   ; (j = i0) → inl (inl (∣ f ∣ 2 (invEq (e B 1) (push (t , false) (i ∨ ~ k)))))
                   ; (j = i1) → inl (inr (∣ g ∣ 2 (invEq (e B 1) (push (t , false) (i ∨ ~ k)))))})
     (inS (PushoutA→PushoutPushoutMapLR-push-filler₀bot t i j i1))
     k
  PushoutA→PushoutPushoutMapLR-push-filler zero t true i j k = inl (pushoutMapₛ-filler zero t true j i)
  PushoutA→PushoutPushoutMapLR-push-filler (suc n) t s i j k =
    PushoutA→PushoutPushoutMapLRGen>1
      inl
      (λ i → inl (∣ f ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (t , s) i))))
      (push (α B (suc (suc n)) (t , s)))
      (λ i → inr (∣ g ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (t , s) (~ i)))))
      (push (inr t , north))
      (push (inr t , south))
      (λ j i → (push (inr t , merid s j)) i)
      i j k

  PushoutA→PushoutPushoutMapLR : (n : ℕ) (b : Pushout (α B n) fst)
    → Path (Pushout (pushoutMapₛ n) fst)
            (inl (inl (∣ f ∣ (suc n) (invEq (e B n) b))))
            (inl (inr (∣ g ∣ (suc n) (invEq (e B n) b))))
  PushoutA→PushoutPushoutMapLR n (inl x) i = inl (push x i)
  PushoutA→PushoutPushoutMapLR zero (inr x) =
    push ((inr x) , false) ∙∙ refl ∙∙ sym (push ((inr x) , true))
  PushoutA→PushoutPushoutMapLR (suc zero) (inr x) i =
    inl (pushoutMapₛ-filler zero x true i i1)
  PushoutA→PushoutPushoutMapLR (suc (suc n)) (inr x) =
    push ((inr x) , north) ∙∙ refl ∙∙ sym (push ((inr x) , south))
  PushoutA→PushoutPushoutMapLR (suc zero) (push (t , true) i) j =
    inl (pushoutMapₛ-filler zero t true j i)
  PushoutA→PushoutPushoutMapLR (suc zero) (push (t , false) i) j =
    PushoutA→PushoutPushoutMapLR-push-filler zero t false i j i1 
  PushoutA→PushoutPushoutMapLR (suc (suc n)) (push (t , s) i) j =
    PushoutA→PushoutPushoutMapLR-push-filler (suc n) t s i j i1

  cofib→wedgeInrσ : (n : ℕ) (x : S₊ n) (y : A B n) → _
  cofib→wedgeInrσ n x y = preBTC n (card B n) (α B n) (e B n) y .fst x

  Pushout→B : (n : ℕ) → Pushout (pushoutMapₛ (suc n)) fst → Susp (cofibCW (suc n) B)
  Pushout→B n (inl x) = north
  Pushout→B n (inr x) = south
  Pushout→B n (push (inl (inl x) , s) i) = merid (inl tt) i
  Pushout→B n (push (inl (inr x) , s) i) = merid (inl tt) i
  Pushout→B n (push (inr x , s) i) = merid (cofib→wedgeInrσ (suc n) s x) i

  Pushout→B' : (n : ℕ) → Pushout ((α B (suc n))) fst → cofibCW (suc n) B
  Pushout→B' n x = inr (invEq (e B (suc n)) x)

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


  pushoutA↑ : (n : ℕ) → (pushoutA (suc n)) → (pushoutA (suc (suc n)))
  pushoutA↑ n (inl x) = inl (CW↪ C (suc n) x)
  pushoutA↑ n (inr x) = inr (CW↪ D (suc n) x)
  pushoutA↑ n (push a i) =
    ((λ i → inl (comm f (suc n) (CW↪ B n a) i))
    ∙∙ push (CW↪ B n a)
    ∙∙ λ i → inr (comm g (suc n) (CW↪ B n a) (~ i))) i


  module _ (n : ℕ) (x : _) (a : _) where
    PushoutPushoutMap→PushoutABotFillSide-filler : (i j k : _) → pushoutA (suc (suc n))
    PushoutPushoutMap→PushoutABotFillSide-filler i j k =
      hfill (λ k → λ {(i = i0) → push (invEq (e B n) (push (x , a) k)) j
                    ; (i = i1) → pushoutA↑ n
                      (doubleCompPath-filler
                        (λ i → inl (∣ f ∣ (suc n) (invEq (e B n) (push (x , a) (~ i)))))
                        (push (α B n (x , a)))
                        (λ i → inr (∣ g ∣ (suc n) (invEq (e B n) (push (x , a) i)))) k j)
                    ; (j = i0) → inl (comm f (suc n) (invEq (e B n) (push (x , a) k)) (~ i))
                    ; (j = i1) → inr (comm g (suc n) (invEq (e B n) (push (x , a) k)) (~ i))})
               (inS (doubleCompPath-filler
                 (λ i₂ → inl (comm f (suc n) (CW↪ B n (α B n (x , a))) i₂))
                 (push (CW↪ B n (α B n (x , a))))
                 (λ i₂ → inr (comm g (suc n) (CW↪ B n (α B n (x , a))) (~ i₂))) i j))
                 k


    PushoutPushoutMap→PushoutABotFill-filler : (i j k : _) → pushoutA (suc (suc n))
    PushoutPushoutMap→PushoutABotFill-filler i j k =
      hfill (λ k → λ {(i = i0) → PushoutPushoutMap→PushoutABotFillSide-filler k j i1
                    ; (i = i1) → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ k))
                    ; (j = i0) → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ k))
                    ; (j = i1) → doubleCompPath-filler
                                    (λ i → inr (comm g (suc n) (invEq (e B n) (inr x)) i))
                                    (sym (push (invEq (e B n) (inr x))))
                                    (λ i₁ → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ i₁))) k i})
              (inS (push (invEq (e B n) (inr x)) (~ i ∧ j)))
              k
    {-
      hfill (λ k → λ {(i = i0) → PushoutPushoutMap→PushoutABotFillSide-filler k j i1
                    ; (i = i1) → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ k))
                    ; (j = i0) → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ k))
                    ; (j = i1) → doubleCompPath-filler
                                    (λ i → inr (comm g (suc n) (invEq (e B n) (inr x)) i))
                                    (sym (push (invEq (e B n) (inr x))))
                                    (λ i₁ → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ i₁))) k i})
              (inS (push (invEq (e B n) (inr x)) (~ i ∧ j)))
              k
-}
  PushoutPushoutMap→PushoutABot :
    (n : ℕ) (x : A B n) (s : S₊ n)
    → Path (pushoutA (suc (suc n))) (pushoutA↑ n (pushoutMapₛ n (inr x , s)))
            (inl (CW↪ C (suc n) ((∣ f ∣ (suc n) (invEq (e B n) (inr x))))))
  PushoutPushoutMap→PushoutABot zero x false = refl
  PushoutPushoutMap→PushoutABot zero x true =
    (λ i → inr (comm g (suc zero) (invEq (e B zero) (inr x)) i))
    ∙∙ sym (push (invEq (e B zero) (inr x)))
    ∙∙ (λ i → inl (comm f (suc zero) (invEq (e B zero) (inr x)) (~ i)))
  PushoutPushoutMap→PushoutABot (suc zero) x base = refl
  PushoutPushoutMap→PushoutABot (suc zero) x (loop i) j = --{!!}
    hcomp (λ k → λ {(i = i0) → pushoutA↑ (suc zero) (pushoutMapₛ-filler zero x false (~ k) i1)
                   ; (i = i1) → PushoutPushoutMap→PushoutABotFill-filler (suc zero) x true j (~ k) i1
                   ; (j = i0) → pushoutA↑ (suc zero)
                                  (doubleCompPath-filler (λ i → pushoutMapₛ-filler zero x false i i1)
                                                    refl (λ i → pushoutMapₛ-filler zero x true (~ i) i1) k i)
                   ; (j = i1) → PushoutPushoutMap→PushoutABotFill-filler (suc zero) x false i (~ k) i1
                   })
    ((PushoutPushoutMap→PushoutABotFill-filler 1 x false (i ∧ j) i1 i1))
  PushoutPushoutMap→PushoutABot (suc (suc n)) x north = refl
  PushoutPushoutMap→PushoutABot (suc (suc n)) x south =
        (λ i → inr (comm g (suc (suc (suc n))) (invEq (e B (suc (suc n))) (inr x)) i))
    ∙∙ sym (push (invEq (e B (suc (suc n))) (inr x)))
    ∙∙ (λ i → inl (comm f (suc (suc (suc n))) (invEq (e B (suc (suc n))) (inr x)) (~ i)))
  PushoutPushoutMap→PushoutABot (suc (suc n)) x (merid a i) j =
    PushoutPushoutMap→PushoutABotFill-filler (suc (suc n)) x a j i i1

  PushoutPushoutMap→PushoutA : (n : ℕ) → (Pushout (pushoutMapₛ n) fst) → (pushoutA (suc (suc n)))
  PushoutPushoutMap→PushoutA n (inl x) = pushoutA↑ n x
  PushoutPushoutMap→PushoutA n (inr (inl (inl x))) = inl (invEq (e C (suc n)) (inr x))
  PushoutPushoutMap→PushoutA n (inr (inl (inr x))) = inr (invEq (e D (suc n)) (inr x))
  PushoutPushoutMap→PushoutA n (inr (inr x)) = inl (CW↪ C (suc n) ((∣ f ∣ (suc n) (invEq (e B n) (inr x))))) --  
  PushoutPushoutMap→PushoutA n (push (inl (inl x) , b) i) =
    inl (invEq (e C (suc n)) ((push (x , b)) i))
  PushoutPushoutMap→PushoutA n (push (inl (inr x) , b) i) =
    inr (invEq (e D (suc n)) ((push (x , b)) i))
  PushoutPushoutMap→PushoutA n (push (inr x , b) i) = PushoutPushoutMap→PushoutABot n x b i


module _ {ℓ ℓ' ℓ'' : Level} {B' : CWskel ℓ} {C' : CWskel ℓ'} {D' : CWskel ℓ''}
  (f : cellMap (strictCWskel B') (strictCWskel C'))
  (g : cellMap (strictCWskel B') (strictCWskel D')) where
  private
    B = strictCWskel B'
    C = strictCWskel C'
    D = strictCWskel D'

  PushoutPushoutMap→PushoutA→PushoutPushoutMap-inl : (n : ℕ) (x : _)
    → PushoutPushoutMap→PushoutA f g n (PushoutA→PushoutPushoutMap f g n (inl x)) ≡ (inl x)
  PushoutPushoutMap→PushoutA→PushoutPushoutMap-inl n (inl x) = refl
  PushoutPushoutMap→PushoutA→PushoutPushoutMap-inl n (inr x) = refl
  PushoutPushoutMap→PushoutA→PushoutPushoutMap-inl n (push a i) = refl

  PushoutPushoutMap→PushoutA→PushoutPushoutMap-inr : (n : ℕ) (x : _)
    → PushoutPushoutMap→PushoutA f g n (PushoutA→PushoutPushoutMap f g n (inr x)) ≡ (inr x)
  PushoutPushoutMap→PushoutA→PushoutPushoutMap-inr n (inl x) = refl
  PushoutPushoutMap→PushoutA→PushoutPushoutMap-inr n (inr x) = refl
  PushoutPushoutMap→PushoutA→PushoutPushoutMap-inr n (push a i) = refl


  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)


  PushoutPushoutMap→PushoutA→PushoutPushoutMap : (n : ℕ) (x : _)
    → Square (cong (PushoutPushoutMap→PushoutA f g n ∘ PushoutA→PushoutPushoutMap f g n ) (push x))
              (push x)
              (PushoutPushoutMap→PushoutA→PushoutPushoutMap-inl n (∣ f ∣ (suc (suc n)) (inl x)))
              (PushoutPushoutMap→PushoutA→PushoutPushoutMap-inr n (∣ g ∣ (suc (suc n)) (inl x)))
  PushoutPushoutMap→PushoutA→PushoutPushoutMap n x =
    (cong-∙∙ (PushoutPushoutMap→PushoutA f g n) _ _ _
    ∙ cong₃ _∙∙_∙∙_
            (cong-∙ (PushoutPushoutMap→PushoutA f g n ∘ PushoutA→PushoutPushoutMapL f g n)
                     (sym (comm f (suc n) x)) refl
              ∙ sym (rUnit _))
            (cong-∙∙ (PushoutPushoutMap→PushoutA f g n) _ _ _
            ∙ sym (rUnit _))
            (cong sym (cong-∙ (PushoutPushoutMap→PushoutA f g n ∘ PushoutA→PushoutPushoutMapR f g n)
                     (sym (comm g (suc n) x)) refl
              ∙ sym (rUnit _))))
   ◁ λ i j → hcomp (λ k → λ {(i = i1) → main n x k j
                            ; (j = i0) → PushoutPushoutMap→PushoutA→PushoutPushoutMap-inl n (comm f (suc n) x k) i -- 
                            ; (j = i1) → PushoutPushoutMap→PushoutA→PushoutPushoutMap-inr n (comm g (suc n) x k) i})
                  (PushoutPushoutMap→PushoutA f g n
                    (PushoutA→PushoutPushoutMapLR f g n x j))
       where
       inr2filler : (n : ℕ) (x : _) (i j k : I) → pushoutA f g (suc (suc (suc (suc n))))
       inr2filler  n x  i j k =
         hfill (λ k → λ {(i = i0) →  (doubleCompPath-filler
                                         (cong (PushoutPushoutMap→PushoutA f g (suc (suc n)))
                                                 (push (inr x , north)))
                                        refl
                                        (cong (PushoutPushoutMap→PushoutA f g (suc (suc n)))
                                               (sym (push (inr x , south)))) k j)
                        ; (i = i1) → push (inr x) (k ∧ j)
                        ; (j = i0) → inl (comm f (suc (suc (suc n))) (inr x) i)
                        ; (j = i1) → doubleCompPath-filler
                                       (λ i → inr (comm g (suc (suc (suc n))) (inr x) i))
                                       (sym (push (inr x)))
                                       (λ i → inl (comm f (suc (suc (suc n))) (inr x) (~ i))) (~ i) (~ k)})
           (inS (inl (comm f (suc (suc (suc n))) (inr x) i))) k

       inlfiller : (n : ℕ) (x : _) (i j : I) → pushoutA f g (suc (suc n))
       inlfiller  n x i j =
         doubleCompPath-filler (λ i₁ → inl (comm f (suc n) (inl x) i₁))
             (push (inl x))
             (λ i₁ → inr (comm g (suc n) (inl x) (~ i₁))) (~ i) j

       main : (n : ℕ) (x : _)
         → Square (cong (PushoutPushoutMap→PushoutA f g n)
                   (PushoutA→PushoutPushoutMapLR f g n x)) (push x)
                   (λ i → inl (comm f (suc n) x i))
                   λ i → inr (comm g (suc n) x i)
       main n (inl x) i j = inlfiller n x i j
       main zero (inr x) = {!PushoutPushoutMap→PushoutA f g (suc (suc n))!}
       main (suc zero) (inr x) = {!!}
       main (suc (suc n)) (inr x) =
         cong-∙∙ (PushoutPushoutMap→PushoutA f g (suc (suc n)))
           (push (inr x , north)) (λ _ → inr (inr x))
           (sym (push (inr x , south))) ◁ (λ i j → inr2filler n x i j i1) ▷ refl -- inr2filler n x i j i1
       main (suc zero) (push a i) j k = {!!}
       main (suc (suc n)) (push (a , s) i) j k =
         hcomp (λ r → λ {(i = i0) → inlfiller (suc (suc n)) (α B (suc (suc n)) (a , s)) j k
                        ; (j = i0) → W (~ r) i k
                        ; (j = i1) → push (push (a , s) i) k
                        ; (k = i0) → inl (comm f (suc (suc (suc n))) (push (a , s) i) j)
                        ; (k = i1) → inr (comm g (suc (suc (suc n))) (push (a , s) i) j)})
           (hcomp (λ r → λ {(i = i0) → compPath-filler' (λ j₁ → W1 i0 k j₁)
                                          (λ j → inlfiller (suc (suc n)) (α B (suc (suc n)) (a , s)) j k)
                                           (~ r) j
                        ; (i = i1) → compPath-filler' (λ j₁ → W1 i1 k j₁)
                                          (λ j → inr2filler n a j k i1)
                                          (~ r) j
                        ; (j = i0) → W1 i k r
                        ; (j = i1) → push (push (a , s) i) k
                        ; (k = i0) → compPath-filler' (λ j → W1 i i0 j) (λ j → inl (comm f (suc (suc (suc n))) (push (a , s) i) j)) (~ r) j
                        ; (k = i1) → compPath-filler' (λ j → W1 i i1 j) (λ j → inr (comm g (suc (suc (suc n))) (push (a , s) i) j)) (~ r) j})
              (hcomp (λ r → λ {(i = i0) → {!!}
                              ; (i = i1) → {!!}
                              ; (j = i1) → push (push (a , s) (i ∨ ~ r)) k
                              ; (k = i0) → {!compPath-filler (λ j₁ → W1 i i0 j₁) (λ r → inl (comm f (suc (suc (suc n))) (push (a , s) (j ∨ ~ r))))!}
                              ; (k = i1) → {!!}})
                   {!!})) -- (push (invEq (e (strictCWskel B') (suc (suc n))) (inr a))  ((~ i ∨ j) ∧ k))))
         where --
         W = cong-PushoutA→PushoutPushoutMapLRGen>1 (PushoutPushoutMap→PushoutA f g (suc (suc n)))
               inl
               (λ i → inl (∣ f ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (a , s) i))))
               (push (α B (suc (suc n)) (a , s)))
               (λ i → inr (∣ g ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (a , s) (~ i)))))
               (push (inr a , north))
               (push (inr a , south))
               (λ j i → (push (inr a , merid s j)) i)

         W1 : (i j k : I) → _
         W1 i j k = PushoutA→PushoutPushoutMapLRGen>1
                  (PushoutPushoutMap→PushoutA f g (suc (suc n)) ∘ inl)
                     (λ i₂ →
                        inl
                        (∣ f ∣ (suc (suc (suc n)))
                         (invEq (e B (suc (suc n))) (push (a , s) i₂))))
                     (push (α B (suc (suc n)) (a , s)))
                     (λ i₂ →
                        inr
                        (∣ g ∣ (suc (suc (suc n)))
                         (invEq (e B (suc (suc n))) (push (a , s) (~ i₂)))))
                     refl
                     ((λ i → inr (comm g (suc (suc (suc n))) (inr a) i))
                           ∙∙ sym (push (inr a))
                           ∙∙ (λ i → inl (comm f (suc (suc (suc n))) (inr a) (~ i))))
                     (λ i₂ j₂ → PushoutPushoutMap→PushoutA f g (suc (suc n))
                        (push (inr a , merid s i₂) j₂))
                     i j k

         W1Charac : Path (Square _ _ _ _) (λ i j → W1 i j i1) {!!}
         W1Charac = {!!}
  
         i1C : Cube {!PushoutPushoutMap→PushoutA f g (suc (suc n)) (inl (push (α B (suc (suc n)) (a , s)) ?))!} {!!} --  (λ k j → inlfiller (suc (suc n)) (α B (suc (suc n)) (a , s)) j k)
                    {!!} {!!}
                    {!!} {!!} -- (λ r k → W1 i0 k r) λ r k → push (inl (strictifyFamα B' (suc (suc n)) (a , s))) k
         i1C = {!Goal: Pushout
      (λ x₁ →
         ∣ f ∣ (suc (suc (suc (suc n))))
         (CW↪ (strictCWskel B') (suc (suc (suc n))) x₁))
      (λ x₁ →
         ∣ g ∣ (suc (suc (suc (suc n))))
         (CW↪ (strictCWskel B') (suc (suc (suc n))) x₁))
———— Boundary (wanted) —————————————————————————————————————
k = i0 ⊢ (?14 (r = i0))
k = i1 ⊢ (?15 (r = i0))
j = i0 ⊢ (W1 i k i0)
j = i1 ⊢ (inl
          (∣ f ∣ (suc (suc (suc (suc n))))
           (CW↪ (strictCWskel B') (suc (suc (suc n))) (push (a , s) i))))
i = i0 ⊢ (?13 (r = i0))
i = i1 ⊢ (inr2filler n a j k i0)!}


         CC : Cube {!(cong (PushoutPushoutMap→PushoutA f g (suc (suc n)))
                      (push (inr a , south)))!}
                   (λ i k → push (push (a , s) i) k)
                   (λ j k → inlfiller (suc (suc n)) (α B (suc (suc n)) (a , s)) j k)
                   {!!} -- (λ j k → inr2filler n a j k i1)
                   (λ j i → inl (comm f (suc (suc (suc n))) (push (a , s) i) j))
                   λ j i → inr (comm g (suc (suc (suc n))) (push (a , s) i) j)
         CC = {!cong-PushoutA→PushoutPushoutMapLRGen>1 f g (PushoutPushoutMap→PushoutA f g (suc (suc n)))
               inl
               (λ i → inl (∣ f ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (a , s) i))))
               (push (α B (suc (suc n)) (a , s)))
               (λ i → inr (∣ g ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (a , s) (~ i)))))
               (push (inr a , north))
               (push (inr a , south))
               (λ j i → (push (inr a , merid s j)) i)!} -- cong-hcomp (PushoutPushoutMap→PushoutA f g (suc (suc n)))
           ◁ {!!}
               
{-
ed) —————————————————————————————————————
k = i0 ⊢ inl (comm f (suc (suc (suc n))) (push a i) j)
k = i1 ⊢ inr (comm g (suc (suc (suc n))) (push a i) j)
j = i0 ⊢ main (suc (suc n)) (push a i) i0 k
j = i1 ⊢ push (push a i) k
i = i0 ⊢ main (suc (suc n)) (push a i0) j k
i = i1 ⊢ inr2filler n (fst a) j k i1
-}


{-
    ∙ cong₃ _∙∙_∙∙_
      (cong-∙ (PushoutPushoutMap→PushoutA f g n ∘ PushoutA→PushoutPushoutMapL f g n) _ _
             ∙ sym (rUnit _) ∙ refl)
             (cong-∙∙ (PushoutPushoutMap→PushoutA f g n) _ _ _ ∙ sym (rUnit _)  ∙ refl)
             {!!}
    ∙ {!!}) ◁ {!!}
    -}

  Iso-PushoutPushoutMap-PushoutA : (n : ℕ) → Iso (Pushout (pushoutMapₛ f g n) fst) (pushoutA f g (suc (suc n)))
  Iso.fun (Iso-PushoutPushoutMap-PushoutA n) = PushoutPushoutMap→PushoutA f g n
  Iso.inv (Iso-PushoutPushoutMap-PushoutA n) = PushoutA→PushoutPushoutMap f g n
  Iso.rightInv (Iso-PushoutPushoutMap-PushoutA n) (inl x) =
    PushoutPushoutMap→PushoutA→PushoutPushoutMap-inl n x
  Iso.rightInv (Iso-PushoutPushoutMap-PushoutA n) (inr x) =
    PushoutPushoutMap→PushoutA→PushoutPushoutMap-inr n x
  Iso.rightInv (Iso-PushoutPushoutMap-PushoutA n) (push a i) k =
    PushoutPushoutMap→PushoutA→PushoutPushoutMap n a k i
  Iso.leftInv (Iso-PushoutPushoutMap-PushoutA n) x = {!!}


-- -- characterisation of boundary map
-- module _ {ℓ ℓ' ℓ'' : Level} {B' : CWskel ℓ} {C' : CWskel ℓ'} {D' : CWskel ℓ''}
--   (f : cellMap (strictCWskel B') (strictCWskel C'))
--   (g : cellMap (strictCWskel B') (strictCWskel D')) where
--   private
--     B = strictCWskel B'
--     C = strictCWskel C'
--     D = strictCWskel D'

--   open CWskel-fields
--   open SequenceMap renaming (map to ∣_∣)


--   CWPushout→cofibCW : (n : ℕ) (b : Pushout (α B (suc n)) fst) → cofibCW (suc n) B
--   CWPushout→cofibCW n (inl x) = inr (inl x)
--   CWPushout→cofibCW n (inr x) = inl tt
--   CWPushout→cofibCW n (push a i) = (push (α B (suc n) a)) (~ i)

--   CWPushout→cofibCWB : (n : ℕ) (b : Pushout (α B (suc n)) fst) → cofibCW (suc n) B
--   CWPushout→cofibCWB n (inl x) = inl tt
--   CWPushout→cofibCWB n (inr x) = inl tt
--   CWPushout→cofibCWB n (push a i) =
--     (push (α B (suc n) a)
--     ∙∙ ((λ i → inr ((push a ∙ sym (push (fst a , ptSn n))) i)))
--     ∙∙ sym (push (α B (suc n) (fst a , ptSn n)))) i

--   CWPushout→cofibCWB∙ : (n : ℕ) (x : _) → cong (CWPushout→cofibCWB n) (push (x , ptSn n)) ≡ refl
--   CWPushout→cofibCWB∙ n x = cong₃ _∙∙_∙∙_ refl (λ j i → inr (rCancel (push (x , ptSn n)) j i)) refl
--     ∙ ∙∙lCancel _

--   CWPushout→cofibCW≡inr : (n : ℕ) (b : _) → CWPushout→cofibCW n b ≡ inl tt
--   CWPushout→cofibCW≡inr n (inl x) = sym (push x)
--   CWPushout→cofibCW≡inr n (inr x) = refl
--   CWPushout→cofibCW≡inr n (push a i) j = push (α B (suc n) a) (~ i ∧ ~ j)

--   module _ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (q : x ≡ x) (r : Square refl q (sym p) (sym p)) where
--     sidesGenFiller : (i j k : I) → A
--     sidesGenFiller i j k =
--       hfill (λ k → λ {(i = i0) → r k j
--                      ; (i = i1) → doubleCompPath-filler p refl (sym p) k j
--                      ; (j = i0) → p (~ k)
--                      ; (j = i1) → p (~ k)})
--          (inS y) k

--     sidesGen : q ≡ (p ∙∙ refl ∙∙ sym p)
--     sidesGen i j = sidesGenFiller i j i1

--   private
--     congPushout→BLoopPre : (n : ℕ) (b : _)
--       → cong (Pushout→B f g n) (PushoutA→PushoutPushoutMapLR f g (suc n) b)
--        ≡ merid (inl tt) ∙∙ refl ∙∙ merid (CWPushout→cofibCWB n b) ⁻¹
--     congPushout→BLoopPre n (inl x) = sidesGen (merid (inl tt)) refl λ i _ → merid (inl tt) (~ i)
--     congPushout→BLoopPre zero (inr x) i j = sidesGen (merid (inl tt)) refl (λ i _ → merid (inl tt) (~ i)) i j
--     congPushout→BLoopPre (suc n) (inr x) =
--       cong-∙∙ (Pushout→B f g (suc n)) (push (inr x , north)) refl (sym (push (inr x , south)))
--     congPushout→BLoopPre zero (push (a , false) i) j k =
--       hcomp (λ r → λ {(i = i0) → sidesGen (merid (inl tt)) refl (λ i _ → merid (inl tt) (~ i)) j k
--                      ; (i = i1) → sidesGen (merid (inl tt)) refl (λ i _ → merid (inl tt) (~ i)) j k
--                      ; (j = i0) → h (~ r) i k
--                      ; (j = i1) → ((merid (inl tt)) ∙∙ refl ∙∙ merid (CWPushout→cofibCWB zero (push (a , false) i)) ⁻¹) k
--                      ; (k = i0) → north
--                      ; (k = i1) → north})
--          (hcomp (λ r → λ {(i = i0) → P' _ (merid (inl tt)) r j k
--                          ; (i = i1) → P' _ (merid (inl tt)) r j k
--                          ; (j = i1) → doubleCompPath-filler (merid (inl tt)) (λ _ → south) (merid (CWPushout→cofibCWB zero (push (a , false) i)) ⁻¹) r k
--                          ; (k = i0) → merid (inl tt) (~ r)
--                          ; (k = i1) → merid (CWPushout→cofibCWB zero (push (a , false) i)) (~ r ∧ j)})
--                     (woo _ (merid (inl tt))
--                       (λ j i → merid (cofib→wedgeInrσ f g 1 (loop j) a) i) k j i))
--        where
--        P = cong-hcomp (Pushout→B f g zero)

--        woo : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) (q : p ≡ p)
--          → Cube (λ _ _ → y) (λ j i → q i j)
--                  (λ k i → q  i (~ k))
--                  (λ _ _ → y)
--                  (λ k j → p (j ∨ ~ k))
--                  λ k j → p (j ∨ ~ k)
--        woo = J> λ q → compPathL→PathP ((cong₂ _∙_ refl (sym (rUnit _)) ∙ sym (rUnit _)))

--        P' : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y)
--           → Cube (λ i j → p (i ∨ ~ j)) (λ j k → sidesGen p refl (λ i _ → p (~ i)) j k)
--                  (λ i j → invSides-filler p refl j (~ i)) (doubleCompPath-filler p refl (sym p))
--                  (λ r j → p (~  r)) (λ r j → p (~ r ∧ j))
--        P' {x = x} = J> compPathL→PathP (cong₂ _∙_ (sym (rUnit refl)) (sym (lUnit _)))

--        h : Path (Square {A = Susp (cofibCW 1 (strictCWskel B'))} _ _ _ _)
--                 (λ i k → Pushout→B f g zero (PushoutA→PushoutPushoutMapLR-push-filler f g zero a false i k i1))
--                 _
--        h = (λ r i k → Pushout→B f g zero (PushoutA→PushoutPushoutMapLR-push-filler f g zero a false i k (~ r)))
--          ∙ cong-PushoutA→PushoutPushoutMapLRGen0 f g (Pushout→B f g zero) inl
--              (λ i₁ → inl (∣ f ∣ 2 (invEq (e B 1) (push (a , false) (~ i₁)))))
--              (push (α B 1 (a , false)))
--              (λ i₁ → inr (∣ g ∣ 2 (invEq (e B 1) (push (a , false) i₁))))
--              (λ i₁ → inl (∣ f ∣ 2 (invEq (e B 1) (push (a , true) (~ i₁)))))
--              (push (α B 1 (a , true)))
--              (λ i₁ → inr (∣ g ∣ 2 (invEq (e B 1) (push (a , true) i₁))))
--              (push (inr a , base)) (λ i j → push (inr a , loop i) (~ j))
--     congPushout→BLoopPre zero (push (a , true) i) j = h j i
--       where
--       h : Square refl
--            (λ i → merid (inl tt) ∙∙ refl ∙∙ merid (CWPushout→cofibCWB zero (push (a , true) i)) ⁻¹)
--            (sidesGen (merid (inl tt)) refl (λ i _ → merid (inl tt) (~ i)))
--            (sidesGen (merid (inl tt)) refl (λ i _ → merid (inl tt) (~ i)))
--       h = (λ i j → sidesGen (merid (inl tt)) refl
--             (λ i₂ _ → merid (inl tt) (~ i₂)) i)
--         ▷ λ j i → ((merid (inl tt) ∙∙ refl ∙∙ (merid (CWPushout→cofibCWB∙ zero a (~ j) i)) ⁻¹))
--     congPushout→BLoopPre (suc n) (push (a , s) i) j k =
--            hcomp (λ r → λ { (i = i0) → (sidesGen (merid (inl tt)) refl λ i _ → merid (inl tt) (~ i)) j k
--                       ; (i = i1) → cong-∙∙ (Pushout→B f g (suc n))
--                                       (push (inr a , north)) refl (sym (push (inr a , south))) (j ∨ ~ r) k
--                       ; (j = i0) → (cong-PushoutA→PushoutPushoutMapLRGen>1 f g (Pushout→B f g (suc n))
--                                      inl
--                                      (λ i → inl (∣ f ∣ (suc (suc (suc n))) ((push (a , s) i))))
--                                      (push (α B (suc (suc n)) (a , s)))
--                                      (λ i → inr (∣ g ∣ (suc (suc (suc n))) ((push (a , s) (~ i)))))
--                                      (push (inr a , north))
--                                      (push (inr a , south))
--                                      (λ j i → (push (inr a , merid s j) i))) (~ r) i k
--                       ; (j = i1) → (merid (inl tt) ∙∙ refl ∙∙ (merid (CWPushout→cofibCWB (suc n) (push (a , s) i)) ⁻¹)) k 
--                       ; (k = i0) → north
--                       ; (k = i1) → north})
--                   (hcomp (λ r → λ { (i = i0) → sidesGenFiller (merid (inl tt)) (λ _ → north) (λ i₁ _ → merid (inl tt) (~ i₁)) j k i1
--                       ; (i = i1) → doubleCompPath-filler (merid (inl tt)) refl (sym (merid (inl tt))) (r ∨ j) k
--                       ; (j = i1) → (merid (inl tt) ∙∙ (λ _ → south) ∙∙ (merid (CWPushout→cofibCWB (suc n) (push (a , s) i)) ⁻¹)) k
--                       ; (k = i0) → invSides-filler-filler {A = Susp (cofibCW (suc (suc n)) (strictCWskel B'))}
--                                        refl (merid (inl tt)) i r (~ j)
--                       ; (k = i1) → invSides-filler-filler {A = Susp (cofibCW (suc (suc n)) (strictCWskel B'))}
--                                        refl (merid (inl tt)) i r (~ j)})
--                       (help _ (merid (inl tt)) (λ i → merid (CWPushout→cofibCWB (suc n) (push (a , s) i))) i k j))
--                   where
--                   help : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) (r : p ≡ p) -- i k j
--                     → Cube (λ k j → sidesGenFiller p _ (λ i _ → p (~ i)) j k i1)
--                             (λ k j → doubleCompPath-filler p refl (sym p) j k)
--                             (λ i j → p (i ∧ ~ j))
--                             (λ i j → p (i ∧ ~ j))
--                             (λ i k → r k i)
--                             (λ i k → (p ∙∙ refl ∙∙ sym (r i)) k)
--                   help {x = x} = J> λ r
--                     → λ i k j
--                      → hcomp (λ w → λ { (i = i0) → sidesGenFiller refl (λ _ → x) refl j k w
--                                         ; (i = i1) → lUnit (λ _ → x) (w ∧ j) k
--                                         ; (j = i0) → r k i
--                                         ; (j = i1) → lUnit (sym (r i)) w k
--                                         ; (k = i0) → x
--                                         ; (k = i1) → x})
--                        (sym≡flipSquare r j (~ k) i)

--   -- main 
--   congPushout→BLoop : (n : ℕ) (b : _)
--     → cong (Pushout→B f g n) (PushoutA→PushoutPushoutMapLR f g (suc n) b)
--      ≡ sym (toSusp (_ , inl tt) (CWPushout→cofibCWB n b))
--   congPushout→BLoop n b = congPushout→BLoopPre n b
--     ∙ doubleCompPath≡compPath _ _ _
--     ∙ cong₂ _∙_ refl (sym (lUnit _))
--     ∙ sym (symDistr _ _)

-- --     -- where
-- --     -- LL : merid (inl tt) ∙∙ refl ∙∙ (merid (CWPushout→cofibCWB (suc n) (push (a , s) i))) ⁻¹
-- --     --    ≡ merid (inl tt) ∙ (merid (CWPushout→cofibCWB (suc n) (push (a , s) i))) ⁻¹
-- --     -- LL = {!!}
    
-- --     -- vgen : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (F : A → B) {x : A}
-- --     --        (y : A) (p : x ≡ y) (z : A) (m : x ≡ z) -- (w : A)
-- --     --        (r : z ≡ y) (t : B) (minl : F y ≡ t)
-- --     --        (sq : Square minl minl (cong F (sym p ∙∙ m ∙∙ sym (sym r))) refl) 
-- --     --     → Cube (λ i k → PushoutA→PushoutPushoutMapLRGen>1 f g F p m (sym r) minl minl sq i k i1)
-- --     --             {!λ i k → (minl ∙∙ refl ∙∙ sym (sq k)) i!} -- (λ i k → (minl ∙∙ refl ∙∙ sym (sq i)) k)
-- --     --             {!λ j k → sidesGen minl refl (λ i _ → minl (~ i)) j k!} -- j i k
-- --     --             {!!}
-- --     --             (λ i j → F (p j))
-- --     --             λ i j → F (r j)
-- --     -- vgen = {!!}
-- -- {-
-- -- (cong-PushoutA→PushoutPushoutMapLRGen>1 f g (Pushout→B f g (suc n))
-- --                      inl
-- --                      (λ i → inl (∣ f ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (a , s) i))))
-- --                      (push (α B (suc (suc n)) (a , s)))
-- --                      (λ i → inr (∣ g ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (a , s) (~ i)))))
-- --                      (push (inr a , north))
-- --                      (push (inr a , south))
-- --                      (λ j i → (push (inr a , merid s j) i)))
-- -- -}
-- --   {-
-- --      hcomp (λ r → λ { (i = i0) → cube1 r j k
-- --                     ; (i = i1) →  (sidesGenFiller (merid (inl tt))
-- --                                      (cong (Pushout→B f g (suc n))
-- --                                            (push ((inr a) , south) ∙∙ refl ∙∙ sym (push ((inr a) , north))))
-- --                                      λ i j → Pushout→B f g (suc n)
-- --                                        (doubleCompPath-filler (push ((inr a) , south)) refl (sym (push ((inr a) , north))) i j)) j k r -- r
-- --                     ; (j = i0) → Pushout→B f g (suc n) (PushoutA→PushoutPushoutMapLR-push-filler f g (suc n) a s i k r)
-- --                     ; (j = i1) → doubleCompPath-filler (merid (inl tt)) refl (merid (CWPushout→cofibCWB (suc n) (push (a , s) i)) ⁻¹) r k -- 
-- --                     ; (k = i0) → {!k0 j r i!} -- k0 j r i
-- --                     ; (k = i1) → {!!}})
-- --            {!!} -- (merid (cofib→wedgeInrσ f g (suc (suc n)) (merid s k) a) (i ∨ j))
          
-- -- -}
-- --           where
-- --           fsteq : Cube (λ i j → Pushout→B f g (suc n)
-- --                                  (PushoutA→PushoutPushoutMapLR f g (suc (suc n))
-- --                                    (push (a , s) i) j))
-- --                        _
-- --                        (λ _ _ → north)
-- --                        (λ i j  → Pushout→B f g (suc n)
-- --                                  (PushoutA→PushoutPushoutMapLR f g (suc (suc n))
-- --                                    (push (a , s) i1) j))
-- --                        (λ _ _ → north)
-- --                        λ _ _ → north
-- --           fsteq = cong-hcomp (Pushout→B f g (suc n))

-- --           rew1 = fsteq i1

-- --           rew2 : Square _ _ _ _
-- --           rew2 = {!!}

-- --           l1 : rew1 ≡ rew2
-- --           l1 = {!cong-PushoutA→PushoutPushoutMapLRGen>1 (Pushout→B f g (suc n))!}

-- --           l2 : Cube (fsteq i0) rew2 _ _ _ _
-- --           l2 = {! (cong-PushoutA→PushoutPushoutMapLRGen>1 f g (Pushout→B f g (suc n))
-- --                      inl
-- --                      (λ i → inl (∣ f ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (a , s) i))))
-- --                      (push (α B (suc (suc n)) (a , s)))
-- --                      (λ i → inr (∣ g ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (a , s) (~ i)))))
-- --                      (push (inr a , north))
-- --                      (push (inr a , south))
-- --                      (λ j i → (push (inr a , merid s j) i)))!} -- fsteq ∙ l1
          

-- --           cube1Gen : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p' p : x ≡ y) (q : p' ≡ p)
-- --             → Cube (λ j k → q k j) (λ j k → sidesGen p refl (λ i _ → p (~ i)) j k)
-- --                     (λ _ _ → x) (doubleCompPath-filler p refl (sym p))
-- --                     (q ◁ (λ i j → p (~ i ∧ j)))
-- --                     (λ i j → p (~ i ∧ j))
-- --           cube1Gen {x = x} = J> (J> {!!})


-- --           cube1 : Cube (λ j k → merid (cofib→wedgeInrσ f g (suc (suc n)) (merid s k) a) j)
-- --                        (λ j k → sidesGen (merid (inl tt)) refl (λ i _ → merid (inl tt) (~ i)) j k)
-- --                        (λ _ _ → north)
-- --                        (doubleCompPath-filler (merid (inl tt)) (λ _ → south) (merid (inl tt) ⁻¹))
-- --                        ((λ k j → merid (cofib→wedgeInrσ f g (suc (suc n)) (merid s k) a) j)
-- --                          ◁ λ i j → merid (inl tt) (~ i ∧ j))
-- --                        λ i j → merid (inl tt) (~ i ∧ j)
-- --           cube1 = cube1Gen _ _ _ _

-- --           k0-help : Cube (λ r i → Pushout→B f g (suc n)
-- --                                  (PushoutA→PushoutPushoutMapLR-push-filler
-- --                                    f g (suc n) a s i i0 r))
-- --                     (λ r i → merid (inl tt) (~ r)) -- (λ r i → merid (inl tt) (~ r) i)
-- --                     {!!} -- (λ j i → merid (inl tt) (i ∨ j))
-- --                     (λ j i → north)
-- --                     (λ j r → cube1 r j i0)
-- --                     (λ j r → merid (inl tt) (~ r))
-- --           k0-help = {!!}

-- --           -- k0 : Cube (λ r i → Pushout→B f g (suc n)
-- --           --                        (PushoutA→PushoutPushoutMapLR-push-filler
-- --           --                          f g (suc n) a s i i0 r))
-- --           --           (λ r i → merid (inl tt) (~ r)) -- (λ r i → merid (inl tt) (~ r) i)
-- --           --           {!!} -- (λ j i → merid (inl tt) (i ∨ j))
-- --           --           (λ j i → north)
-- --           --           {!!} -- ({!!} ◁ {!λ i j → merid (inl tt) (~ i ∧ j)!}) -- (λ j r → cube1 r j i0) -- (λ j r → cube1 r j i0)
-- --           --           (λ j r → merid (inl tt) (~ r))
-- --           -- k0 j r i = {!!}
-- --           {-
-- --             hcomp (λ k →  λ { (i = i0) → {!cube1 r j i0!}
-- --                     ; (i = i1) → merid (inl tt) (~ r ∧ k)
-- --                     ; (j = i0) → Pushout→B f g (suc n)
-- --                                    (invSides-filler-filler (push (inr a , north))
-- --                                     (λ i → inl (inl (∣ f ∣ (suc (suc (suc n)))
-- --                                     ((push (a , s) (~ i)))))) r i k)
-- --                     ; (j = i1) → merid (inl tt) (~ r ∧ k)
-- --                     ; (r = i0) → {!!} -- merid (inl tt) (k ∧ (i ∨ j))
-- --                     ; (r = i1) → north})
-- --                  north
-- -- -}

-- -- -- module _ {ℓ ℓ' ℓ'' : Level} {B' : CWskel ℓ} {C' : CWskel ℓ'} {D' : CWskel ℓ''}
-- -- --   (f : cellMap (strictCWskel B') (strictCWskel C'))
-- -- --   (g : cellMap (strictCWskel B') (strictCWskel D')) where
-- -- --   private
-- -- --     B = strictCWskel B'
-- -- --     C = strictCWskel C'
-- -- --     D = strictCWskel D'

-- -- --   open CWskel-fields
-- -- --   open SequenceMap renaming (map to ∣_∣)
  
-- -- --   PushoutA→PushoutPushoutMapStrict : (n : ℕ)
-- -- --     → (pushoutA f g (suc (suc n))) → (Pushout (pushoutMapₛ f g n) fst)
-- -- --   PushoutA→PushoutPushoutMapStrict n (inl x) =
-- -- --     PushoutA→PushoutPushoutMapL f g n (fst (e C (suc n)) x)
-- -- --   PushoutA→PushoutPushoutMapStrict n (inr x) =
-- -- --     PushoutA→PushoutPushoutMapR f g n (fst (e D (suc n)) x)
-- -- --   PushoutA→PushoutPushoutMapStrict n (push a i) =
-- -- --       (cong (PushoutA→PushoutPushoutMapL f g n)
-- -- --         (cong (fst (e C (suc n))) (sym (comm f (suc n) a)))
-- -- --     ∙∙ PushoutA→PushoutPushoutMapLR f g n (fst (e B n) a)
-- -- --     ∙∙ cong (PushoutA→PushoutPushoutMapR f g n)
-- -- --         (sym (cong (fst (e D (suc n))) (sym (comm g (suc n) a))))) i

-- -- --   PushoutA→PushoutPushoutMapStrict≡ : (n : ℕ) (x : _)
-- -- --     → PushoutA→PushoutPushoutMapStrict n x ≡ PushoutA→PushoutPushoutMap f g n x
-- -- --   PushoutA→PushoutPushoutMapStrict≡ n (inl x) = refl
-- -- --   PushoutA→PushoutPushoutMapStrict≡ n (inr x) = refl
-- -- --   PushoutA→PushoutPushoutMapStrict≡ n (push a i) j =
-- -- --     (cong (PushoutA→PushoutPushoutMapL f g n)
-- -- --           (rUnit (cong (fst (e C (suc n))) (sym (comm f (suc n) a))) j)
-- -- --     ∙∙ rUnit (PushoutA→PushoutPushoutMapLR f g n (fst (e B n) a)) j
-- -- --     ∙∙ cong (PushoutA→PushoutPushoutMapR f g n)
-- -- --         (sym (rUnit ((cong (fst (e D (suc n))) (sym (comm g (suc n) a)))) j))) i

-- -- -- {-

-- -- --   mapBack : (n : ℕ) → Pushout (pushoutMapₛ f g n) fst → pushoutA f g (suc (suc n))
-- -- --   mapBack n (inl (inl x)) = inl (inl x)
-- -- --   mapBack n (inl (inr x)) = inr (inl x)
-- -- --   mapBack n (inl (push a i)) = ((λ i → inl (comm f (suc n) (inl a) i)) ∙∙ push (inl a) ∙∙ λ i → inr (comm g (suc n) (inl a) (~ i))) i
-- -- --   mapBack n (inr (inl (inl x))) = inl (inr x)
-- -- --   mapBack n (inr (inl (inr x))) = inr (inr x)
-- -- --   mapBack n (inr (inr x)) = inl (inl (∣ f ∣ (suc n) (inr x)))
-- -- --   mapBack n (push (inl (inl x) , t) i) = inl ((push (x , Iso.inv (IsoSphereSusp n) t )) i)
-- -- --   mapBack n (push (inl (inr x) , t) i) = inr ((push (x , Iso.inv (IsoSphereSusp n) t )) i)
-- -- --   mapBack n (push (inr x , north) i) = inl (inl (∣ f ∣ (suc n) (inr x)))
-- -- --   mapBack n (push (inr x , south) i) =
-- -- --     ((λ i → inr (comm g (suc n) (inr x) i))
-- -- --     ∙∙ sym (push (inr x))
-- -- --     ∙∙ λ i → inl (comm f (suc n) (inr x) (~ i))) i
-- -- --   mapBack n (push (inr x , merid a i) j) = {!!}
-- -- -- -}

-- -- -- sphereBouquetIso : (n : ℕ) {a b c : ℕ}
-- -- --   → Iso (SphereBouquet n (Fin (a + b + c))) (SphereBouquet n ((Fin a ⊎ Fin b) ⊎ Fin c))
-- -- -- Iso.fun (sphereBouquetIso n) (inl x) = inl x
-- -- -- Iso.fun (sphereBouquetIso n) (inr (x , y)) = inr ((fst (finSplit3≃ _ _ _) x) , y)
-- -- -- Iso.fun (sphereBouquetIso n) (push a i) = push (fst (finSplit3≃ _ _ _) a) i
-- -- -- Iso.inv (sphereBouquetIso n) (inl x) = inl x
-- -- -- Iso.inv (sphereBouquetIso n) (inr (x , y)) = inr ((invEq (finSplit3≃ _ _ _) x) , y)
-- -- -- Iso.inv (sphereBouquetIso n) (push a i) = push (invEq (finSplit3≃ _ _ _) a) i
-- -- -- Iso.rightInv (sphereBouquetIso n) (inl x) = refl
-- -- -- Iso.rightInv (sphereBouquetIso n) (inr (x , y)) i = inr ((secEq (finSplit3≃ _ _ _) x i) , y)
-- -- -- Iso.rightInv (sphereBouquetIso n) (push a i) j = push (secEq (finSplit3≃ _ _ _) a j) i
-- -- -- Iso.leftInv (sphereBouquetIso n) (inl x) = refl
-- -- -- Iso.leftInv (sphereBouquetIso n) (inr (x , y)) i = inr ((retEq (finSplit3≃ _ _ _) x i) , y)
-- -- -- Iso.leftInv (sphereBouquetIso n) (push a i) j = push (retEq (finSplit3≃ _ _ _) a j) i

-- -- -- SplitBouquet : (n : ℕ) (a b c : ℕ) → Type ℓ-zero
-- -- -- SplitBouquet n a b c = (SphereBouquet∙ n (Fin a) ⋁∙ₗ SphereBouquet∙ n (Fin b))
-- -- --                                           ⋁ SphereBouquet∙ n (Fin c)

-- -- -- module _ (n : ℕ) {a b c : ℕ} where
-- -- --   sumSphereBouquet→SplitBouquet : (SphereBouquet n ((Fin a ⊎ Fin b) ⊎ Fin c))
-- -- --      → SplitBouquet n a b c
-- -- --   sumSphereBouquet→SplitBouquet (inl x) = inl (inl (inl x))
-- -- --   sumSphereBouquet→SplitBouquet (inr (inl (inl x) , y)) = inl (inl (inr (x , y)))
-- -- --   sumSphereBouquet→SplitBouquet (inr (inl (inr x) , y)) = inl (inr (inr (x , y)))
-- -- --   sumSphereBouquet→SplitBouquet (inr (inr x , y)) = inr (inr (x , y))
-- -- --   sumSphereBouquet→SplitBouquet (push (inl (inl x)) i) = inl (inl (push x i))
-- -- --   sumSphereBouquet→SplitBouquet (push (inl (inr x)) i) =
-- -- --     inl (((λ i → push tt i) ∙ λ i → (inr (push x i))) i)
-- -- --   sumSphereBouquet→SplitBouquet (push (inr x) i) = (push tt ∙ λ i → inr (push x i)) i

-- -- --   SplitBouquet→sumSphereBouquet : SplitBouquet n a b c
-- -- --     → SphereBouquet n ((Fin a ⊎ Fin b) ⊎ Fin c)
-- -- --   SplitBouquet→sumSphereBouquet (inl (inl (inl x))) = inl x
-- -- --   SplitBouquet→sumSphereBouquet (inl (inl (inr (x , y)))) = inr ((inl (inl x)) , y)
-- -- --   SplitBouquet→sumSphereBouquet (inl (inl (push a i))) = push (inl (inl a)) i
-- -- --   SplitBouquet→sumSphereBouquet (inl (inr (inl x))) = inl x
-- -- --   SplitBouquet→sumSphereBouquet (inl (inr (inr (x , y)))) = inr ((inl (inr x)) , y)
-- -- --   SplitBouquet→sumSphereBouquet (inl (inr (push a i))) = push (inl (inr a)) i
-- -- --   SplitBouquet→sumSphereBouquet (inl (push a i)) = inl tt
-- -- --   SplitBouquet→sumSphereBouquet (inr (inl x)) = inl x
-- -- --   SplitBouquet→sumSphereBouquet (inr (inr (x , y))) = inr (inr x , y)
-- -- --   SplitBouquet→sumSphereBouquet (inr (push a i)) = push (inr a) i
-- -- --   SplitBouquet→sumSphereBouquet (push a i) = inl tt

-- -- --   Iso-sumSphereBouquet-SplitBouquet : Iso (SphereBouquet n ((Fin a ⊎ Fin b) ⊎ Fin c))
-- -- --                                           (SplitBouquet n a b c)
-- -- --   Iso.fun Iso-sumSphereBouquet-SplitBouquet = sumSphereBouquet→SplitBouquet
-- -- --   Iso.inv Iso-sumSphereBouquet-SplitBouquet = SplitBouquet→sumSphereBouquet
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inl (inl x))) = refl
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inl (inr x))) = refl
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inl (push a i))) = refl
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inr (inl x))) i = inl (push tt i)
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inr (inr x))) = refl
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inr (push a i))) j =
-- -- --     inl (compPath-filler' (push tt) (λ i → inr (push a i)) (~ j) i)
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (push a i)) j = inl (push tt (i ∧ j))
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inr (inl x)) = push tt
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inr (inr x)) = refl
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inr (push a i)) j =
-- -- --     compPath-filler' (push tt) (λ i → inr (push a i)) (~ j) i
-- -- --   Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (push a i) j = push tt (i ∧ j)
-- -- --   Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inl x) = refl
-- -- --   Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inr (inl (inl x) , y)) = refl
-- -- --   Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inr (inl (inr x) , y)) = refl
-- -- --   Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inr (inr x , y)) = refl
-- -- --   Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (push (inl (inl x)) i) = refl
-- -- --   Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (push (inl (inr x)) i) j =
-- -- --     SplitBouquet→sumSphereBouquet (inl (lUnit (λ i → inr (push x i)) (~ j) i))
-- -- --   Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (push (inr x) i) j =
-- -- --     SplitBouquet→sumSphereBouquet (compPath-filler' (push tt) (λ i → inr (push x i)) (~ j) i)


-- -- -- open import Cubical.Data.Nat.Order.Inductive
-- -- -- Pushout→Bouquet-pre∂ : ∀ {ℓ} (B : CWskel ℓ) (n : ℕ)
-- -- --   → Fin (CWskel-fields.card B (suc n)) × S₊ n
-- -- --   → SphereBouquet n (Fin (CWskel-fields.card B n))
-- -- -- Pushout→Bouquet-pre∂ B n x =
-- -- --   (Pushout→Bouquet n (CWskel-fields.card B n)
-- -- --         (CWskel-fields.α B n) (CWskel-fields.e B n)
-- -- --           (fst (CWskel-fields.e B n) (CWskel-fields.α B (suc n) x)))

-- -- -- -- module _ where
-- -- -- --   open FinSequenceMap renaming (fmap to ∣_∣)
-- -- -- --   open CWskel-fields
-- -- -- --   preFunctImproved : ∀ {ℓ ℓ'} {C : CWskel ℓ} {D : CWskel ℓ'}
-- -- -- --     (m : ℕ) (f : finCellMap m C D) (n' : Fin m)
-- -- -- --     → SphereBouquet (fst n')
-- -- -- --         (Fin (CWskel-fields.card C (fst n')))
-- -- -- --     → SphereBouquet (fst n')
-- -- -- --         (Fin (CWskel-fields.card D (fst n')))
-- -- -- --   preFunctImproved m f n' (inl x) = inl tt
-- -- -- --   preFunctImproved {C = C} {D} (suc n) f (zero , p) (inr (x , w)) =
-- -- -- --     inr ((fst (CW₁-discrete D) (∣ f ∣ fone (invEq (e C 0) (inr x)))) , w)
-- -- -- --   preFunctImproved n f (suc zero , p) (inr (x , base)) = inl tt
-- -- -- --   preFunctImproved {C = C} {D = D} (suc (suc n)) f (suc zero , p) (inr (x , loop i)) =
-- -- -- --      (cong G (push (∣ f ∣ (1 , p) (α C 1 (x , false)))
-- -- -- --            ∙ (λ i → inr (fcomm f (1 , p) (α C 1 (x , false)) i)))
-- -- -- --     ∙∙ cong (G ∘ inr ∘ ∣ f ∣ (fsuc (1 , tt)) ∘ invEq (e C 1)) (push (x , false))
-- -- -- --       ∙ cong (G ∘ inr ∘ ∣ f ∣ (fsuc (1 , tt)) ∘ invEq (e C 1)) (sym (push (x , true)))
-- -- -- --     ∙∙ sym (cong G (push (∣ f ∣ (1 , p) (α C 1 (x , true)))
-- -- -- --            ∙ (λ i → inr (fcomm f (1 , p) (α C 1 (x , true)) i))))) i
-- -- -- --     where
-- -- -- --     G = BouquetFuns.CTB 1 (D .snd .fst 1) (D .snd .snd .fst 1)
-- -- -- --           (D .snd .snd .snd .snd 1)
-- -- -- --   preFunctImproved n f (suc (suc s) , p) (inr (x , north)) = inl tt
-- -- -- --   preFunctImproved n f (suc (suc s) , p) (inr (x , south)) = inl tt
-- -- -- --   preFunctImproved {C = C} {D = D} (suc n') f (suc (suc n) , p) (inr (x , merid a i)) =
-- -- -- --     (cong G ((push (∣ f ∣ (suc (suc n) , <ᵗ-trans-suc p) (α C (suc (suc n)) (x , a)))
-- -- -- --             ∙ λ i → inr (fcomm f (suc (suc n) , p) (α C (suc (suc n)) (x , a)) i)))
-- -- -- --     ∙ cong G (λ j → inr (∣ f ∣ (fsuc (suc (suc n) , p))
-- -- -- --                       (invEq (e C (suc (suc n))) (push (x , a) j))))
-- -- -- --     ∙ {!!}) i
-- -- -- --     where
-- -- -- --     G = BouquetFuns.CTB (suc (suc n)) (D .snd .fst (suc (suc n))) (D .snd .snd .fst (suc (suc n)))
-- -- -- --           (D .snd .snd .snd .snd (suc (suc n)))
-- -- -- --   preFunctImproved {C = C} {D = D} (suc m) f (zero , p) (push a i) =
-- -- -- --     push (fst (CW₁-discrete D) (∣ f ∣ fone (invEq (e C 0) (inr a)))) i
-- -- -- --   preFunctImproved m f (suc zero , p) (push a i) = inl tt
-- -- -- --   preFunctImproved m f (suc (suc s) , p) (push a i) = inl tt

-- -- -- pre∂Improved : ∀ {ℓ} (B : CWskel ℓ) (n : ℕ)
-- -- --       → SphereBouquet (suc n) (Fin (preboundary.An+1 (strictCWskel B) n))
-- -- --       → SphereBouquet (suc n) (Fin (preboundary.An (strictCWskel B) n))
-- -- -- pre∂Improved B n (inl x) = inl tt
-- -- -- pre∂Improved B zero (inr (x , base)) = inl tt
-- -- -- pre∂Improved B zero (inr (x , loop i)) =
-- -- --   (cong (Iso.fun sphereBouquetSuspIso₀)
-- -- --     (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B zero)) (λ _ → S₊∙ zero)
-- -- --       (Pushout→Bouquet-pre∂ B zero (x , false)))
-- -- --   ∙ sym (cong (Iso.fun sphereBouquetSuspIso₀)
-- -- --     (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B zero)) (λ _ → S₊∙ zero)
-- -- --       (Pushout→Bouquet-pre∂ B zero (x , true))))) i
-- -- -- pre∂Improved B (suc n) (inr (x , north)) = inl tt
-- -- -- pre∂Improved B (suc n) (inr (x , south)) = inl tt
-- -- -- pre∂Improved B (suc n) (inr (x , merid a i)) =
-- -- --     Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n))) (λ _ → S₊∙ (suc n))
-- -- --       (Pushout→Bouquet-pre∂ B (suc n) (x , a)) i
-- -- -- pre∂Improved B zero (push a i) = inl tt
-- -- -- pre∂Improved B (suc n) (push a i) = inl tt

-- -- -- pre∂Improved≡ : ∀ {ℓ} (B : CWskel ℓ) (n : ℕ)
-- -- --   (x : SphereBouquet (suc n) (Fin (preboundary.An+1 B n)))
-- -- --   → preboundary.pre∂ B n x ≡ pre∂Improved B n x
-- -- -- pre∂Improved≡ B zero (inl x) = refl
-- -- -- pre∂Improved≡ B (suc n) (inl x) = refl
-- -- -- pre∂Improved≡ B zero (inr (x , base)) = refl
-- -- -- pre∂Improved≡ B zero (inr (x , loop i)) j =
-- -- --   hcomp (λ k →
-- -- --     λ {(i = i0) → Iso.fun sphereBouquetSuspIso₀ (w (push (preboundary.αn+1 B 0 (x , false)) (~ k ∧ ~ j)))
-- -- --      ; (i = i1) → Iso.fun sphereBouquetSuspIso₀ (w (push (preboundary.αn+1 B 0 (x , true)) (~ k)))
-- -- --      ; (j = i0) → Iso.fun sphereBouquetSuspIso₀
-- -- --                    (w (doubleCompPath-filler
-- -- --                      (push (preboundary.αn+1 B 0 (x , false)))
-- -- --                      (λ i → inr (invEq (CWskel-fields.e B (suc zero))
-- -- --                        ((push (x , false) ∙ sym (push (x , true))) i)))
-- -- --                      (sym (push (preboundary.αn+1 B 0 (x , true)))) k i))})
-- -- --         (Iso.fun sphereBouquetSuspIso₀ (w (push (preboundary.αn+1 B 0 (x , false)) (~ j ∨ i))))
-- -- --   where
-- -- --   w = (SuspBouquet→Bouquet (Fin (preboundary.An B 0)) (λ _ → S₊∙ zero))
-- -- --        ∘ (suspFun (preboundary.isoCofBouquet B 0))
-- -- --        ∘  (suspFun (to 0 cofibCW B))
-- -- --        ∘ (δ-pre (CW↪ B 1))

-- -- -- pre∂Improved≡ B (suc n) (inr (x , north)) = refl
-- -- -- pre∂Improved≡ B (suc n) (inr (x , south)) =
-- -- --    (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
-- -- --       (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , ptSn (suc n))))
-- -- -- pre∂Improved≡ B (suc n) (inr (x , merid a i)) j = h j i
-- -- --   where
-- -- --   open preboundary B (suc n)
-- -- --   h : Square (λ i → preboundary.pre∂ B (suc n) (inr (x , merid a i)))
-- -- --              (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
-- -- --                 (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , a)))
-- -- --              refl ((Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
-- -- --       (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , ptSn (suc n)))))
-- -- --   h = cong-∙∙ (SuspBouquet→Bouquet (Fin An) (λ _ → S₊∙ (suc n))
-- -- --             ∘ suspFun isoCofBouquet
-- -- --             ∘ suspFun (to suc n cofibCW B)
-- -- --             ∘ δ-pre (CW↪ B (suc (suc n))))
-- -- --             (push (αn+1 (x , a))) _ (sym (push (αn+1 (x , ptSn (suc n)))))
-- -- --     ∙ doubleCompPath≡compPath _ _ _ -- 
-- -- --     ∙ cong₂ _∙_ refl ((sym (lUnit _))) -- cong₂ _∙_ refl (sym (lUnit _)) ∙ refl
-- -- --     ◁ symP (compPath-filler (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
-- -- --                          (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , a)))
-- -- --                         (sym (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
-- -- --                          (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , ptSn (suc n))))))
-- -- -- pre∂Improved≡ B zero (push a i) = refl
-- -- -- pre∂Improved≡ B (suc n) (push a i) = refl

-- -- -- module MOOO (isEquivPushoutA→PushoutPushoutMapStrict : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
-- -- --   (f : cellMap B C)
-- -- --   (g : cellMap B D)
-- -- --    → (n : ℕ) → retract (PushoutPushoutMap→PushoutA f g n) (PushoutA→PushoutPushoutMap f g n)
-- -- --                × section (PushoutPushoutMap→PushoutA f g n) (PushoutA→PushoutPushoutMap f g n))
-- -- --    where
-- -- --   eCWPushout : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
-- -- --      (f : cellMap B C) (g : cellMap B D) (n : ℕ)
-- -- --      → pushoutA f g (suc (suc n)) ≃ Pushout (pushoutMapₛ f g n) (λ r → fst r)
-- -- --   eCWPushout f g n = isoToEquiv theIso
-- -- --     where
-- -- --     theIso : Iso _ _
-- -- --     Iso.fun theIso = PushoutA→PushoutPushoutMap f g n
-- -- --     Iso.inv theIso = PushoutPushoutMap→PushoutA f g n
-- -- --     Iso.rightInv theIso = isEquivPushoutA→PushoutPushoutMapStrict f g n .fst
-- -- --     Iso.leftInv theIso = isEquivPushoutA→PushoutPushoutMapStrict f g n .snd

-- -- --   PushoutCWSkel : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
-- -- --     (f : cellMap B C) (g : cellMap B D) → CWskel _
-- -- --   fst (PushoutCWSkel f g) = pushoutA f g
-- -- --   fst (snd (PushoutCWSkel f g)) = pushoutCells f g
-- -- --   fst (snd (snd (PushoutCWSkel f g))) = pushoutMap f g
-- -- --   fst (snd (snd (snd ((PushoutCWSkel {B = B}) f g)))) (lift t) =
-- -- --     fst (snd (snd (snd B))) t
-- -- --   snd (snd (snd (snd (PushoutCWSkel {B = B} {C = C} {D} f g)))) zero =
-- -- --     compEquiv (compEquiv (symPushout _ _)
-- -- --       (compEquiv (invEquiv (pushoutEquiv _ _ _ _
-- -- --         (propBiimpl→Equiv (λ())
-- -- --           (λ x → ⊥.rec (fst (snd (snd (snd B))) x)) (λ()) (fst (snd (snd (snd B)))))
-- -- --         (idEquiv _) (idEquiv _) (funExt λ()) (funExt λ())))
-- -- --         (compEquiv (invEquiv (isoToEquiv Pushout-⊎-Iso))
-- -- --         (compEquiv
-- -- --           (compEquiv (invEquiv ⊎-IdR-⊥-≃)
-- -- --             (isoToEquiv (⊎Iso (compIso (compIso
-- -- --               (⊎Iso (equivToIso (CW₁-discrete D))
-- -- --                 (equivToIso (CW₁-discrete C))) ⊎-swap-Iso)
-- -- --                   (Iso-Fin⊎Fin-Fin+))
-- -- --                     (iso (λ()) (λ()) (λ()) λ()))))
-- -- --           (isoToEquiv (Iso-Fin⊎Fin-Fin+ {m = zero}))))))
-- -- --       (compEquiv (isoToEquiv (PushoutEmptyFam (λ())
-- -- --         λ {(lift t) → fst (snd (snd (snd B))) t}))
-- -- --         (symPushout _ _))
-- -- --   snd (snd (snd (snd (PushoutCWSkel f g)))) (suc n) =
-- -- --     compEquiv (eCWPushout f g n)
-- -- --               (isoToEquiv (Iso-Pushoutα-PushoutPushoutMapₛ  f g n))


-- -- --   open import Cubical.Data.Unit
-- -- --   UnitCWskel : CWskel ℓ-zero
-- -- --   fst UnitCWskel zero = ⊥
-- -- --   fst UnitCWskel (suc n) = Unit
-- -- --   fst (snd UnitCWskel) zero = 1
-- -- --   fst (snd UnitCWskel) (suc n) = 0
-- -- --   fst (snd (snd UnitCWskel)) zero ()
-- -- --   fst (snd (snd UnitCWskel)) (suc n) t = tt
-- -- --   fst (snd (snd (snd UnitCWskel))) ()
-- -- --   snd (snd (snd (snd UnitCWskel))) zero =
-- -- --     compEquiv (isoToEquiv Iso-Unit-Fin1)
-- -- --       (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _))
-- -- --   snd (snd (snd (snd UnitCWskel))) (suc n) =
-- -- --     isoToEquiv (PushoutEmptyFam (λ()) λ())


-- -- --   terminalCW : ∀ {ℓ} {C : CWskel ℓ} → cellMap C UnitCWskel
-- -- --   SequenceMap.map (terminalCW {C = C}) zero = fst (snd (snd (snd C)))
-- -- --   SequenceMap.map terminalCW (suc n) _ = tt
-- -- --   SequenceMap.comm terminalCW _ _ = refl


-- -- --   module MIAU {ℓ ℓ'' : Level} {B' : CWskel ℓ} {D' : CWskel ℓ''}
-- -- --     (f : cellMap (strictCWskel B') (strictCWskel D')) where
-- -- --     private
-- -- --       B = strictCWskel B'
-- -- --       D = strictCWskel D'
-- -- --       C = UnitCWskel

-- -- --     open CWskel-fields
-- -- --     open SequenceMap renaming (map to ∣_∣)
-- -- --     open import Cubical.HITs.Wedge
-- -- --     open import Cubical.Foundations.Pointed

-- -- --     cofibCWskel : CWskel _
-- -- --     cofibCWskel = PushoutCWSkel terminalCW f


-- -- --     PushoutA→PushoutPushoutMap' : (n : ℕ) → pushoutA terminalCW f (suc (suc n))
-- -- --                        → Pushout (pushoutMapₛ terminalCW f n) (λ r → fst r)
-- -- --     PushoutA→PushoutPushoutMap' n (inl x) = inl (inl x)
-- -- --     PushoutA→PushoutPushoutMap' n (inr x) =
-- -- --       PushoutA→PushoutPushoutMapR terminalCW f n x
-- -- --     PushoutA→PushoutPushoutMap' n (push a i) =
-- -- --       (PushoutA→PushoutPushoutMapLR terminalCW f n a
-- -- --      ∙ cong (PushoutA→PushoutPushoutMapR terminalCW f n) (comm f (suc n) a)) i

-- -- --     PushoutA→PushoutPushoutMap'≡ : (n : ℕ) (x : _)
-- -- --       → PushoutA→PushoutPushoutMap terminalCW f n x ≡ PushoutA→PushoutPushoutMap' n x
-- -- --     PushoutA→PushoutPushoutMap'≡ n (inl x) = refl
-- -- --     PushoutA→PushoutPushoutMap'≡ n (inr x) = refl
-- -- --     PushoutA→PushoutPushoutMap'≡ n (push a i) k = help k i
-- -- --       where
-- -- --       help : cong (PushoutA→PushoutPushoutMap terminalCW f n) (push a) ≡ cong (PushoutA→PushoutPushoutMap' n) (push a)
-- -- --       help = cong₃ _∙∙_∙∙_
-- -- --         (cong (cong (PushoutA→PushoutPushoutMapL terminalCW f n)) (sym (rUnit refl)))
-- -- --         (sym (rUnit _))
-- -- --         ((cong (sym ∘ cong (PushoutA→PushoutPushoutMapR terminalCW f n)) (sym (rUnit _))))

-- -- --     -- SphereBouquetCellIso : (n m : ℕ) → Iso (SphereBouquet (suc n) (Fin (card cofibCWskel m)))
-- -- --     --                                          (SplitBouquet n (card C m) (card D m) (pushoutMidCells terminalCW f m))
-- -- --     -- SphereBouquetCellIso n m = compIso (sphereBouquetIso (suc n)) (Iso-sumSphereBouquet-SplitBouquet n) --  -- 

-- -- --     -- sphereBouquetSuspIso∙ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → Iso.fun (sphereBouquetSuspIso {A = A} {n}) north ≡ inl tt
-- -- --     -- sphereBouquetSuspIso∙ {n = zero} = refl
-- -- --     -- sphereBouquetSuspIso∙ {n = suc n} = refl

-- -- --     -- QuotCW : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Type ℓ 
-- -- --     -- QuotCW C n = cofib (CW↪ C n)

-- -- --     -- QuotCW∙ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Pointed ℓ 
-- -- --     -- QuotCW∙ C n = QuotCW C n , inl tt

-- -- --     -- bouquetFun1 : (n : ℕ) → SphereBouquet n (Fin (card cofibCWskel n)) → QuotCW cofibCWskel n
-- -- --     -- bouquetFun1 n = BouquetFuns.BTC n (card cofibCWskel n) (α cofibCWskel n) (e cofibCWskel n)

-- -- --     -- SphereBouquetCellEquiv : (n m : ℕ)
-- -- --     --   → SphereBouquet n (Fin (card cofibCWskel m)) ≃ (SplitBouquet n (card C m) (card D m) (pushoutMidCells terminalCW f m))
-- -- --     -- SphereBouquetCellEquiv n m = isoToEquiv (compIso (sphereBouquetIso n) (Iso-sumSphereBouquet-SplitBouquet n))

-- -- --     -- bouquetFun1' : (n : ℕ) → SplitBouquet n (card C n) (card D n) (pushoutMidCells terminalCW f n)
-- -- --     --                         → QuotCW cofibCWskel n
-- -- --     -- bouquetFun1' n = bouquetFun1 n ∘ invEq (SphereBouquetCellEquiv n n)

-- -- --     -- bouquetFun'-inl : (n : ℕ) → (SphereBouquet∙ (suc n) (Fin zero) ⋁ SphereBouquet∙ (suc n) (Fin (card D (suc n))))
-- -- --     --                            → (QuotCW D (suc n))
-- -- --     -- bouquetFun'-inl n (inl x) = {!!}
-- -- --     -- bouquetFun'-inl n (inr x) = {!!}
-- -- --     -- bouquetFun'-inl n (push a i) = {!!}

-- -- --     -- bouquetFun' : (n : ℕ) → SplitBouquet (suc n) zero (card D (suc n)) (pushoutMidCells terminalCW f (suc n))
-- -- --     --                         → (QuotCW∙ D (suc n)) ⋁ Susp∙ (QuotCW B n)
-- -- --     -- bouquetFun' n (inl x) = inl (bouquetFun'-inl n x)
-- -- --     -- bouquetFun' n (inr x) = {!!}
-- -- --     -- bouquetFun' n (push a i) = {!!}

-- -- --     -- SphereBouquetSplit : (n : ℕ) → Type
-- -- --     -- SphereBouquetSplit n = SphereBouquet (suc (suc n)) (Fin (card D (suc (suc n))) ⊎ Fin (card B (suc n)))

-- -- --     -- cofibskel' : (n : ℕ) → Type _
-- -- --     -- cofibskel' n = Pushout (pushoutMapₛ terminalCW f n) fst

-- -- --     -- Iso-cofibskel' : (n : ℕ) → (fst cofibCWskel (suc (suc n))) ≃ (cofibskel' n)
-- -- --     -- Iso-cofibskel' = eCWPushout terminalCW f

-- -- --     -- cofibskel'↑ : (n : ℕ) → cofibskel' n → cofibskel' (suc n)
-- -- --     -- cofibskel'↑ n x = inl (invEq (Iso-cofibskel' n) x)

-- -- --     -- cofibskelQuot : (n : ℕ) → Type _
-- -- --     -- cofibskelQuot n = cofib {A = cofibskel' n} {B = cofibskel' (suc n)} (cofibskel'↑ n)

-- -- --     -- -- bouquetFun2Inr : (n : ℕ) (x : Fin (card D (suc (suc n))) ⊎ Fin (card B (suc n))) → S₊ (suc (suc n)) → cofibskel' (suc n)
-- -- --     -- -- bouquetFun2Inr n x north = inl {!!}
-- -- --     -- -- bouquetFun2Inr n x south = {!!}
-- -- --     -- -- bouquetFun2Inr n x (merid a i) = {!!}

-- -- --     -- -- bouquetFun2 : (n : ℕ) → SplitBouquet n zero (card D (suc (suc n))) (pushoutMidCells terminalCW f (suc (suc n)))
-- -- --     -- --                         → cofibskelQuot n
-- -- --     -- -- bouquetFun2 n (inl x) = {!!}
-- -- --     -- -- bouquetFun2 n (inr x) = {!x!}
-- -- --     -- -- bouquetFun2 n (push a i) = {!!}

-- -- --     -- cofibskelQuot≃ : (n : ℕ) → cofibskelQuot n ≃ QuotCW cofibCWskel (suc (suc n))
-- -- --     -- cofibskelQuot≃ n =
-- -- --     --   pushoutEquiv _ _ _ _
-- -- --     --   (invEquiv (Iso-cofibskel' n)) (idEquiv _) (invEquiv (Iso-cofibskel' (suc n)))
-- -- --     --   (λ _ _ → tt) (funExt λ x → refl)

-- -- --     -- cofib→wedgeInr : (n : ℕ) → cofibskel' (suc n) → (QuotCW∙ D (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc n))
-- -- --     -- cofib→wedgeInr n (inl x) = inl (inl tt)
-- -- --     -- cofib→wedgeInr n (inr (inl (inr x))) = inl (inr (inr x))
-- -- --     -- cofib→wedgeInr n (inr (inr x)) = inr north
-- -- --     -- cofib→wedgeInr n (push (inl (inr x) , b) i) =
-- -- --     --   ((λ i → inl (push (α D (suc (suc n)) (x , Iso.inv (IsoSphereSusp (suc n)) b)) i)) ∙ (λ i → inl (inr (push (x , Iso.inv (IsoSphereSusp (suc n)) b) i)))) i
-- -- --     -- cofib→wedgeInr n (push (inr x , b) i) = (push tt ∙ λ i → inr (toSusp (_ , inl tt) (haha b x) i)) i
-- -- --     --   where
-- -- --     --   haha : (x : Susp (S₊ n)) (y : A B (suc n)) → QuotCW B (suc n)
-- -- --     --   haha north y = inl tt
-- -- --     --   haha south y = inr (inr y)
-- -- --     --   haha (merid a i) y =
-- -- --     --     (push (α B (suc n) (y , a)) ∙ λ i → inr ((push (y , a)) i)) i

-- -- --     -- cofib→wedge : (n : ℕ) → cofibskelQuot n → (QuotCW∙ D (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc n))
-- -- --     -- cofib→wedge n (inl x) = inl (inl tt)
-- -- --     -- cofib→wedge n (inr x) = cofib→wedgeInr n x
-- -- --     -- cofib→wedge n (push a i) = inl (inl tt)

    


    
