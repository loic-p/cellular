{-# OPTIONS --cubical --lossy-unification #-}
module Pushout.CWPushout where

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
open import Cubical.CW.Homology.Base
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Foundations.Pointed
open import Cubical.HITs.Wedge

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
       (CW↪ C n ∘ ∣ f ∣ n) (CW↪ D n ∘ ∣ g ∣ n)

  pushoutA' : ℕ → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') 
  pushoutA' zero = Lift {ℓ} {ℓ-max ℓ' ℓ''} (B .fst zero)
  pushoutA' (suc n) =
    Pushout {A = fst B n} {B = fst C (suc n)} {C = fst D (suc n)}
       (∣ f ∣ (suc n) ∘ CW↪ B n) (∣ g ∣ (suc n) ∘ CW↪ B n)

  pushoutMapₛ' : (n : ℕ) → (((A C (suc n)) ⊎ (A D (suc n))) ⊎ (A B n)) × (Susp (S⁻ n)) → pushoutA' (suc n)
  pushoutMapₛ' n (inl (inl c) , x) =  inl (α C (suc n) (c , (Iso.inv (IsoSphereSusp n) x)))
  pushoutMapₛ' n (inl (inr d) , x) = inr (α D (suc n) (d , (Iso.inv (IsoSphereSusp n) x)))
  pushoutMapₛ' n (inr b , north) = inl (∣ f ∣ (suc n) (invEq (e B n) (inr b)))
  pushoutMapₛ' n (inr b , south) = inr (∣ g ∣ (suc n) (invEq (e B n) (inr b)))
  pushoutMapₛ' n (inr b , merid x i) =
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

  pushoutMapₛ : (n : ℕ) → (((A C (suc n)) ⊎ (A D (suc n))) ⊎ (A B n)) × (Susp (S⁻ n)) → pushoutA (suc n)
  pushoutMapₛ n (inl (inl c) , x) =  inl (α C (suc n) (c , (Iso.inv (IsoSphereSusp n) x)))
  pushoutMapₛ n (inl (inr d) , x) = inr (α D (suc n) (d , (Iso.inv (IsoSphereSusp n) x)))
  pushoutMapₛ n (inr b , north) = inl (∣ f ∣ (suc n) (invEq (e B n) (inr b)))
  pushoutMapₛ n (inr b , south) = inr (∣ g ∣ (suc n) (invEq (e B n) (inr b)))
  pushoutMapₛ n (inr b , merid x i) =
    (((λ j → inl ((cong (∣ f ∣ (suc n)) (λ j → invEq (e B n) (push (b , x) (~ j)))
      ∙ sym (comm f n (α B n (b , x)))) j))
    ∙∙ push (α B n (b , x))
    ∙∙ λ j → inr ((cong (∣ g ∣ (suc n)) (λ j → invEq (e B n) (push (b , x) (~ j)))
      ∙ sym (comm g n (α B n (b , x)))) (~ j)))) i


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
  Iso-Pushoutα-PushoutPushoutMapₛ n = pushoutIso _ _ _ _
    (Σ-cong-equiv (invEquiv (finSplit3≃ _ _ _))
      λ _ → isoToEquiv (invIso (IsoSphereSusp n)))
    (idEquiv _)
    (invEquiv (finSplit3≃ _ _ _))
    (funExt λ x → cong (pushoutMapₛ n) (ΣPathP
      (sym (secEq (finSplit3≃ _ _ _) (fst x))
      , sym (Iso.rightInv (IsoSphereSusp n) (snd x)))))
    refl

  pushoutMap : (n : ℕ) → (Fin (pushoutCells n)) × (S⁻ n) → pushoutA n
  pushoutMap zero = pushoutMap₀
  pushoutMap (suc n) = pushoutα> n

  module _ (n : ℕ) where
    open 3x3-span
    span1 : 3x3-span
    A00 span1 = Fin (card B n)
    A02 span1 = ⊥
    A04 span1 = Fin (card C (suc n)) ⊎ Fin (card D (suc n))
    A20 span1 = Fin (card B n) × Susp (S⁻ n)
    A22 span1 = ⊥
    A24 span1 = (Fin (card C (suc n)) ⊎ Fin (card D (suc n))) × Susp (S⁻ n)
    A40 span1 = pushoutA (suc n)
    A42 span1  = (Fin (card C (suc n)) ⊎ Fin (card D (suc n))) × Susp (S⁻ n)
    A44 span1 = (Fin (card C (suc n)) ⊎ Fin (card D (suc n))) × Susp (S⁻ n)
    f10 span1 = fst
    f12 span1 = λ()
    f14 span1 = fst
    f30 span1 = λ xs → pushoutMapₛ n ((inr (fst xs)) , (snd xs))
    f32 span1 = λ()
    f34 span1 = idfun _
    f01 span1 = λ()
    f21 span1 = λ()
    f41 span1 = λ xs → pushoutMapₛ n ((inl (fst xs)) , (snd xs))
    f03 span1 = λ()
    f23 span1 = λ()
    f43 span1 = idfun _
    H11 span1 = λ()
    H13 span1 = λ()
    H31 span1 = λ()
    H33 span1 = λ()
  
    Iso1 : Iso (Pushout (pushoutMapₛ n) fst)
               (A○□ span1)
    Iso1 =
      compIso (pushoutIso _ _ _ _ (isoToEquiv iso1)
                (isoToEquiv iso2)
                (isoToEquiv iso3)
                (funExt (λ { (inl x , s) → push (x , s)
                           ; (inr x , s) → refl}))
                (funExt λ { (inl x , s) → refl ; (inr x , s) → refl}))
      (equivToIso (symPushout _ _))
      where
      iso3 : Iso ((A C (suc n) ⊎ A D (suc n)) ⊎ A B n) (A0□ span1)
      Iso.fun iso3 (inl x) = inr x
      Iso.fun iso3 (inr x) = inl x
      Iso.inv iso3 (inl x) = inr x
      Iso.inv iso3 (inr x) = inl x
      Iso.rightInv iso3 (inl x) = refl
      Iso.rightInv iso3 (inr x) = refl
      Iso.leftInv iso3 (inl x) = refl
      Iso.leftInv iso3 (inr x) = refl

      iso2 : Iso (pushoutA (suc n)) (A4□ span1)
      iso2 = invIso (compIso
        (equivToIso (symPushout _ _))
         (PushoutAlongEquiv (idEquiv _) _))

      iso1 : Iso (((A C (suc n) ⊎ A D (suc n)) ⊎ A B n) × Susp (S⁻ n))
                 (A2□ span1)
      Iso.fun iso1 (inl x , s) = inr (x , s)
      Iso.fun iso1 (inr x , s) = inl (x , s)
      Iso.inv iso1 (inl (x , s)) = (inr x) , s
      Iso.inv iso1 (inr (x , s)) = (inl x) , s
      Iso.rightInv iso1 (inl x) = refl
      Iso.rightInv iso1 (inr x) = refl
      Iso.leftInv iso1 (inl x , s) = refl
      Iso.leftInv iso1 (inr x , s) = refl

    T2 = (Pushout {A = (Fin (card C (suc n)) ⊎ Fin (card D (suc n)))
                           × Susp (S⁻ n)}
                        {B = A□0 span1}
                (λ xs → inr (pushoutMapₛ n ((inl (fst xs)) , (snd xs))))
                fst)

    Iso2 : Iso (A□○ span1) T2
    Iso2 =
      pushoutIso _ _ _ _
      (compEquiv (symPushout _ _)
        (isoToEquiv (invIso (PushoutEmptyFam (λ()) λ()))))
      (idEquiv _)
      (compEquiv (symPushout _ _)
        (isoToEquiv (PushoutAlongEquiv (idEquiv _) _)))
      (funExt λ { (inr x) → refl})
      (funExt λ { (inr x) → refl})

    firstRetwriteIso : Iso (Pushout (pushoutMapₛ n) fst) T2
    firstRetwriteIso = compIso Iso1 (compIso (invIso (3x3-Iso span1)) Iso2)

  module _ (n : ℕ) where
    open 3x3-span
    span2 : 3x3-span
    A00 span2 = Fin (card B n)
    A02 span2 = Fin (card B n)
    A04 span2 = Fin (card B n)
    A20 span2 = Fin (card B n)
    A22 span2 = Fin (card B n) × S⁻ n
    A24 span2 = Fin (card B n)
    A40 span2 = fst C (suc n)
    A42 span2 = fst B n
    A44 span2 = fst D (suc n)
    f10 span2 = idfun _
    f12 span2 = fst
    f14 span2 = idfun _
    f30 span2 = λ x → ∣ f ∣ (suc n) (invEq (e B n) (inr x))
    f32 span2 = α B n
    f34 span2 = λ x → ∣ g ∣ (suc n) (invEq (e B n) (inr x))
    f01 span2 = idfun _
    f21 span2 = fst
    f41 span2 = λ x → CW↪ C n (∣ f ∣ n x)
    f03 span2 = idfun _
    f23 span2 = fst
    f43 span2 = λ x → CW↪ D n (∣ g ∣ n x)
    H11 span2 = λ _ → refl
    H13 span2 = λ _ → refl
    H31 span2 = λ x → sym (sym (cong (∣ f ∣ (suc n) ∘ invEq (e B n)) (push x)) ∙ sym (comm f n (α B n x)))
    H33 span2 = λ x → sym (sym (cong (∣ g ∣ (suc n) ∘ invEq (e B n)) (push x)) ∙ sym (comm g n (α B n x)))

    Iso3 : Iso (A○□ span2) (A□0 (span1 n))
    Iso3 =
      (pushoutIso _ _ _ _
        (isoToEquiv iso1)
        (isoToEquiv (PushoutAlongEquiv (idEquiv _) _))
        (idEquiv _)
        (funExt (λ { (inl x) → refl
                   ; (inr x) → refl
                   ; (push a i) j → PushoutAlongEquiv→ (idEquiv (Fin (card B n))) (idfun _)
                                      (rUnit (push (fst a)) (~ j) i)}))
        (funExt λ { (inl x) → refl
                   ; (inr x) → refl
                   ; (push a i) → refl}))
      where

      iso1 : Iso (A2□ span2) (Fin (card B n) × Susp (S⁻ n))
      Iso.fun iso1 (inl x) = x , north
      Iso.fun iso1 (inr x) = x , south
      Iso.fun iso1 (push a i) = fst a , (merid (snd a) i)
      Iso.inv iso1 (x , north) = inl x
      Iso.inv iso1 (x , south) = inr x
      Iso.inv iso1 (x , merid a i) = push (x , a) i
      Iso.rightInv iso1 (x , north) = refl
      Iso.rightInv iso1 (x , south) = refl
      Iso.rightInv iso1 (x , merid a i) = refl
      Iso.leftInv iso1 (inl x) = refl
      Iso.leftInv iso1 (inr x) = refl
      Iso.leftInv iso1 (push a i) = refl

    Iso4 : Iso (A□○ span2)
               (Pushout {A = fst B (suc n)} (∣ f ∣ (suc n) ) (∣ g ∣ (suc n)))
    Iso4 = pushoutIso _ _ _ _
      (compEquiv (symPushout _ _) (invEquiv (e B n)))
      (isoToEquiv (PushoutAlongEquiv (idEquiv _) _))
      (isoToEquiv (PushoutAlongEquiv (idEquiv _) _))
      (funExt (λ { (inl x) → refl
                 ; (inr x) → comm f n x
                 ; (push a i) j → lem1 a j i}))
      (funExt λ { (inl x) → refl
                 ; (inr x) → comm g n x
                 ; (push a i) j → lem2 a j i})
      where
      module _ (a : Fin (card B n) × S⁻ n) where
        lem1 : Square (cong ((PushoutAlongEquiv→ (idEquiv (Fin (card B n)))
                            (λ x → ∣ f ∣ (suc n) (invEq (e B n) (inr x)))))
                         (cong (f□1 span2) (push a)))
                    (cong (∣ f ∣ (suc n) ∘ invEq (e B n) ) (sym (push a)))
                    refl
                    (comm f n (α B n a))
        lem1 =
          (cong-∙ (PushoutAlongEquiv→ (idEquiv (Fin (card B n)))
                   (λ x → ∣ f ∣ (suc n) (invEq (e B n) (inr x))))
                  (push (fst a))
                  _
                ∙ sym (lUnit _))
          ◁ symP (compPath-filler (cong (∣ f ∣ (suc n) ∘ invEq (e B n)) (sym (push a)))
                             (sym (comm f n (α B n a))))

        lem2 : Square (cong ((PushoutAlongEquiv→ (idEquiv (Fin (card B n)))
                            (λ x → ∣ g ∣ (suc n) (invEq (e B n) (inr x)))))
                         (cong (f□3 span2) (push a)))
                    (cong (∣ g ∣ (suc n) ∘ invEq (e B n)) (sym (push a)))
                    refl
                    (comm g n (α B n a))
        lem2 =
          (cong-∙ (PushoutAlongEquiv→ (idEquiv (Fin (card B n)))
                   (λ x → ∣ g ∣ (suc n) (invEq (e B n) (inr x))))
                  (push (fst a))
                  _
                ∙ sym (lUnit _))
          ◁ symP (compPath-filler (cong (∣ g ∣ (suc n) ∘ invEq (e B n)) (sym (push a)))
                             (sym (comm g n (α B n a))))

  module _ (n : ℕ) where
    open 3x3-span
    span3 : 3x3-span
    A00 span3 = Fin (card C (suc n))
    A02 span3 = ⊥
    A04 span3 = Fin (card D (suc n))
    A20 span3 = Fin (card C (suc n)) × Susp (S⁻ n)
    A22 span3 = ⊥
    A24 span3 = Fin (card D (suc n)) × Susp (S⁻ n)
    A40 span3 = fst C (suc n)
    A42 span3 = fst B (suc n)
    A44 span3 = fst D (suc n)
    f10 span3 = fst
    f12 span3 = λ()
    f14 span3 = fst
    f30 span3 = λ x → α C (suc n) (fst x , Iso.inv (IsoSphereSusp n) (snd x))
    f32 span3 = λ()
    f34 span3 = λ x → α D (suc n) (fst x , Iso.inv (IsoSphereSusp n) (snd x))
    f01 span3 = λ()
    f21 span3 = λ()
    f41 span3 = ∣ f ∣ (suc n)
    f03 span3 = λ()
    f23 span3 = λ()
    f43 span3 = ∣ g ∣ (suc n)
    H11 span3 = λ()
    H13 span3 = λ()
    H31 span3 = λ()
    H33 span3 = λ()

    Iso5 : Iso (A□○ span3) (pushoutA (suc (suc n)))
    Iso5 = 
      (pushoutIso _ _ _ _
      (compEquiv (symPushout _ _)
        (isoToEquiv (invIso (PushoutEmptyFam (λ()) λ()))))
        (compEquiv (compEquiv (symPushout _ _)
          (pushoutEquiv _ _ _ _
            (Σ-cong-equiv-snd
              (λ _ → invEquiv (isoToEquiv (IsoSphereSusp n))))
                (idEquiv _) (idEquiv _)
                  (λ i x → α C (suc n) (fst x , Iso.inv (IsoSphereSusp n) (snd x)))
                  λ _ x → fst x))
          (invEquiv (e C (suc n))))
        (compEquiv (compEquiv (symPushout _ _)
          (pushoutEquiv _ _ _ _
            (Σ-cong-equiv-snd
              (λ _ → invEquiv (isoToEquiv (IsoSphereSusp n))))
                (idEquiv _) (idEquiv _)
                  (λ i x → α D (suc n) (fst x , Iso.inv (IsoSphereSusp n) (snd x)))
                  λ _ x → fst x))
          (invEquiv (e D (suc n))))
        (funExt (λ { (inr x) → refl}))
        (funExt (λ { (inr x) → refl})))

    T3 : Type _
    T3 = Pushout {A = (Fin (card C (suc n)) ⊎ Fin (card D (suc n)))
                            × Susp (S⁻ n)}
                        {B = Pushout (∣ f ∣ (suc n)) (∣ g ∣ (suc n))}
                (uncurry (⊎.rec
                  (λ x y → inl (α C (suc n) (x , Iso.inv (IsoSphereSusp n) y)))
                  (λ x y → inr (α D (suc n) (x , Iso.inv (IsoSphereSusp n) y)))))
                fst

    T4 : Type _
    T4 = Pushout {A = (Fin (card C (suc n)) ⊎ Fin (card D (suc n)))
                            × Susp (S⁻ n)}
                        {B = Pushout (∣ f ∣ (suc n)) (∣ g ∣ (suc n))}
                (uncurry (⊎.rec
                  (λ x y → inl (α C (suc n) (x , Iso.inv (IsoSphereSusp n) y)))
                  (λ x y → inr (α D (suc n) (x , Iso.inv (IsoSphereSusp n) y)))))
                fst

    Iso6 : Iso (A○□ span3) T3
    Iso6 = compIso (equivToIso (symPushout _ _))
      (pushoutIso _ _ _ _
        (compEquiv (isoToEquiv (invIso Pushout-⊎-Iso))
          (invEquiv (isoToEquiv Σ⊎Iso)))
        (idEquiv _)
          (isoToEquiv (invIso Pushout-⊎-Iso))
        (funExt (λ { (inl x) → refl ; (inr x) → refl}))
        (funExt λ { (inl x) → refl ; (inr x) → refl}))


  open 3x3-span
  T3≅T2 : (n : ℕ) → Iso (T3 n) (T2 n)
  T3≅T2 n = pushoutIso _ _ _ _
    (idEquiv _)
    (isoToEquiv
      (compIso
        (compIso (invIso
          (Iso4 n)) (3x3-Iso (span2 n)))
        (Iso3 n)))
    (idEquiv _)
    (funExt (λ { (inl x , y) → refl
               ; (inr x , y) → refl}))
    λ _ x → fst x

  isCWPushoutIsoPre : (n : ℕ)
    → Iso (pushoutA (suc (suc n)))
           (Pushout (pushoutMapₛ n) fst)
  isCWPushoutIsoPre n =
    compIso (invIso (Iso5 n))
     (compIso (3x3-Iso (span3 n))
       (compIso (Iso6 n)
        (compIso
         (compIso
          (compIso (T3≅T2 n)
            (invIso (Iso2 n)))
              (3x3-Iso (span1 n)))
               (invIso (Iso1 n)))))

  isCWPushoutIso : (n : ℕ)
    → Iso (pushoutA (suc (suc n)))
           (Pushout (pushoutα> n) fst)
  isCWPushoutIso n =
    compIso (isCWPushoutIsoPre n)
      (Iso-Pushoutα-PushoutPushoutMapₛ n)

  M1L : (n : ℕ) → Pushout (α C (suc n)) fst → Pushout (pushoutMapₛ' n) fst
  M1L n (inl x) = inl (inl x)
  M1L n (inr x) = inr ((inl (inl x)))
  M1L n (push a i) =
    ((λ i → inl (inl (α C (suc n) (fst a , Iso.leftInv (IsoSphereSusp n) (snd a) (~ i)))))
    ∙ push (((inl (inl (fst a)))) , Iso.fun (IsoSphereSusp n) (snd a))) i

  M1R : (n : ℕ) → Pushout (α D (suc n)) fst → Pushout (pushoutMapₛ' n) fst
  M1R n (inl x) = inl (inr x)
  M1R n (inr x) = inr ((inl (inr x)))
  M1R n (push a i) =
    ((λ i → inl (inr (α D (suc n) (fst a , Iso.leftInv (IsoSphereSusp n) (snd a) (~ i)))))
    ∙ push (((inl (inr (fst a)))) , Iso.fun (IsoSphereSusp n) (snd a))) i

  M1LR : (n : ℕ) (b : Pushout (α B n) fst)
    → Path (Pushout (pushoutMapₛ' n) fst)
            (inl (inl (∣ f ∣ (suc n) (invEq (e B n) b)))) (inl (inr (∣ g ∣ (suc n) (invEq (e B n) b))))
  M1LR n (inl x) i = inl (push x i)
  M1LR n (inr x) = push ((inr x) , north) ∙∙ refl ∙∙ sym (push ((inr x) , south))
  M1LR n (push (t , s) i) j =
    hcomp (λ k → λ {(i = i0) → inl (doubleCompPath-filler (λ i → inl (∣ f ∣ (suc n) (invEq (e B n) (push (t , s) (~ i)))))
                                                           (push (α B n (t , s)))
                                                           (λ i → inr (∣ g ∣ (suc n) (invEq (e B n) (push (t , s) i)))) (~ k) j)
                   ; (i = i1) → doubleCompPath-filler (push ((inr t) , north)) refl (sym (push ((inr t) , south))) k j
                   ; (j = i0) → invSides-filler (push (inr t , north))
                                                 (λ i → inl (inl (∣ f ∣ (suc n) (invEq (e B n) (push (t , s) (~ i)))))) k i
                   ; (j = i1) → invSides-filler (push (inr t , south))
                                                 (λ i → inl (inr (∣ g ∣ (suc n) (invEq (e B n) (push (t , s) (~ i)))))) k i})
          ((push (inr t , merid s j)) i)


  M1 : (n : ℕ) → (pushoutA (suc (suc n))) → (Pushout (pushoutMapₛ' n) fst)
  M1 n (inl x) = M1L n (fst (e C (suc n)) x)
  M1 n (inr x) = M1R n (fst (e D (suc n)) x)
  M1 n (push a i) =
      ((λ i → M1L n (secEq (e C (suc n)) (inl (∣ f ∣ (suc n) a)) i))
    ∙∙ (λ i →((λ i → inl (inl (∣ f ∣ (suc n) (retEq (e B n) a (~ i)))))
    ∙∙ M1LR n (fst (e B n) a)
    ∙∙ λ i → inl (inr (∣ g ∣ (suc n) (retEq (e B n) a i)))) i)
    ∙∙ λ i → M1R n (secEq (e D (suc n)) (inl (∣ g ∣ (suc n) a)) (~ i))) i

  open import Cubical.CW.Properties
  isCWPushoutIso₀ : Iso (pushoutA (suc zero)) (Pushout pushoutMap₀ fst)
  isCWPushoutIso₀ =
    compIso
      (compIso
        (compIso
          (compIso
          (invIso (pushoutIso _ _ _ _
            (propBiimpl→Equiv isProp⊥
              (λ x → ⊥.rec (fst (snd (snd (snd B))) x))
              (λ()) (fst (snd (snd (snd B)))))
            (invEquiv (CW₁-discrete C))
            (invEquiv (CW₁-discrete D))
            (funExt λ ()) (funExt λ())))
           (invIso Pushout-⊎-Iso))
          Iso-Fin⊎Fin-Fin+)
        (compIso (compIso (compIso (invIso (⊎-IdR-⊥-Iso))
          (⊎Iso idIso (equivToIso (propBiimpl→Equiv isProp⊥ (λ()) (λ()) λ()))))
          (Iso-Fin⊎Fin-Fin+ {m = zero}))
          (PushoutEmptyFam (λ()) λ {(lift t) → fst (snd (snd (snd B))) t})))
      (equivToIso (symPushout _ _))

  PushoutCWskel : CWskel _
  fst PushoutCWskel = pushoutA
  fst (snd PushoutCWskel) = pushoutCells
  fst (snd (snd PushoutCWskel)) = pushoutMap
  fst (snd (snd (snd PushoutCWskel))) (lift t) = fst (snd (snd (snd B))) t
  snd (snd (snd (snd PushoutCWskel))) zero = isoToEquiv isCWPushoutIso₀
  snd (snd (snd (snd PushoutCWskel))) (suc n) = isoToEquiv (isCWPushoutIso n)

  inlCellMap : cellMap C PushoutCWskel
  ∣ inlCellMap ∣ zero x = ⊥.rec (fst (snd (snd (snd C))) x)
  ∣ inlCellMap ∣ (suc n) x = inl x
  comm inlCellMap zero x = ⊥.rec (fst (snd (snd (snd C))) x)
  comm inlCellMap (suc n) x = refl

  inrCellMap : cellMap D PushoutCWskel
  ∣ inrCellMap ∣ zero x = ⊥.rec (fst (snd (snd (snd D))) x)
  ∣ inrCellMap ∣ (suc n) x = inr x
  comm inrCellMap zero x = ⊥.rec (fst (snd (snd (snd D))) x)
  comm inrCellMap (suc n) x = refl

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

  open import Cubical.HITs.Wedge
  open import Cubical.Foundations.Pointed
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

  SphereBouquetCellIso : (n m : ℕ) → Iso (SphereBouquet (suc n) (Fin (pushoutCells m)))
                                           (SplitBouquet n (card C m) (card D m) (pushoutMidCells m))
  SphereBouquetCellIso n m = compIso (sphereBouquetIso n) (Iso-sumSphereBouquet-SplitBouquet n) -- 


  open import Hurewicz.random
  open import Cubical.HITs.SphereBouquet.Degree

  projC : {n m : ℕ} → SphereBouquet (suc n) (Fin (pushoutCells m))
        → SphereBouquet (suc n) (Fin (card C m))
  projC {n = n} {m} = (foldL ∘ foldL) ∘ Iso.fun (SphereBouquetCellIso n m)

  sphereBouquetSuspIso∙ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → Iso.fun (sphereBouquetSuspIso {A = A} {n}) north ≡ inl tt
  sphereBouquetSuspIso∙ {n = zero} = refl
  sphereBouquetSuspIso∙ {n = suc n} = refl

  bouquetSusp→∙ : (n : ℕ) → bouquetSusp→
      (prefunctoriality.bouquetFunct (suc n)
       (cellMap→finCellMap (suc n) f) flast)
      (snd (SphereBouquet∙ (suc n) (Fin (pushoutMidCells (suc n)))))
      ≡ inl tt
  bouquetSusp→∙ zero = refl
  bouquetSusp→∙ (suc n) = refl

  Test : (n : ℕ) (x : Fin (preboundary.An+1 PushoutCWskel (suc n)))
    → fst (S₊∙ (suc (suc n))) → Susp (fst PushoutCWskel (suc (suc n)))
  Test n x z = δ-pre (CW↪ PushoutCWskel (suc (suc n)))
    (preBTC (suc (suc n)) (preboundary.An+1 PushoutCWskel (suc n))
        (preboundary.αn+1 PushoutCWskel (suc n))
        (snd PushoutCWskel .snd .snd .snd (suc (suc n))) x .fst z)

  mainFun : (n : ℕ) (x : Fin (card C (suc (suc n))))
    → SplitBouquet (suc n) (card C (suc (suc n)))
      (card D (suc (suc n))) (card B (suc n)) -- S₊ (suc (suc n))
    → SphereBouquet (suc (suc n)) (Fin (preboundary.An PushoutCWskel (suc n)))
  mainFun n x = (preboundary.pre∂ PushoutCWskel (suc n) ∘
          Iso.inv (SphereBouquetCellIso (suc n) (suc (suc n))))

  pushoutMapₛ-inr∙ : (n : ℕ) (x : _) → pushoutMapₛ (suc n) (x , north) ≡ inl {!∣ f ∣ (suc (suc n)) (invEq !}
  pushoutMapₛ-inr∙ = {!!}

  mainFun' :  (n : ℕ) (x : Fin (card C (suc (suc n))))
    → S₊ (suc (suc n)) → SphereBouquet (suc (suc n)) (Fin (preboundary.An PushoutCWskel (suc n)))
  mainFun' n x y = {!!} -- inr (invEq (finSplit3≃ {!!} {!!} {!!}) {!inl (inl x)!} , y)

  Test* : (n : ℕ) (x : Fin (preboundary.An+1 PushoutCWskel (suc n))) (a : _)
    → cong (suspFun (preboundary.isoCofBouquet PushoutCWskel (suc n)))
        (cong (suspFun (to suc n cofibCW PushoutCWskel)) (cong (Test n x) (merid a)))
     ≡ {!!}
  Test* n x a =
    cong (cong (suspFun (preboundary.isoCofBouquet PushoutCWskel (suc n))))
     (cong (cong (suspFun (to suc n cofibCW PushoutCWskel)))
    (cong-∙∙ (δ-pre (CW↪ PushoutCWskel (suc (suc n)))) _ _ _
              ∙ (λ i → merid (preboundary.αn+1 PushoutCWskel (suc n) (x , a))
                           ∙∙ ( λ j → merid (preboundary.αn+1 PushoutCWskel (suc n) (x , ptSn (suc n))) (~ j ∨ ~ i))
                           ∙∙ λ j → merid (preboundary.αn+1 PushoutCWskel (suc n) (x , ptSn (suc n))) (~ j ∧ ~ i))
              ∙ sym (compPath≡compPath' _ _)
              ∙ cong₂ _∙_ refl (cong (sym ∘ merid) (cong (pushoutMapₛ (suc n)) (ΣPathP (refl
                , sym (cong (Iso.fun (IsoSucSphereSusp n)) (IsoSucSphereSusp∙ n))
                  ∙ Iso.rightInv ((IsoSucSphereSusp n)) north)) ∙ refl)))
              ∙ cong-∙ (suspFun (to suc n cofibCW PushoutCWskel))
                  (merid (preboundary.αn+1 PushoutCWskel (suc n) (x , a)))
                  (sym (merid (pushoutMapₛ (suc n) (Iso.fun (⊎Iso (invIso Iso-Fin⊎Fin-Fin+) idIso)
                                                (Iso.inv Iso-Fin⊎Fin-Fin+ x) , north))))
             ∙ refl)
    ∙ cong-∙ (suspFun (preboundary.isoCofBouquet PushoutCWskel (suc n)))
             (merid (inr (preboundary.αn+1 PushoutCWskel (suc n) (x , a))))
             (sym (merid (inr (pushoutMapₛ (suc n)
                                (Iso.fun (⊎Iso (invIso Iso-Fin⊎Fin-Fin+) idIso)
                                 (Iso.inv Iso-Fin⊎Fin-Fin+ x)
                                 , north)))))
    ∙ cong₂ _∙_ (cong merid {! -- Pushout→Bouquet (suc n) (pushoutCells (suc n)) (pushoutα> n) (snd PushoutCWskel .snd .snd .snd (suc n)) (Iso.fun (isCWPushoutIso n) (preboundary.αn+1 PushoutCWskel (suc n) (x , a)))!}) -- λ _ → Pushout→Bouquet (suc n) ? ? ? ?)
                {!(Iso.fun (isCWPushoutIso n) (preboundary.αn+1 PushoutCWskel (suc n) (x , a)))!}
    ∙ {!!} 

  altT : (n : ℕ) (x : Fin (preboundary.An+1 PushoutCWskel (suc n)))
    → fst (S₊∙ (suc (suc n))) → Susp (fst PushoutCWskel (suc (suc n)))
  altT n x north = {!!}
  altT n x south = {!!}
  altT n x (merid a i) = {!!}
  

  charac∂ : (n : ℕ) → projC ∘ preboundary.pre∂ PushoutCWskel n ∘ Iso.inv (SphereBouquetCellIso n _)
                      ≡ (((preboundary.pre∂ C n , sphereBouquetSuspIso∙) ∘∙ foldL∙)
                      ∨→ (bouquetSusp→ (prefunctoriality.bouquetFunct (suc n)
                               (cellMap→finCellMap (suc n) f) flast) , bouquetSusp→∙ n))
  charac∂ zero = {!!}
  charac∂ (suc n) =
    funExt λ { (inl (inl (inl x))) → refl
             ; (inl (inl (inr (x , y))))
               → {! (projC ∘
       preboundary.pre∂ PushoutCWskel (suc n) ∘
       Iso.inv (SphereBouquetCellIso (suc n) (suc (suc n))))
      (inl (inl (inr (x , y))))!} -- refl
             {-
             ; (inl (inl (inr (x , south)))) → refl
             ; (inl (inl (inr (x , merid a i)))) j
               → (cong (cong (projC ∘ preboundary.pre∂ PushoutCWskel (suc n)))
                       (λ j i → inr (mok x , merid a i))
                    ∙ {!invEq (snd PushoutCWskel .snd .snd .snd (suc (suc n))) (push ? i) -- preboundary.isoCofBouquetInv↑ PushoutCWskel (suc n) (inr (? , merid a i))!}) j i
                    -}
               {- (cong (cong (projC ∘ preboundary.pre∂ PushoutCWskel (suc n)))
                       (λ j i → inr ({!!} , merid a i))
                    ∙ {!!}) j i
                    -}
             ; (inl (inl (push a i))) → {!preboundary.isoCofBouquet PushoutCWskel (suc n) (inr ?)!}
              ; (inl (inr x)) → {!x!}
              ; (inl (push a i)) → {!!}
              ; (inr (inl x)) → refl
              ; (inr (inr (x , north))) → refl
              ; (inr (inr (x , south))) → refl
              ; (inr (inr (x , merid a i))) → {!!}
              ; (inr (push a i)) → _ preBTC
              ; (push a i) → {!!}}
     where
     mok : (x : Fin (card C (suc (suc n)))) → Fin (preboundary.An+1 PushoutCWskel (suc n))
     mok x = Iso.fun Iso-Fin⊎Fin-Fin+ (inl (Iso.fun Iso-Fin⊎Fin-Fin+ (inl x)))



-- open import Cubical.Data.Unit
-- UnitCWskel : CWskel ℓ-zero
-- fst UnitCWskel zero = ⊥
-- fst UnitCWskel (suc n) = Unit
-- fst (snd UnitCWskel) zero = 1
-- fst (snd UnitCWskel) (suc n) = 0
-- fst (snd (snd UnitCWskel)) zero ()
-- fst (snd (snd UnitCWskel)) (suc n) t = tt
-- fst (snd (snd (snd UnitCWskel))) ()
-- snd (snd (snd (snd UnitCWskel))) zero =
--   compEquiv (isoToEquiv Iso-Unit-Fin1)
--     (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _))
-- snd (snd (snd (snd UnitCWskel))) (suc n) =
--   isoToEquiv (PushoutEmptyFam (λ()) λ())

-- terminalCW : ∀ {ℓ} {C : CWskel ℓ} → cellMap C UnitCWskel
-- SequenceMap.map (terminalCW {C = C}) zero = fst (snd (snd (snd C)))
-- SequenceMap.map terminalCW (suc n) _ = tt
-- SequenceMap.comm terminalCW _ _ = refl

-- CofibCWskel : ∀ {ℓ ℓ'} {C : CWskel ℓ} {D : CWskel ℓ'} → cellMap C D → CWskel _
-- CofibCWskel f = PushoutCWskel terminalCW f

-- open import Cubical.CW.Properties
-- open import Cubical.Algebra.ChainComplex
-- open import Cubical.CW.ChainComplex
-- open import Cubical.CW.Homology
-- open import Cubical.Algebra.Group.Morphisms

-- cfcodCellMap : ∀ {ℓ ℓ'} {C : CWskel ℓ} {D : CWskel ℓ'} (f : cellMap C D)
--   → cellMap D (CofibCWskel f)
-- cfcodCellMap f = inrCellMap terminalCW f

-- ExcisionAxiom : ∀ {ℓ ℓ'} (C : CWskel ℓ) (D : CWskel ℓ') (f : cellMap C D) (n : ℕ)
--   → Type _
-- ExcisionAxiom C D f n =
--   (x : Hˢᵏᵉˡ D n .fst)
--   → isInKer (Hˢᵏᵉˡ→-pre D (CofibCWskel f) n
--                 (cellMap→finCellMap (suc (suc (suc n))) (cfcodCellMap f)))
--                 x
--   → isInIm (Hˢᵏᵉˡ→-pre C D n (cellMap→finCellMap (suc (suc (suc n))) f)) x

-- open import Cubical.HITs.SetQuotients as SQ
-- open import Cubical.Algebra.Group
-- open import Cubical.Algebra.Group.Subgroup
-- open import Cubical.Algebra.Group.QuotientGroup renaming (_/_ to _/G_)
-- open import Cubical.Relation.Binary.Base
-- open import Cubical.Algebra.ChainComplex
-- open import Cubical.Foundations.Powerset
-- open import Cubical.Algebra.AbGroup
-- open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
-- open import Cubical.CW.ChainComplex




-- module _ {ℓ : Level} (G' : Group ℓ) (H' : Subgroup G') (Hnormal : isNormal H') where

--   open BinaryRelation
--   open isSubgroup (snd H')
--   open GroupStr (snd G') renaming (_·_ to _·G_)
--   open GroupTheory G'

--   isSym~ : isSym ((G' ~ H') Hnormal)
--   isSym~ g h s = subst-∈ (fst H') (invDistr g (inv h)
--                ∙ cong₂ _·G_ (invInv h) refl) (inv-closed s)

--   isTrans~ : isTrans ((G' ~ H') Hnormal)
--   isTrans~ g1 g2 g3 g12 g23 =
--     subst-∈ (fst H')
--       (sym (·Assoc g1 (inv g2) (g2 ·G inv g3))
--      ∙ cong₂ _·G_ refl (·Assoc (inv g2) g2 (inv g3)
--                      ∙ cong₂ _·G_ (·InvL g2) refl
--                      ∙ ·IdL (inv g3)))
--       (op-closed g12 g23)

--   isEquivalenceRelation~ : isEquivRel (_~_ G' H' Hnormal)
--   isEquivRel.reflexive isEquivalenceRelation~ = isRefl~ G' H' Hnormal
--   isEquivRel.symmetric isEquivalenceRelation~ = isSym~
--   isEquivRel.transitive isEquivalenceRelation~ = isTrans~

-- PathIsoQuotientGroup : ∀ {ℓ} {G : Group ℓ} {H : NormalSubgroup G}
--   → {g1 g2 : fst G}
--   → Path (fst (G /G H)) [ g1 ] [ g2 ] → _~_ G (fst H) (snd H) g1 g2
-- PathIsoQuotientGroup {G = G} {H} x =
--   PT.rec (∈-isProp (fst H .fst) _) (λ x → x)
--     (Iso.fun (isEquivRel→TruncIso (isEquivalenceRelation~ G (fst H) (snd H)) _ _) x)

-- open import Cubical.HITs.SphereBouquet.Degree
-- open import Cubical.Data.Int renaming (_+_ to _+ℤ_)
-- open import Cubical.Algebra.AbGroup.Instances.Int


-- ExcisionStrict! : ∀ {ℓ ℓ'} (C : CWskel ℓ) (D : CWskel ℓ')
--   (f : cellMap (strictCWskel C) (strictCWskel D)) (n : ℕ)
--   → ExcisionAxiom (strictCWskel C) (strictCWskel D) f n
-- ExcisionStrict! C D' f n = SQ.elimProp {!!}
--   λ w p → PT.rec {!!}
--     (uncurry λ g p → {!p -- main (fst w) (snd w) g p!})
--     (PathIsoQuotientGroup p)
--   where
--   D = strictCWskel D'
--   open CWskel-fields
--   main : (w : ℤ[Fin card D (suc n) ] .fst)
--     → bouquetDegree (preboundary.pre∂ D n) .fst w ≡ (λ _ → 0)
--     → (g : ℤ[Fin card D (suc (suc n)) + card C (suc n) ] .fst)
--     → (p : bouquetDegree (preboundary.pre∂ (CofibCWskel f) (suc n)) .fst g ≡ λ _ → 0) -- {!?!}
--     → {!preboundary.pre∂ (CofibCWskel f) (suc n) -- bouquetDegree (preboundary.pre∂ (CofibCWskel f) (suc n))!} 
--   main = {!!}

-- Excision! : ∀ {ℓ ℓ'} (C : CWskel ℓ) (D : CWskel ℓ') (f : cellMap C D) (n : ℕ)
--   → ExcisionAxiom C D f n
-- Excision! = elimStrictCW (λ B → elimStrictCW λ C → {!!})


-- -- module _ {ℓ ℓ' ℓ'' : Level} {B' : CWskel ℓ} {C' : CWskel ℓ'} {D' : CWskel ℓ''}
-- --   (f : cellMap (strictCWskel B') (strictCWskel C'))
-- --   (g : cellMap (strictCWskel B') (strictCWskel D')) where

-- --   private
-- --     B = strictCWskel B'
-- --     C = strictCWskel C'
-- --     D = strictCWskel D'

-- --   open CWskel-fields
-- --   open SequenceMap renaming (map to ∣_∣)

-- --   pushoutA : ℕ → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') 
-- --   pushoutA zero = Lift {ℓ} {ℓ-max ℓ' ℓ''} (B .fst zero)
-- --   pushoutA (suc n) =
-- --     Pushout {A = fst B n} {B = fst C (suc n)} {C = fst D (suc n)}
-- --        (inl ∘ ∣ f ∣ n) (inl ∘ ∣ g ∣ n)

-- --   pushoutCells : ℕ → ℕ
-- --   pushoutCells zero = (card C zero) +ℕ (card D zero)
-- --   pushoutCells (suc n) = ((card C (suc n)) +ℕ (card D (suc n))) +ℕ (card B n)

-- --   pushoutMap₀ : (Fin (pushoutCells zero)) × (S⁻ 0) → pushoutA 0
-- --   pushoutMap₀ ()

-- --   pushoutMapₛ : (n : ℕ) → (((A C (suc n)) ⊎ (A D (suc n))) ⊎ (A B n)) × (Susp (S⁻ n)) → pushoutA (suc n)
-- --   pushoutMapₛ n (inl (inl c) , x) = inl (α C (suc n) (c ,  Iso.inv (IsoSphereSusp n) x))
-- --   pushoutMapₛ n (inl (inr d) , x) = inr (α D (suc n) (d , Iso.inv (IsoSphereSusp n) x))
-- --   pushoutMapₛ n (inr b , north) = inl (∣ f ∣ (suc n) (inr b))
-- --   pushoutMapₛ n (inr b , south) = inr (∣ g ∣ (suc n) (inr b))
-- --   pushoutMapₛ n (inr b , merid x i) =
-- --      ((λ j → inl ((cong (∣ f ∣ (suc n)) (λ j → push (b , x) (~ j))
-- --       ∙ sym (comm f n (α B n (b , x)))) j))
-- --     ∙∙ push (α B n (b , x))
-- --     ∙∙ λ j → inr ((cong (∣ g ∣ (suc n)) (λ j → push (b , x) (~ j))
-- --       ∙ sym (comm g n (α B n (b , x)))) (~ j))) i

-- --   pushoutMap' : (n : ℕ) → (Fin (pushoutCells (suc n))) × (Susp (S⁻ n)) → pushoutA (suc n)
-- --   pushoutMap' n (a , x) = pushoutMapₛ n (finSplit3 (card C (suc n)) (card D (suc n)) (card B n) a , x)

-- --   pushoutα> : (n : ℕ) → Fin (card C (suc n) + card D (suc n) + card B n) × S₊ n
-- --                        → pushoutA (suc n)
-- --   pushoutα> n (x , y) =
-- --     pushoutMapₛ n ((finSplit3 (card C (suc n)) (card D (suc n)) (card B n) x)
-- --                  , Iso.fun (IsoSphereSusp n) y)

-- --   Iso-Pushoutα-PushoutPushoutMapₛ : (n : ℕ)
-- --     → Iso (Pushout (pushoutMapₛ n) fst)
-- --            (Pushout (pushoutα> n) fst)
-- --   Iso-Pushoutα-PushoutPushoutMapₛ n = pushoutIso _ _ _ _
-- --     (Σ-cong-equiv (invEquiv (finSplit3≃ _ _ _))
-- --       λ _ → isoToEquiv (invIso (IsoSphereSusp n)))
-- --     (idEquiv _)
-- --     (invEquiv (finSplit3≃ _ _ _))
-- --     (funExt λ x → cong (pushoutMapₛ n) (ΣPathP
-- --       (sym (secEq (finSplit3≃ _ _ _) (fst x))
-- --       , sym (Iso.rightInv (IsoSphereSusp n) (snd x)))))
-- --     refl

-- --   pushoutMap : (n : ℕ) → (Fin (pushoutCells n)) × (S⁻ n) → pushoutA n
-- --   pushoutMap zero = pushoutMap₀
-- --   pushoutMap (suc n) = pushoutα> n

-- --   module _ (n : ℕ) where
-- --     open 3x3-span
-- --     span1 : 3x3-span
-- --     A00 span1 = Fin (card B n)
-- --     A02 span1 = ⊥
-- --     A04 span1 = Fin (card C (suc n)) ⊎ Fin (card D (suc n))
-- --     A20 span1 = Fin (card B n) × Susp (S⁻ n)
-- --     A22 span1 = ⊥
-- --     A24 span1 = (Fin (card C (suc n)) ⊎ Fin (card D (suc n))) × Susp (S⁻ n)
-- --     A40 span1 = pushoutA (suc n)
-- --     A42 span1  = (Fin (card C (suc n)) ⊎ Fin (card D (suc n))) × Susp (S⁻ n)
-- --     A44 span1 = (Fin (card C (suc n)) ⊎ Fin (card D (suc n))) × Susp (S⁻ n)
-- --     f10 span1 = fst
-- --     f12 span1 = λ()
-- --     f14 span1 = fst
-- --     f30 span1 = λ xs → pushoutMapₛ n ((inr (fst xs)) , (snd xs))
-- --     f32 span1 = λ()
-- --     f34 span1 = idfun _
-- --     f01 span1 = λ()
-- --     f21 span1 = λ()
-- --     f41 span1 = λ xs → pushoutMapₛ n ((inl (fst xs)) , (snd xs))
-- --     f03 span1 = λ()
-- --     f23 span1 = λ()
-- --     f43 span1 = idfun _
-- --     H11 span1 = λ()
-- --     H13 span1 = λ()
-- --     H31 span1 = λ()
-- --     H33 span1 = λ()
  
-- --     Iso1 : Iso (Pushout (pushoutMapₛ n) fst)
-- --                (A○□ span1)
-- --     Iso1 =
-- --       compIso (pushoutIso _ _ _ _ (isoToEquiv iso1)
-- --                 (isoToEquiv iso2)
-- --                 (isoToEquiv iso3)
-- --                 (funExt (λ { (inl x , s) → push (x , s)
-- --                            ; (inr x , s) → refl}))
-- --                 (funExt λ { (inl x , s) → refl ; (inr x , s) → refl}))
-- --       (equivToIso (symPushout _ _))
-- --       where
-- --       iso3 : Iso ((A C (suc n) ⊎ A D (suc n)) ⊎ A B n) (A0□ span1)
-- --       Iso.fun iso3 (inl x) = inr x
-- --       Iso.fun iso3 (inr x) = inl x
-- --       Iso.inv iso3 (inl x) = inr x
-- --       Iso.inv iso3 (inr x) = inl x
-- --       Iso.rightInv iso3 (inl x) = refl
-- --       Iso.rightInv iso3 (inr x) = refl
-- --       Iso.leftInv iso3 (inl x) = refl
-- --       Iso.leftInv iso3 (inr x) = refl

-- --       iso2 : Iso (pushoutA (suc n)) (A4□ span1)
-- --       iso2 = invIso (compIso
-- --         (equivToIso (symPushout _ _))
-- --          (PushoutAlongEquiv (idEquiv _) _))

-- --       iso1 : Iso (((A C (suc n) ⊎ A D (suc n)) ⊎ A B n) × Susp (S⁻ n))
-- --                  (A2□ span1)
-- --       Iso.fun iso1 (inl x , s) = inr (x , s)
-- --       Iso.fun iso1 (inr x , s) = inl (x , s)
-- --       Iso.inv iso1 (inl (x , s)) = (inr x) , s
-- --       Iso.inv iso1 (inr (x , s)) = (inl x) , s
-- --       Iso.rightInv iso1 (inl x) = refl
-- --       Iso.rightInv iso1 (inr x) = refl
-- --       Iso.leftInv iso1 (inl x , s) = refl
-- --       Iso.leftInv iso1 (inr x , s) = refl

-- --     T2 = (Pushout {A = (Fin (card C (suc n)) ⊎ Fin (card D (suc n)))
-- --                            × Susp (S⁻ n)}
-- --                         {B = A□0 span1}
-- --                 (λ xs → inr (pushoutMapₛ n ((inl (fst xs)) , (snd xs))))
-- --                 fst)

-- --     Iso2 : Iso (A□○ span1) T2
-- --     Iso2 =
-- --       pushoutIso _ _ _ _
-- --       (compEquiv (symPushout _ _)
-- --         (isoToEquiv (invIso (PushoutEmptyFam (λ()) λ()))))
-- --       (idEquiv _)
-- --       (compEquiv (symPushout _ _)
-- --         (isoToEquiv (PushoutAlongEquiv (idEquiv _) _)))
-- --       (funExt λ { (inr x) → refl})
-- --       (funExt λ { (inr x) → refl})

-- --     firstRetwriteIso : Iso (Pushout (pushoutMapₛ n) fst) T2
-- --     firstRetwriteIso = compIso Iso1 (compIso (invIso (3x3-Iso span1)) Iso2)

-- --   module _ (n : ℕ) where
-- --     open 3x3-span
-- --     span2 : 3x3-span
-- --     A00 span2 = Fin (card B n)
-- --     A02 span2 = Fin (card B n)
-- --     A04 span2 = Fin (card B n)
-- --     A20 span2 = Fin (card B n)
-- --     A22 span2 = Fin (card B n) × S⁻ n
-- --     A24 span2 = Fin (card B n)
-- --     A40 span2 = fst C (suc n)
-- --     A42 span2 = fst B n
-- --     A44 span2 = fst D (suc n)
-- --     f10 span2 = idfun _
-- --     f12 span2 = fst
-- --     f14 span2 = idfun _
-- --     f30 span2 = λ x → ∣ f ∣ (suc n) (inr x)
-- --     f32 span2 = α B n
-- --     f34 span2 = λ x → ∣ g ∣ (suc n) (inr x)
-- --     f01 span2 = idfun _
-- --     f21 span2 = fst
-- --     f41 span2 = λ x → inl (∣ f ∣ n x)
-- --     f03 span2 = idfun _
-- --     f23 span2 = fst
-- --     f43 span2 = λ x → inl (∣ g ∣ n x)
-- --     H11 span2 = λ _ → refl
-- --     H13 span2 = λ _ → refl
-- --     H31 span2 = λ x → sym (sym (cong (∣ f ∣ (suc n)) (push x)) ∙ sym (comm f n (α B n x)))
-- --     H33 span2 = λ x → sym (sym (cong (∣ g ∣ (suc n)) (push x)) ∙ sym (comm g n (α B n x)))

-- --     Iso3 : Iso (A○□ span2) (A□0 (span1 n))
-- --     Iso3 =
-- --       (pushoutIso _ _ _ _
-- --         (isoToEquiv iso1)
-- --         (isoToEquiv (PushoutAlongEquiv (idEquiv _) _))
-- --         (idEquiv _)
-- --         (funExt (λ { (inl x) → refl
-- --                    ; (inr x) → refl
-- --                    ; (push a i) j → PushoutAlongEquiv→ (idEquiv (Fin (card B n))) (idfun _)
-- --                                       (rUnit (push (fst a)) (~ j) i)}))
-- --         (funExt λ { (inl x) → refl
-- --                    ; (inr x) → refl
-- --                    ; (push a i) → refl}))
-- --       where

-- --       iso1 : Iso (A2□ span2) (Fin (card B n) × Susp (S⁻ n))
-- --       Iso.fun iso1 (inl x) = x , north
-- --       Iso.fun iso1 (inr x) = x , south
-- --       Iso.fun iso1 (push a i) = fst a , (merid (snd a) i)
-- --       Iso.inv iso1 (x , north) = inl x
-- --       Iso.inv iso1 (x , south) = inr x
-- --       Iso.inv iso1 (x , merid a i) = push (x , a) i
-- --       Iso.rightInv iso1 (x , north) = refl
-- --       Iso.rightInv iso1 (x , south) = refl
-- --       Iso.rightInv iso1 (x , merid a i) = refl
-- --       Iso.leftInv iso1 (inl x) = refl
-- --       Iso.leftInv iso1 (inr x) = refl
-- --       Iso.leftInv iso1 (push a i) = refl

-- --     Iso4 : Iso (A□○ span2)
-- --                (Pushout {A = fst B (suc n)} (∣ f ∣ (suc n) ) (∣ g ∣ (suc n)))
-- --     Iso4 = pushoutIso _ _ _ _
-- --       (compEquiv (symPushout _ _) (invEquiv (e B n)))
-- --       (isoToEquiv (PushoutAlongEquiv (idEquiv _) _))
-- --       (isoToEquiv (PushoutAlongEquiv (idEquiv _) _))
-- --       (funExt (λ { (inl x) → refl
-- --                  ; (inr x) → comm f n x
-- --                  ; (push a i) j → lem1 a j i}))
-- --       (funExt λ { (inl x) → refl
-- --                  ; (inr x) → comm g n x
-- --                  ; (push a i) j → lem2 a j i})
-- --       where
-- --       module _ (a : Fin (card B n) × S⁻ n) where
-- --         lem1 : Square (cong ((PushoutAlongEquiv→ (idEquiv (Fin (card B n)))
-- --                             (λ x → ∣ f ∣ (suc n) (inr x))))
-- --                          (cong (f□1 span2) (push a)))
-- --                     (cong (∣ f ∣ (suc n)) (sym (push a)))
-- --                     refl
-- --                     (comm f n (α B n a))
-- --         lem1 =
-- --           (cong-∙ (PushoutAlongEquiv→ (idEquiv (Fin (card B n)))
-- --                    (λ x → ∣ f ∣ (suc n) (inr x)))
-- --                   (push (fst a))
-- --                   _
-- --                 ∙ sym (lUnit _))
-- --           ◁ symP (compPath-filler (cong (∣ f ∣ (suc n)) (sym (push a)))
-- --                              (sym (comm f n (α B n a))))

-- --         lem2 : Square (cong ((PushoutAlongEquiv→ (idEquiv (Fin (card B n)))
-- --                             (λ x → ∣ g ∣ (suc n) (inr x))))
-- --                          (cong (f□3 span2) (push a)))
-- --                     (cong (∣ g ∣ (suc n)) (sym (push a)))
-- --                     refl
-- --                     (comm g n (α B n a))
-- --         lem2 =
-- --           (cong-∙ (PushoutAlongEquiv→ (idEquiv (Fin (card B n)))
-- --                    (λ x → ∣ g ∣ (suc n) (inr x)))
-- --                   (push (fst a))
-- --                   _
-- --                 ∙ sym (lUnit _))
-- --           ◁ symP (compPath-filler (cong (∣ g ∣ (suc n)) (sym (push a)))
-- --                              (sym (comm g n (α B n a))))

-- --   module _ (n : ℕ) where
-- --     open 3x3-span
-- --     span3 : 3x3-span
-- --     A00 span3 = Fin (card C (suc n))
-- --     A02 span3 = ⊥
-- --     A04 span3 = Fin (card D (suc n))
-- --     A20 span3 = Fin (card C (suc n)) × Susp (S⁻ n)
-- --     A22 span3 = ⊥
-- --     A24 span3 = Fin (card D (suc n)) × Susp (S⁻ n)
-- --     A40 span3 = fst C (suc n)
-- --     A42 span3 = fst B (suc n)
-- --     A44 span3 = fst D (suc n)
-- --     f10 span3 = fst
-- --     f12 span3 = λ()
-- --     f14 span3 = fst
-- --     f30 span3 = λ x → α C (suc n) (fst x , Iso.inv (IsoSphereSusp n) (snd x))
-- --     f32 span3 = λ()
-- --     f34 span3 = λ x → α D (suc n) (fst x , Iso.inv (IsoSphereSusp n) (snd x))
-- --     f01 span3 = λ()
-- --     f21 span3 = λ()
-- --     f41 span3 = ∣ f ∣ (suc n)
-- --     f03 span3 = λ()
-- --     f23 span3 = λ()
-- --     f43 span3 = ∣ g ∣ (suc n)
-- --     H11 span3 = λ()
-- --     H13 span3 = λ()
-- --     H31 span3 = λ()
-- --     H33 span3 = λ()

-- --     Iso5 : Iso (A□○ span3) (pushoutA (suc (suc n)))
-- --     Iso5 = 
-- --       (pushoutIso _ _ _ _
-- --       (compEquiv (symPushout _ _)
-- --         (isoToEquiv (invIso (PushoutEmptyFam (λ()) λ()))))
-- --         (compEquiv (compEquiv (symPushout _ _)
-- --           (pushoutEquiv _ _ _ _
-- --             (Σ-cong-equiv-snd
-- --               (λ _ → invEquiv (isoToEquiv (IsoSphereSusp n))))
-- --                 (idEquiv _) (idEquiv _)
-- --                   (λ i x → α C (suc n) (fst x , Iso.inv (IsoSphereSusp n) (snd x)))
-- --                   λ _ x → fst x))
-- --           (invEquiv (e C (suc n))))
-- --         (compEquiv (compEquiv (symPushout _ _)
-- --           (pushoutEquiv _ _ _ _
-- --             (Σ-cong-equiv-snd
-- --               (λ _ → invEquiv (isoToEquiv (IsoSphereSusp n))))
-- --                 (idEquiv _) (idEquiv _)
-- --                   (λ i x → α D (suc n) (fst x , Iso.inv (IsoSphereSusp n) (snd x)))
-- --                   λ _ x → fst x))
-- --           (invEquiv (e D (suc n))))
-- --         (funExt (λ { (inr x) → refl}))
-- --         (funExt (λ { (inr x) → refl})))

-- --     T3 : Type _
-- --     T3 = Pushout {A = (Fin (card C (suc n)) ⊎ Fin (card D (suc n)))
-- --                             × Susp (S⁻ n)}
-- --                         {B = Pushout (∣ f ∣ (suc n)) (∣ g ∣ (suc n))}
-- --                 (uncurry (⊎.rec
-- --                   (λ x y → inl (α C (suc n) (x , Iso.inv (IsoSphereSusp n) y)))
-- --                   (λ x y → inr (α D (suc n) (x , Iso.inv (IsoSphereSusp n) y)))))
-- --                 fst

-- --     T4 : Type _
-- --     T4 = Pushout {A = (Fin (card C (suc n)) ⊎ Fin (card D (suc n)))
-- --                             × Susp (S⁻ n)}
-- --                         {B = Pushout (∣ f ∣ (suc n)) (∣ g ∣ (suc n))}
-- --                 (uncurry (⊎.rec
-- --                   (λ x y → inl (α C (suc n) (x , Iso.inv (IsoSphereSusp n) y)))
-- --                   (λ x y → inr (α D (suc n) (x , Iso.inv (IsoSphereSusp n) y)))))
-- --                 fst

-- --     Iso6 : Iso (A○□ span3) T3
-- --     Iso6 = compIso (equivToIso (symPushout _ _))
-- --       (pushoutIso _ _ _ _
-- --         (compEquiv (isoToEquiv (invIso Pushout-⊎-Iso))
-- --           (invEquiv (isoToEquiv Σ⊎Iso)))
-- --         (idEquiv _)
-- --           (isoToEquiv (invIso Pushout-⊎-Iso))
-- --         (funExt (λ { (inl x) → refl ; (inr x) → refl}))
-- --         (funExt λ { (inl x) → refl ; (inr x) → refl}))


-- --   open 3x3-span
-- --   T3≅T2 : (n : ℕ) → Iso (T3 n) (T2 n)
-- --   T3≅T2 n = pushoutIso _ _ _ _
-- --     (idEquiv _)
-- --     (isoToEquiv
-- --       (compIso
-- --         (compIso (invIso
-- --           (Iso4 n)) (3x3-Iso (span2 n)))
-- --         (Iso3 n)))
-- --     (idEquiv _)
-- --     (funExt (λ { (inl x , y) → refl
-- --                ; (inr x , y) → refl}))
-- --     λ _ x → fst x

-- --   isCWPushoutIsoPre : (n : ℕ)
-- --     → Iso (pushoutA (suc (suc n)))
-- --            (Pushout (pushoutMapₛ n) fst)
-- --   isCWPushoutIsoPre n =
-- --     compIso (invIso (Iso5 n))
-- --      (compIso (3x3-Iso (span3 n))
-- --        (compIso (Iso6 n)
-- --         (compIso
-- --          (compIso
-- --           (compIso (T3≅T2 n)
-- --             (invIso (Iso2 n)))
-- --               (3x3-Iso (span1 n)))
-- --                (invIso (Iso1 n)))))

-- --   isCWPushoutIso : (n : ℕ)
-- --     → Iso (pushoutA (suc (suc n)))
-- --            (Pushout (pushoutα> n) fst)
-- --   isCWPushoutIso n =
-- --     compIso (isCWPushoutIsoPre n)
-- --       (Iso-Pushoutα-PushoutPushoutMapₛ n)

-- --   open import Cubical.CW.Properties
-- --   isCWPushoutIso₀ : Iso (pushoutA (suc zero)) (Pushout pushoutMap₀ fst)
-- --   isCWPushoutIso₀ =
-- --     compIso
-- --       (compIso
-- --         (compIso
-- --           (compIso
-- --           (invIso (pushoutIso _ _ _ _
-- --             (propBiimpl→Equiv isProp⊥
-- --               (λ x → ⊥.rec (fst (snd (snd (snd B))) x))
-- --               (λ()) (fst (snd (snd (snd B)))))
-- --             (invEquiv (CW₁-discrete C))
-- --             (invEquiv (CW₁-discrete D))
-- --             (funExt λ ()) (funExt λ())))
-- --            (invIso Pushout-⊎-Iso))
-- --           Iso-Fin⊎Fin-Fin+)
-- --         (PushoutEmptyFam (λ())
-- --           λ {(lift t) → fst (snd (snd (snd B))) t}))
-- --       (equivToIso (symPushout _ _))

-- --   PushoutCWskelStrict : CWskel _
-- --   fst PushoutCWskelStrict = pushoutA
-- --   fst (snd PushoutCWskelStrict) = pushoutCells
-- --   fst (snd (snd PushoutCWskelStrict)) = pushoutMap
-- --   fst (snd (snd (snd PushoutCWskelStrict))) (lift t) = fst (snd (snd (snd B))) t
-- --   snd (snd (snd (snd PushoutCWskelStrict))) zero = isoToEquiv isCWPushoutIso₀
-- --   snd (snd (snd (snd PushoutCWskelStrict))) (suc n) = isoToEquiv (isCWPushoutIso n)

-- --   inlCellMapStrict : cellMap C PushoutCWskelStrict
-- --   ∣ inlCellMapStrict ∣ zero x = ⊥.rec (fst (snd (snd (snd C'))) x)
-- --   ∣ inlCellMapStrict ∣ (suc n) x = inl x
-- --   comm inlCellMapStrict zero x = ⊥.rec (fst (snd (snd (snd C'))) x)
-- --   comm inlCellMapStrict (suc n) x = refl

-- --   inrCellMapStrict : cellMap D PushoutCWskelStrict
-- --   ∣ inrCellMapStrict ∣ zero x = ⊥.rec (fst (snd (snd (snd D'))) x)
-- --   ∣ inrCellMapStrict ∣ (suc n) x = inr x
-- --   comm inrCellMapStrict zero x = ⊥.rec (fst (snd (snd (snd D'))) x)
-- --   comm inrCellMapStrict (suc n) x = refl

-- -- open import Cubical.Algebra.ChainComplex
-- -- open import Cubical.CW.ChainComplex
-- -- open import Cubical.CW.Homology
-- -- open import Cubical.Algebra.Group.Morphisms

-- -- PushoutCWskelPre : ∀ {ℓ} {ℓ'} {ℓ''} (B : CWskel ℓ) (C : CWskel ℓ') (D : CWskel ℓ'')
-- --   → cellMap B C → cellMap B D → CWskel _
-- -- PushoutCWskelPre = elim3StrictCW λ B C D → PushoutCWskelStrict

-- -- PushoutCWskel : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
-- --   → cellMap B C → cellMap B D → CWskel _
-- -- PushoutCWskel {B = B} {C = C} {D = D} f g = PushoutCWskelPre _ _ _ f g

-- -- PushoutCWskelβ : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
-- --   (f : cellMap (strictCWskel B) (strictCWskel C))
-- --   (g : cellMap (strictCWskel B) (strictCWskel D))
-- --   → PushoutCWskel f g ≡ PushoutCWskelStrict f g
-- -- PushoutCWskelβ {B = B} {C = C} {D = D} f g i =
-- --   elim3StrictCWβ {P = λ B C D → cellMap B C → cellMap B D → CWskel _}
-- --     (λ B C D → PushoutCWskelStrict {B' = B} {C' = C} {D' = D}) B C D i f g

-- -- UnitCWFam : ℕ → Type ℓ-zero
-- -- UnitCWFam zero = ⊥
-- -- UnitCWFam (suc n) = Unit

-- -- -- UnitCWCells : ℕ → ℕ
-- -- -- UnitCWCells zero = 1
-- -- -- UnitCWCells (suc n) = 0

-- -- -- UnitCWPushoutEquiv : ∀ {ℓ} → Unit ≃ Pushout {A = Fin 0 × {!!}} {!!} {!!}
-- -- -- UnitCWPushoutEquiv = {!!}

-- -- open import Cubical.Data.Unit
-- -- UnitCWskel : CWskel ℓ-zero
-- -- fst UnitCWskel zero = ⊥
-- -- fst UnitCWskel (suc n) = Unit
-- -- fst (snd UnitCWskel) zero = 1
-- -- fst (snd UnitCWskel) (suc n) = 0
-- -- fst (snd (snd UnitCWskel)) zero ()
-- -- fst (snd (snd UnitCWskel)) (suc n) t = tt
-- -- fst (snd (snd (snd UnitCWskel))) ()
-- -- snd (snd (snd (snd UnitCWskel))) zero =
-- --   compEquiv (isoToEquiv Iso-Unit-Fin1)
-- --     (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _))
-- -- snd (snd (snd (snd UnitCWskel))) (suc n) =
-- --   isoToEquiv (PushoutEmptyFam (λ()) λ())

-- -- terminalCW : ∀ {ℓ} {C : CWskel ℓ} → cellMap C UnitCWskel
-- -- SequenceMap.map (terminalCW {C = C}) zero = fst (snd (snd (snd C)))
-- -- SequenceMap.map terminalCW (suc n) _ = tt
-- -- SequenceMap.comm terminalCW _ _ = refl

-- -- terminalCWStrict∙ : (n : ℕ) → fst (strictCWskel UnitCWskel) (suc n)
-- -- terminalCWStrict∙ zero = inr fzero
-- -- terminalCWStrict∙ (suc n) = inl (terminalCWStrict∙ n)

-- -- terminalCWStrict : ∀ {ℓ} (C : CWskel ℓ) → cellMap C (strictCWskel UnitCWskel)
-- -- SequenceMap.map (terminalCWStrict C) zero x = ⊥.rec (fst (snd (snd (snd C))) x)
-- -- SequenceMap.map (terminalCWStrict C) (suc n) x = terminalCWStrict∙ n
-- -- SequenceMap.comm (terminalCWStrict C) zero x = ⊥.rec (fst (snd (snd (snd C))) x)
-- -- SequenceMap.comm (terminalCWStrict C) (suc n) x = refl

-- -- cofibCWSkel : ∀ {ℓ ℓ'} {B : CWskel ℓ} {C : CWskel ℓ'} (f : cellMap B C)
-- --   → CWskel (ℓ-max ℓ ℓ')
-- -- cofibCWSkel f = PushoutCWskel terminalCW f

-- -- cofibCWSkelβ : ∀ {ℓ ℓ'} {B : CWskel ℓ} {C : CWskel ℓ'}
-- --   (f : cellMap (strictCWskel B) (strictCWskel C))
-- --   → cofibCWSkel f ≡ PushoutCWskelStrict (terminalCWStrict _) f
-- -- cofibCWSkelβ f = {!f -- -- cong₂ PushoutCWskel ? ?!} ∙ PushoutCWskelβ (terminalCWStrict _) f
-- --   where
-- --   h : {!!}
-- --   h = {!!}

-- -- cfcodCellMap : ∀ {ℓ ℓ'} {B : CWskel ℓ} {C : CWskel ℓ'} (f : cellMap B C)
-- --   → cellMap {!!} {!!}
-- -- cfcodCellMap = {!!}



-- -- --   C→PushoutA : (n : ℕ) → fst C (suc n) → pushoutA n
-- -- --   C→PushoutA zero (inl x) = {!!}
-- -- --   C→PushoutA zero (inr x) = {!!}
-- -- --   C→PushoutA (suc n) c = {!!}

-- -- --   open import Cubical.Data.Nat.Order.Inductive
-- -- --   open import Cubical.Data.Empty as ⊥
  
-- -- --   map→ : (n : ℕ)
-- -- --     → pushoutA (suc n)
-- -- --     → Pushout (pushoutMap n) (λ r → fst r)
-- -- --   map→ zero (inl (inl x)) = ⊥.rec (snd (snd C') .snd .fst x)
-- -- --   map→ zero (inl (inr x)) = inr {!x!}
-- -- --   map→ (suc n) (inl (inl x)) = inl (inl x)
-- -- --   map→ (suc n) (inl (inr x)) = inr (fst x , {!x!}) --  (inl {!x!})
-- -- --   map→ (suc n) (inl (push a i)) = ({!!} ∙ push ({!fst a!} , (snd a))) i
-- -- --   map→ zero (inr (inl x)) = ⊥.rec (snd (snd D) .snd .fst x)
-- -- --   map→ (suc n) (inr (inl x)) = {!!}
-- -- --   map→ n (inr (inr x)) = inl {!!}
-- -- --   map→ n (inr (push a i)) = {!Iso-Fin⊎Fin-Fin+!}
-- -- --   map→ n (push a i) = {!a!}

-- -- --   pushoutMapInv : (n : ℕ) → (Fin (pushoutCells n)) × (S⁻ n) → pushoutA n
-- -- --   pushoutMapInv = {!!}

-- -- --   PushoutComplex : CWskel _
-- -- --   fst PushoutComplex = pushoutA
-- -- --   fst (snd PushoutComplex) = pushoutCells
-- -- --   fst (snd (snd PushoutComplex)) = pushoutMap
-- -- --   fst (snd (snd (snd PushoutComplex))) = fst (snd (snd (snd B)))
-- -- --   snd (snd (snd (snd PushoutComplex))) n = isoToEquiv (iso (map→ n){!!} {!!} {!!})

-- -- -- --   2+ : ℕ → ℕ
-- -- -- --   2+ n = suc (suc n)

-- -- -- --   -- α' : (X : CWskel ℓ) → (n : ℕ) →

-- -- -- --   strictA : CWskel ℓ → ℕ → Type ℓ
-- -- -- --   strictA X zero = X .fst zero
-- -- -- --   strictA X (suc n) = Pushout (α X n) fst

-- -- -- --   strict²A : CWskel ℓ → ℕ → Type ℓ
-- -- -- --   strict²A X zero = X .fst zero
-- -- -- --   strict²A X (suc zero) = strictA X 1
-- -- -- --   strict²A X (suc (suc n)) = Pushout (λ ax → e X n .fst (α X (suc n) (fst ax , Iso.inv (IsoSphereSusp n) (snd ax)))) fst

-- -- -- --   Iso-strictA-strict²A : (C : CWskel ℓ) (n : ℕ) → Iso (strictA C n) (strict²A C n) 
-- -- -- --   Iso-strictA-strict²A C zero = idIso
-- -- -- --   Iso-strictA-strict²A C (suc zero) = idIso
-- -- -- --   Iso-strictA-strict²A C (suc (suc n)) =
-- -- -- --     pushoutIso _ _ _ _ (Σ-cong-equiv-snd (λ _ → isoToEquiv (IsoSphereSusp n))) (e C n)
-- -- -- --       (idEquiv _)
-- -- -- --       (λ i x → fst (e C n) (α C (suc n) (fst x , Iso.leftInv (IsoSphereSusp n) (snd x) (~ i))))
-- -- -- --       refl

-- -- -- --   strictMap : {X Y : CWskel ℓ} (f : cellMap X Y) → (n : ℕ) → strictA X n → strictA Y n
-- -- -- --   strictMap {X} {Y} f zero = ∣ f ∣ zero
-- -- -- --   strictMap {X} {Y} f (suc n) (inl x) = inl (∣ f ∣ n x)
-- -- -- --   strictMap {X} {Y} f (suc n) (inr x) = e Y n .fst (∣ f ∣ (suc n) (invEq (e X n) (inr x)))
-- -- -- --   strictMap {X} {Y} f (suc n) (push a i) =
-- -- -- --     ((λ i → secEq (e Y n) (inl (∣ f ∣ n (α X n a))) (~ i))
-- -- -- --     ∙∙ (λ i → e Y n .fst (f .comm n (α X n a) i))
-- -- -- --     ∙∙ (λ i → e Y n .fst (∣ f ∣ (suc n) (invEq (e X n) (push a i))))) i

-- -- -- --   strictPushout : (n : ℕ) → Type ℓ
-- -- -- --   strictPushout n = (Pushout {A = strictA B (suc n)} {B = strict²A C (2+ n)} {C = strict²A D (2+ n)}
-- -- -- --                              (inl ∘ strictMap {B} {C} f (suc n)) (inl ∘ strictMap {B} {D} g (suc n)))

-- -- -- --   pushoutA : ℕ → Type ℓ
-- -- -- --   pushoutA zero = B .fst zero
-- -- -- --   pushoutA (suc n) = Pushout {A = B .fst n} {B = strictA C (suc n)} {C = strictA D (suc n)} (inl ∘ ∣ f ∣ n) (inl ∘ ∣ g ∣ n)

-- -- -- --   pushoutCells : ℕ → ℕ
-- -- -- --   pushoutCells zero = (card C zero) +ℕ (card D zero)
-- -- -- --   pushoutCells (suc n) = (card C (suc n)) +ℕ (card B n) +ℕ (card D (suc n))

-- -- -- --   pushoutMap₀ : (Fin (pushoutCells zero)) × (S⁻ 0) → pushoutA 0
-- -- -- --   pushoutMap₀ ()

-- -- -- --   pushoutMapₛ : (n : ℕ) → (((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n))) × (Susp (S⁻ n)) → pushoutA (suc n)
-- -- -- --   pushoutMapₛ n (inl (inl c) , x) = inl (e C n .fst (α C (suc n) (c ,  Iso.inv (IsoSphereSusp n) x)))
-- -- -- --   pushoutMapₛ n (inl (inr b) , north) = inl (strictMap {B} {C} f (suc n) (inr b))
-- -- -- --   pushoutMapₛ n (inl (inr b) , south) = inr (strictMap {B} {D} g (suc n) (inr b))
-- -- -- --   pushoutMapₛ n (inl (inr b) , merid x i) = --pushoutIsoₛ-filler0 n b x i1 i
-- -- -- --     ((λ i → inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i))))
-- -- -- --     ∙∙ (push (α B n (b , x)))
-- -- -- --     ∙∙ (λ i → inr (strictMap {B} {D} g (suc n) (push (b , x) i)))) i
-- -- -- --   pushoutMapₛ n (inr d , x) = inr (e D n .fst (α D (suc n) (d ,  Iso.inv (IsoSphereSusp n) x )))

-- -- -- --   pushoutMap : (n : ℕ) → (Fin (pushoutCells n)) × (S⁻ n) → pushoutA n
-- -- -- --   pushoutMap zero = pushoutMap₀
-- -- -- --   pushoutMap (suc n) (a , x) = pushoutMapₛ n (finSplit3 (card C (suc n)) (card B n) (card D (suc n)) a
-- -- -- --                                                    , Iso.fun (IsoSphereSusp n) x)

-- -- -- --   pushoutIsoₛ-filler0 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → pushoutA (suc n)
-- -- -- --   pushoutIsoₛ-filler0 n b x i j = (doubleCompPath-filler (λ i → inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i))))
-- -- -- --                                                          (push (α B n (b , x)))
-- -- -- --                                                          (λ i → inr (strictMap {B} {D} g (suc n) (push (b , x) i))) i j)

-- -- -- --   pushoutIsoₛ-filler1 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → I → (Pushout (pushoutMapₛ n) fst)
-- -- -- --   pushoutIsoₛ-filler1 n b x i j k =
-- -- -- --     hfill (λ k → λ { (i = i0) → invSides-hfill2 (push (inl (inr b) , north))
-- -- -- --                                                 (λ i → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i))))) (~ j) (~ k) i1
-- -- -- --                    ; (i = i1) → invSides-hfill2 (push (inl (inr b) , south))
-- -- -- --                                                 (λ i → inl (inr (strictMap {B} {D} g (suc n) (push (b , x) (~ i))))) (~ j) (~ k) i1
-- -- -- --                    ; (j = i0) → inl (pushoutIsoₛ-filler0 n b x (~ k) i)
-- -- -- --                    ; (j = i1) → doubleCompPath-filler (push (inl (inr b) , north))
-- -- -- --                                                       (λ _ → inr (inl (inr b)))
-- -- -- --                                                       (λ i → push (inl (inr b) , south) (~ i)) k i })
-- -- -- --           (inS (push (inl (inr b) , merid x i) j)) k

-- -- -- --   pushoutIsoₛ-inv↪ : (n : ℕ) → pushoutA (suc n) → strictPushout n
-- -- -- --   pushoutIsoₛ-inv↪ n (inl c) = inl (inl c)
-- -- -- --   pushoutIsoₛ-inv↪ n (inr d) = inr (inl d)
-- -- -- --   pushoutIsoₛ-inv↪ n (push b i) = push (inl b) i

-- -- -- --   pushoutIsoₛ-filler2 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → I → strictPushout n
-- -- -- --   pushoutIsoₛ-filler2 n b x i j k =
-- -- -- --     hfill (λ k → λ { (i = i0) → pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x k j)
-- -- -- --                    ; (i = i1) → push (inr b) ((~ k) ∧ j)
-- -- -- --                    ; (j = i0) → invSides-hfill1 (λ i → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i)))))
-- -- -- --                                                 (λ _ → push (inr b) i0) i (~ k) i1
-- -- -- --                    ; (j = i1) → invSides-hfill1 (λ i → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) (~ i)))))
-- -- -- --                                                 (λ i → push (inr b) (~ i)) i (~ k) i1 })
-- -- -- --           (inS (push (push (b , x) i) j)) k

-- -- -- --   pushoutIsoₛ-filler3 : (n : ℕ) → (b : A B n) → I → I → I → Pushout (pushoutMapₛ n) fst
-- -- -- --   pushoutIsoₛ-filler3 n b j k l =
-- -- -- --     hfill (λ l → λ { (j = i0) → push (inl (inr b) , south) i0
-- -- -- --                    ; (j = i1) → doubleCompPath-filler (push (inl (inr b) , north))
-- -- -- --                                                       (λ _ → inr (inl (inr b)))
-- -- -- --                                                       (λ i → push (inl (inr b) , south) (~ i)) (~ k) (~ l)
-- -- -- --                    ; (k = i0) → (push (inl (inr b) , north) ∙∙ (λ _ → inr (inl (inr b))) ∙∙ (λ i → push (inl (inr b) , south) (~ i))) (~ l ∨ ~ j)
-- -- -- --                    ; (k = i1) → push (inl (inr b) , south) j })
-- -- -- --           (inS (push (inl (inr b) , south) (j ∧ k))) l

-- -- -- --   pushoutIsoₛ-filler4 : (n : ℕ) → (b : A B n) → I → I → I → Pushout (pushoutMapₛ n) fst
-- -- -- --   pushoutIsoₛ-filler4 n b i k j =
-- -- -- --     hfill (λ j → λ { (i = i0) → push (inl (inr b) , south) i0
-- -- -- --                    ; (i = i1) → pushoutIsoₛ-filler3 n b j k i1
-- -- -- --                    ; (k = i0) → (push (inl (inr b) , north) ∙∙ (λ _ → inr (inl (inr b))) ∙∙ (λ i → push (inl (inr b) , south) (~ i))) (~ i ∨ ~ j)
-- -- -- --                    ; (k = i1) → push (inl (inr b) , south) (i ∧ j) })
-- -- -- --           (inS (push (inl (inr b) , south) i0)) j

-- -- -- --   pushoutIsoₛ-fun : (n : ℕ) → strictPushout n → (Pushout (pushoutMapₛ n) fst)
-- -- -- --   pushoutIsoₛ-fun n (inl (inl c)) = inl (inl c)
-- -- -- --   pushoutIsoₛ-fun n (inl (inr c)) = inr (inl (inl c))
-- -- -- --   pushoutIsoₛ-fun n (inl (push (c , x) i)) = push (inl (inl c) , x) i
-- -- -- --   pushoutIsoₛ-fun n (inr (inl d)) = inl (inr d)
-- -- -- --   pushoutIsoₛ-fun n (inr (inr d)) = inr (inr d)
-- -- -- --   pushoutIsoₛ-fun n (inr (push (d , x) i)) = push (inr d , x) i
-- -- -- --   pushoutIsoₛ-fun n (push (inl b) i) = inl (push b i)
-- -- -- --   pushoutIsoₛ-fun n (push (inr b) i) = (push (inl (inr b) , north) ∙∙ refl ∙∙ (λ i → push (inl (inr b) , south) (~ i))) i
-- -- -- --   pushoutIsoₛ-fun n (push (push (b , x) j) i) = pushoutIsoₛ-filler1 n b x i j i1

-- -- -- --   pushoutIsoₛ-inv : (n : ℕ) → (Pushout (pushoutMapₛ n) fst) → strictPushout n
-- -- -- --   pushoutIsoₛ-inv n (inl x) = pushoutIsoₛ-inv↪ n x
-- -- -- --   pushoutIsoₛ-inv n (inr (inl (inl c))) = inl (inr c)
-- -- -- --   pushoutIsoₛ-inv n (inr (inl (inr b))) = push (inr b) i0 --inl (inl (strictMap {B} {C} f (suc n) (inr b)))
-- -- -- --   pushoutIsoₛ-inv n (inr (inr d)) = inr (inr d)
-- -- -- --   pushoutIsoₛ-inv n (push (inl (inl c) , x) i) = inl (push (c , x) i)
-- -- -- --   pushoutIsoₛ-inv n (push (inl (inr b) , north) i) = push (inr b) i0 --inl (inl (strictMap {B} {C} f (suc n) (inr b)))
-- -- -- --   pushoutIsoₛ-inv n (push (inl (inr b) , south) i) = push (inr b) (~ i)
-- -- -- --   pushoutIsoₛ-inv n (push (inl (inr b) , merid x j) i) = pushoutIsoₛ-filler2 n b x i j i1
-- -- -- --   pushoutIsoₛ-inv n (push (inr d , x) i) = inr (push (d , x) i)

-- -- -- --   pushoutIsoₛ-rightInv↪ : (n : ℕ) → (x : pushoutA (suc n)) → pushoutIsoₛ-fun n (pushoutIsoₛ-inv↪ n x) ≡ inl x
-- -- -- --   pushoutIsoₛ-rightInv↪ n (inl c) = refl
-- -- -- --   pushoutIsoₛ-rightInv↪ n (inr d) = refl
-- -- -- --   pushoutIsoₛ-rightInv↪ n (push b i) = refl

-- -- -- --   pushoutIsoₛ-rightInv : (n : ℕ) → (x : Pushout (pushoutMapₛ n) fst) → pushoutIsoₛ-fun n (pushoutIsoₛ-inv n x) ≡ x
-- -- -- --   pushoutIsoₛ-rightInv n (inl x) = pushoutIsoₛ-rightInv↪ n x
-- -- -- --   pushoutIsoₛ-rightInv n (inr (inl (inl c))) = refl
-- -- -- --   pushoutIsoₛ-rightInv n (inr (inl (inr b))) = push (inl (inr b) , north)
-- -- -- --   pushoutIsoₛ-rightInv n (inr (inr d)) = refl
-- -- -- --   pushoutIsoₛ-rightInv n (push (inl (inl c) , x) i) = refl
-- -- -- --   pushoutIsoₛ-rightInv n (push (inl (inr b) , north) i) k = push (inl (inr b) , north) (i ∧ k)
-- -- -- --   pushoutIsoₛ-rightInv n (push (inl (inr b) , south) i) k = pushoutIsoₛ-filler4 n b i k i1
-- -- -- --   pushoutIsoₛ-rightInv n (push (inl (inr b) , merid x j) i) k =
-- -- -- --     hcomp (λ l → λ { (i = i0) → hcomp (λ i → λ { (j = i0) → inl (pushoutIsoₛ-filler0 n b x (i ∧ (k ∨ l)) i0)
-- -- -- --                                                ; (j = i1) → inl (pushoutIsoₛ-filler0 n b x (i ∧ (k ∨ l)) i1)
-- -- -- --                                                ; (k = i0) → pushoutIsoₛ-fun n (pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x (l ∧ i) j))
-- -- -- --                                                ; (k = i1) → pushoutIsoₛ-rightInv↪ n (pushoutIsoₛ-filler0 n b x i j) i1
-- -- -- --                                                ; (l = i0) → inl (pushoutIsoₛ-filler0 n b x (i ∧ k) j)
-- -- -- --                                                ; (l = i1) → pushoutIsoₛ-rightInv↪ n (pushoutIsoₛ-filler0 n b x i j) k })
-- -- -- --                                       (inl (push (α B n (b , x)) j))
-- -- -- --                    ; (i = i1) → doubleCompPath-filler (push (inl (inr b) , north))
-- -- -- --                                                       (λ _ → inr (inl (inr b)))
-- -- -- --                                                       (λ i → push (inl (inr b) , south) (~ i)) (~ k) (~ l ∧ j)
-- -- -- --                    ; (j = i0) → hcomp (λ j → λ { (i = i0) → inl (pushoutIsoₛ-filler0 n b x (k ∨ l) i0)
-- -- -- --                                                ; (i = i1) → push (inl (inr b) , north) (k ∧ j)
-- -- -- --                                                ; (k = i0) → pushoutIsoₛ-fun n (invSides-hfill1
-- -- -- --                                                                 (λ i → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i)))))
-- -- -- --                                                                 (λ _ → push (inr b) i0) i (~ l) j)
-- -- -- --                                                ; (k = i1) → push (inl (inr b) , north) (i ∧ j) --?
-- -- -- --                                                ; (l = i0) → invSides-hfill2 (push (inl (inr b) , north))
-- -- -- --                                                                             (λ i → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i)))))
-- -- -- --                                                                             (~ i) ( k) j
-- -- -- --                                                ; (l = i1) → push (inl (inr b) , north) (i ∧ k ∧ j) })
-- -- -- --                                       (inl (pushoutIsoₛ-filler0 n b x (i ∨ k ∨ l) i0))
-- -- -- --                    ; (j = i1) → hcomp (λ j → λ { (i = i0) → inl (pushoutIsoₛ-filler0 n b x (k ∨ l) i1)
-- -- -- --                                                ; (i = i1) → pushoutIsoₛ-filler3 n b j k l
-- -- -- --                                                ; (k = i0) → pushoutIsoₛ-fun n (invSides-hfill1
-- -- -- --                                                                 (λ i → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) (~ i)))))
-- -- -- --                                                                 (λ i → push (inr b) (~ i)) i (~ l) j)
-- -- -- --                                                ; (k = i1) → push (inl (inr b) , south) (i ∧ j)
-- -- -- --                                                ; (l = i0) → invSides-hfill2 (push (inl (inr b) , south))
-- -- -- --                                                                             (λ i → inl (inr (strictMap {B} {D} g (suc n) (push (b , x) (~ i)))))
-- -- -- --                                                                             (~ i) ( k) j
-- -- -- --                                                ; (l = i1) → pushoutIsoₛ-filler4 n b i k j })
-- -- -- --                                       (inl (pushoutIsoₛ-filler0 n b x (i ∨ k ∨ l) i1))
-- -- -- --                    ; (k = i0) → pushoutIsoₛ-fun n (pushoutIsoₛ-filler2 n b x i j l)
-- -- -- --                    ; (k = i1) → push (inl (inr b) , merid x j) i })
-- -- -- --           (pushoutIsoₛ-filler1 n b x j i (~ k))
-- -- -- --   pushoutIsoₛ-rightInv n (push (inr d , x) i) = refl

-- -- -- --   pushoutIsoₛ-leftInv : (n : ℕ) → (x : strictPushout n) → pushoutIsoₛ-inv n (pushoutIsoₛ-fun n x) ≡ x
-- -- -- --   pushoutIsoₛ-leftInv n (inl (inl c)) = refl
-- -- -- --   pushoutIsoₛ-leftInv n (inl (inr c)) = refl
-- -- -- --   pushoutIsoₛ-leftInv n (inl (push (c , x) i)) = refl
-- -- -- --   pushoutIsoₛ-leftInv n (inr (inl d)) = refl
-- -- -- --   pushoutIsoₛ-leftInv n (inr (inr d)) = refl
-- -- -- --   pushoutIsoₛ-leftInv n (inr (push (d , x) i)) = refl
-- -- -- --   pushoutIsoₛ-leftInv n (push (inl b) i) = refl
-- -- -- --   pushoutIsoₛ-leftInv n (push (inr b) i) k =
-- -- -- --     hcomp (λ j → λ { (i = i0) → inl (inl (strictMap {B} {C} f (suc n) (inr b)))
-- -- -- --                    ; (i = i1) → push (inr b) (k ∨ j)
-- -- -- --                    ; (k = i0) → pushoutIsoₛ-inv n (doubleCompPath-filler (push (inl (inr b) , north)) refl
-- -- -- --                                                                          (λ i → push (inl (inr b) , south) (~ i)) j i)
-- -- -- --                    ; (k = i1) → push (inr b) i })
-- -- -- --           (push (inr b) (i ∧ k))
-- -- -- --   pushoutIsoₛ-leftInv n (push (push (b , x) j) i) k =
-- -- -- --     hcomp (λ l → λ { (i = i0) → hcomp (λ i → λ { (j = i0) → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) ((~ l) ∧ (~ k)))))
-- -- -- --                                                ; (j = i1) → inl (inl (e C n .fst (∣ f ∣ (suc n) (invEq (e B n) (inr b)))))
-- -- -- --                                                ; (k = i0) → pushoutIsoₛ-inv n (invSides-hfill2 (push (inl (inr b) , north))
-- -- -- --                                                                               (λ i → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i)))))
-- -- -- --                                                                               (~ j) (~ l) i)
-- -- -- --                                                ; (k = i1) → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) j)))
-- -- -- --                                                ; (l = i0) → invSides-hfill1 (λ i → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i)))))
-- -- -- --                                                                             (λ _ → push (inr b) i0) (~ k) (~ j) i
-- -- -- --                                                ; (l = i1) → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) j))) })
-- -- -- --                                       (inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (((~ k) ∧ (~ l)) ∨ j)))))
-- -- -- --                    ; (i = i1) → hcomp (λ i → λ { (j = i0) → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) ((~ l) ∧ (~ k)))))
-- -- -- --                                                ; (j = i1) → push (inr b) (k ∨ ~ i ∨ l)
-- -- -- --                                                ; (k = i0) → pushoutIsoₛ-inv n (invSides-hfill2 (push (inl (inr b) , south))
-- -- -- --                                                                               (λ i → inl (inr (strictMap {B} {D} g (suc n) (push (b , x) (~ i)))))
-- -- -- --                                                                               (~ j) (~ l) i)
-- -- -- --                                                ; (k = i1) → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) j)))
-- -- -- --                                                ; (l = i0) → invSides-hfill1 (λ i → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) (~ i)))))
-- -- -- --                                                                             (λ i → push (inr b) (~ i)) (~ k) (~ j) i
-- -- -- --                                                ; (l = i1) → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) j))) })
-- -- -- --                                       (inr (inl (strictMap {B} {D} g (suc n) (push (b , x) (((~ k) ∧ (~ l)) ∨ j)))))
-- -- -- --                    ; (j = i0) → pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x ((~ k) ∧ (~ l)) i)
-- -- -- --                    ; (j = i1) → hfill (λ j → λ { (i = i0) → inl (inl (strictMap {B} {C} f (suc n) (inr b)))
-- -- -- --                                                ; (i = i1) → push (inr b) (k ∨ j)
-- -- -- --                                                ; (k = i0) → pushoutIsoₛ-inv n (doubleCompPath-filler (push (inl (inr b) , north)) refl (λ i → push (inl (inr b) , south) (~ i)) j i)
-- -- -- --                                                ; (k = i1) → push (inr b) i })
-- -- -- --                                       (inS (push (inr b) (i ∧ k))) l
-- -- -- --                    ; (k = i0) → pushoutIsoₛ-inv n (pushoutIsoₛ-filler1 n b x i j l)
-- -- -- --                    ; (k = i1) → push (push (b , x) j) i })
-- -- -- --           (pushoutIsoₛ-filler2 n b x j i (~ k))

-- -- -- --   pushoutIsoₛ : (n : ℕ) → Iso (strictPushout n) (Pushout (pushoutMapₛ n) fst)
-- -- -- --   pushoutIsoₛ n = iso (pushoutIsoₛ-fun n) (pushoutIsoₛ-inv n) (pushoutIsoₛ-rightInv n) (pushoutIsoₛ-leftInv n)

-- -- -- --   -- it remains to show that strictPushout is the same as the regular pushout...

-- -- -- --   correctionIsoR : (n : ℕ) → Iso (Pushout (pushoutMapₛ n) fst) (Pushout (pushoutMap (suc n)) fst)
-- -- -- --   correctionIsoR n = pushoutIso _ _ _ _
-- -- -- --     (Σ-cong-equiv (invEquiv (finSplit3≃ (card C (suc n)) (card B n) (card D (suc n))))
-- -- -- --       λ _ → isoToEquiv (invIso (IsoSphereSusp n)))
-- -- -- --       (idEquiv _)
-- -- -- --       (invEquiv (finSplit3≃ (card C (suc n)) (card B n) (card D (suc n))))
-- -- -- --         (λ i x → pushoutMapₛ n (secEq (finSplit3≃  (card C (suc n)) (card B n) (card D (suc n))) (fst x) (~ i)
-- -- -- --                               , Iso.rightInv (IsoSphereSusp n) (snd x) (~ i)))
-- -- -- --         refl

-- -- -- --   correctionIsoL : (n : ℕ) → Iso (pushoutA (suc (suc n))) (strictPushout n)
-- -- -- --   correctionIsoL n =
-- -- -- --     pushoutIso _ _ _ _ (e B n) (isoToEquiv (Iso-strictA-strict²A C (suc (suc n))))
-- -- -- --                        (isoToEquiv (Iso-strictA-strict²A D (suc (suc n))))
-- -- -- --                        (λ i x → inl {!strictMap f!})
-- -- -- --                        {!!}

-- -- -- --   isCWPushout : (n : ℕ) →
-- -- -- --       Iso (pushoutA (suc n))
-- -- -- --           (Pushout (pushoutMap n) fst)
-- -- -- --   isCWPushout zero = {!!} -- _ IsoSucSphereSusp
-- -- -- --   isCWPushout (suc n) = compIso {!!} (compIso (pushoutIsoₛ n) (correctionIsoR n))
-- -- -- --   -- compIso {!idIso!} (compIso (pushoutIsoₛ n) {!!})
-- -- -- -- {-
-- -- -- --   pushoutSkel : CWskel ℓ
-- -- -- --   pushoutSkel = pushoutA , (pushoutCells , pushoutMap , (B .snd .snd .snd .fst) , λ n → isoToEquiv (compIso {!pushoutIsoₛ n!} {!!}))
-- -- -- -- -}
