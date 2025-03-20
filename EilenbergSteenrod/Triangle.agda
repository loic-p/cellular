{-# OPTIONS --cubical #-}
module EilenbergSteenrod.Triangle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.Map
open import Cubical.CW.ChainComplex

open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive
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

open import EilenbergSteenrod.StrictifyCW renaming (strictCWskel to str)
open import EilenbergSteenrod.CWPushout
open import Cubical.Foundations.Pointed

open SequenceMap renaming (map to seqMap)

-- lemmas
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


cong-invSides-hfill1 : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  → {x y z : A} (p : x ≡ y) (q : x ≡ z)
    → Cube {A = B} (λ i j → invSides-hfill1 (cong f p) (cong f q) i j i1)
                   (λ i j → f (invSides-hfill1 p q i j i1))
            (λ i j → f (p j )) (λ i j → f (q (~ j)))
            refl refl
cong-invSides-hfill1 f p q i j k =
  hcomp (λ r → λ {(i = i1) → f (invSides-hfill1 p q j k r)
                 ; (j = i0) → f (p k)
                 ; (j = i1) → f (q (~ k ∧ r))
                 ; (k = i0) → f (q (j ∧ r))
                 ; (k = i1) → f (p (~ j))})
        (f (p (~ j ∧ k)))


silly : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (b : B) (x : A)
  → cong-∙∙ (λ (x : A) → b) (refl {x = x}) refl refl ≡ rUnit refl 
silly {A = A} b x i j k =
  hcomp (λ r → λ {(i = i0) → cong-∙∙-filler (λ (x : A) → b) (refl {x = x}) refl refl r j k
                 ; (i = i1) → rUnit (refl {x = b}) j k -- rUnit (refl {x = b}) j k
                 ; (j = i0) → b
                 ; (j = i1) → rUnit (refl {x = b}) (i ∨ r) k
                 ; (k = i0) → b
                 ; (k = i1) → b})
        (rUnit (λ _ → b) (i ∧ j) k)

module _ {ℓ : Level} {A : Type ℓ} {x y z : A} (pushₗ* : x ≡ y) (inl-push-inr : y ≡ z) (σ⋆ : x ≡ x) (rC : refl ≡ σ⋆)  where
  mainNGen : (i j k : I) → A
  mainNGen i j k =
    hfill (λ k → λ {(i = i0) → rC k j
               ; (i = i1) → (pushₗ* ∙ inl-push-inr) k
              ; (j = i0) → (pushₗ* ∙ inl-push-inr) (i ∧ k)
              ; (j = i1) → (pushₗ* ∙ inl-push-inr)  (i ∧ k)})
              (inS x) k

  module _ {y' z' : A} (pushᵣ* : x ≡ y') (inr-push-inr : y' ≡ z') (σ⋆' : x ≡ x) (q : σ⋆ ≡ σ⋆') where
    mainSGen : (i j k : I) → A
    mainSGen i j k =
      hfill (λ k → λ {(i = i0) → rC k j
                 ; (i = i1) → doubleCompPath-filler (sym (pushᵣ* ∙ inr-push-inr)) (sym σ⋆') (pushₗ* ∙ inl-push-inr) k j
                ; (j = i0) → (pushᵣ* ∙ inr-push-inr) (i ∧ k)
                ; (j = i1) → (pushₗ* ∙ inl-push-inr)  (i ∧ k)})
                (inS ((rC ∙ q) i (~ j))) k

module Bob (ℓ : Level) (Bʷ Cʷ Dʷ : CWskel ℓ) where

module _ {ℓ ℓ'} {A : Type ℓ}  {B : Type ℓ'} (f g : A → B) (P : (x : _) → f x  ≡ g x)  {x y z w : A}
  (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) where
  compAltFill : (i j k : I) → B
  compAltFill i j k =
    hfill (λ k → λ {(i = i0) → P (p (~ k)) j
                               ; (i = i1) → P (r k) j
                               ; (j = i0) → doubleCompPath-filler (cong f p) (cong f q) (cong f r) k i
                               ; (j = i1) → doubleCompPath-filler (cong g p) (cong g q) (cong g r) k i})
                      (inS (P (q i) j)) k

  compAlt : PathP (λ i → (cong f p ∙∙ cong f q ∙∙ cong f r) i
                        ≡ (cong g p ∙∙ cong g q ∙∙ cong g r) i)
                  (P x) (P w)
  compAlt i j = compAltFill i j i1

  cong-∙∙≡ : SquareP (λ i j → cong-∙∙ f p q r i j ≡ cong-∙∙ g p q r i j)
                     (cong P (p ∙∙ q ∙∙ r)) (compAlt) refl refl
  cong-∙∙≡ i j k =
    hcomp (λ w → λ {(i = i0) → P (doubleCompPath-filler p q r w j) k
                    ; (i = i1) → compAltFill j k w
                    ; (j = i0) → P (p (~ w)) k
                    ; (j = i1) → P (r w) k
                    ; (k = i0) → cong-∙∙-filler f p q r w i j
                    ; (k = i1) → cong-∙∙-filler g p q r w i j})
           (P (q j) k)

IsoSphereSuspInv∙ : (n : ℕ) → Iso.inv (IsoSphereSusp n) north ≡ ptSn n
IsoSphereSuspInv∙ zero = refl
IsoSphereSuspInv∙ (suc zero) = refl
IsoSphereSuspInv∙ (suc (suc n)) = refl

cellMap→finCellMap : ∀ {ℓ ℓ'} (m : ℕ) {C : CWskel ℓ} {D : CWskel ℓ'} (ϕ : cellMap C D) → finCellMap m C D
FinSequenceMap.fmap (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.map ϕ x
FinSequenceMap.fcomm (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.comm ϕ x

QuotCW : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Type ℓ
QuotCW C n = cofib (CW↪ C n)

QuotCW∙ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Pointed ℓ
QuotCW∙ C n = QuotCW C n , inl tt

data 3⋁ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  inl : fst A → 3⋁ A B C
  inm : fst B → 3⋁ A B C
  inr : fst C → 3⋁ A B C

  pushₗ : inl (pt A) ≡ inm (pt B)
  pushᵣ : inr (pt C) ≡ inm (pt B)

3⋁Susp-inl : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') → Susp (A .fst) → Susp (3⋁ A B C)
3⋁Susp-inl A B C north = north
3⋁Susp-inl A B C south = south
3⋁Susp-inl A B C (merid a i) = merid (inl a) i

3⋁Susp-inm : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') → Susp (B .fst) → Susp (3⋁ A B C)
3⋁Susp-inm A B C north = north
3⋁Susp-inm A B C south = south
3⋁Susp-inm A B C (merid b i) = merid (inm b) i

3⋁Susp-inr : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') → Susp (C .fst) → Susp (3⋁ A B C)
3⋁Susp-inr A B C north = north
3⋁Susp-inr A B C south = south
3⋁Susp-inr A B C (merid c i) = merid (inr c) i

3⋁Susp-Susp3⋁ : ∀ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'')
                → 3⋁ (Susp∙ (A .fst)) (Susp∙ (B .fst)) (Susp∙ (C .fst))
                → Susp (3⋁ A B C)
3⋁Susp-Susp3⋁ A B C (inl x) = 3⋁Susp-inl A B C x
3⋁Susp-Susp3⋁ A B C (inm x) = 3⋁Susp-inm A B C x
3⋁Susp-Susp3⋁ A B C (inr x) = 3⋁Susp-inr A B C x
3⋁Susp-Susp3⋁ A B C (pushₗ i) = north
3⋁Susp-Susp3⋁ A B C (pushᵣ i) = north

module _ (ℓ : Level) (Bʷ Cʷ Dʷ : CWskel ℓ)
  (fʷ : cellMap (str Bʷ) (str Cʷ))
  (gʷ : cellMap (str Bʷ) (str Dʷ)) where
  open Pushoutz ℓ Bʷ Cʷ Dʷ fʷ gʷ

  Bob : (n : ℕ) → Type ℓ
  Bob n = 3⋁ (QuotCW∙ C (suc n)) (Susp∙ (QuotCW B n)) (QuotCW∙ D (suc n))

  pushoutA→Bob : (n : ℕ) → pushoutA (suc (suc n)) → Bob n
  pushoutA→Bob n (inl x) = inl (inr x)
  pushoutA→Bob n (inr x) = inr (inr x)
  pushoutA→Bob n (push a i) =
    (sym (sym pushₗ ∙ λ i → inl (push (seqMap f (suc n) a) i))
    ∙∙ (λ i → inm (toSusp (QuotCW∙ B n) (inr a) i))
    ∙∙ (sym pushᵣ ∙ (λ i → inr (push (seqMap g (suc n) a) i)))) i

  -- inl (f a) ---- push a i ---- inr (g a)

  -- inl (inr (f a))                                          inr (inr (g a))
  --        |                                                        |
  --   inl north                                                 inr north
  --        |                                                        |
  -- inm north -- inm (merid (inr a)) -- inm (sym (merid base)) -- inm north

  open CWskel-fields
  open import Cubical.HITs.Wedge.Properties

  subpushout→Bob : (n : ℕ) → (x : pushoutA (suc n)) → pushoutA→Bob n (CW↪ pushoutSkel (suc n) x) ≡ inm north
  subpushout→Bob n (inl x) i = (sym pushₗ ∙ (λ i → inl (push x i))) (~ i)
  subpushout→Bob n (inr x) i = (sym pushᵣ ∙ (λ i → inr (push x i))) (~ i)
  subpushout→Bob n (push a i) j =
    hcomp (λ k → λ {(i = i0) → (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i))) (j ∨ ~ k)
                   ; (i = i1) → (sym pushᵣ ∙ λ i → inr (push (inl (seqMap g n a)) i)) (~ j ∧ k)
                   ; (j = i0) → doubleCompPath-filler (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i)))
                                                      (λ i → inm (toSusp (QuotCW∙ B n) (inr (inl a)) i))
                                                      (sym pushᵣ ∙ (λ i → inr (push (inl (seqMap g n a)) i))) k i
                   ; (j = i1) → inm (rCancel (merid (inl tt)) k i)})
          (inm (toSusp (QuotCW∙ B n) (push a (~ j)) i))

  Pn+1/Pn→Bob : (n : ℕ) → QuotCW pushoutSkel (suc n) → Bob n
  Pn+1/Pn→Bob n (inl x) = inm north
  Pn+1/Pn→Bob n (inr x) = pushoutA→Bob n x
  Pn+1/Pn→Bob n (push a i) = subpushout→Bob n a (~ i)

  open CWskel-fields
  open import Cubical.HITs.Wedge.Properties

  makePath : ∀ {ℓ} (D : CWskel ℓ) (n : ℕ) (s : S₊ n) (s : Fin (card (str D) (suc n)))
    → Path (QuotCW (str D) (suc n)) (inl tt) (inr (inr s))
  makePath D n s w = (push (α (str D) (suc n) (w , s)) ∙ λ i → inr (push (w , s) i))

  makeLoop : ∀ {ℓ} (D : CWskel ℓ) (n : ℕ) (s : S₊ n) (s : Fin (card (str D) (suc n)))
    → Path (QuotCW (str D) (suc n)) (inl tt) (inl tt)
  makeLoop D n s w = makePath D n s w ∙ sym (makePath D n (ptSn n) w)


  Strict→BobΩinm : (n : ℕ) (w : Fin (card B (suc n))) (s : Susp (S₊ n))
    → QuotCW B (suc n)
  Strict→BobΩinm n w north = inl tt
  Strict→BobΩinm n w south = inl tt
  Strict→BobΩinm n w (merid a i) = makeLoop Bʷ n a w (~ i) --------- Had to add inversion!!

  Strict→BobΩ : (n : ℕ) (a : (Fin (card C (suc n)) ⊎ Fin (card B n)) ⊎ Fin (card D (suc n)))
              → S₊ n → Path (Bob n) (inm north) (inm north)
  Strict→BobΩ n (inl (inl s)) x = sym pushₗ
            ∙∙ (λ i → inl (makeLoop Cʷ n x s i))
            ∙∙ pushₗ
  Strict→BobΩ zero (inl (inr s)) false = sym (cong inm (toSusp (QuotCW∙ B zero) (inr (invEq (CW₁-discrete B) s))))
  Strict→BobΩ zero (inl (inr s)) true = refl
  Strict→BobΩ (suc n) (inl (inr s)) x =
    cong inm (toSusp (QuotCW∙ B (suc n)) (Strict→BobΩinm n s (Iso.fun (IsoSucSphereSusp n) x)))
  Strict→BobΩ n (inr s) x =
    sym pushᵣ
    ∙∙ (λ i → inr (makeLoop Dʷ n x s i))
    ∙∙ pushᵣ

  Strict→Bob : (n : ℕ) → Pushout (pushoutMap (suc n)) fst → Bob n
  Strict→Bob n (inl x) = inm north
  Strict→Bob n (inr x) = inm north
  Strict→Bob n (push (a , b) i) =
    Strict→BobΩ n (Iso.fun (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))) a) b i


  Triangle-inl : (n : ℕ) (x : pushoutA (suc n)) → inm north ≡ pushoutA→Bob n (Iso.inv (pushoutIsoₜ (suc n)) (inl x))
  Triangle-inl n x = sym (subpushout→Bob n x)

  Triangle-inr : (n : ℕ) (x : _) → inm north ≡ pushoutA→Bob n (modifiedPushout→Pushout n (pushoutIsoₛ-inv n (inr x)))
  Triangle-inr n (inl (inl x)) = sym pushₗ ∙ (λ i → inl ((push (α C (suc n) (x , ptSn n)) ∙ λ i → inr (push (x , ptSn n) i)) i))
  Triangle-inr n (inl (inr x)) = sym pushₗ ∙ λ i → inl (push (seqMap f (suc n) (inr x)) i)
  Triangle-inr n (inr x) = sym pushᵣ ∙ (λ i → inr ((push (α D (suc n) (x , ptSn n)) ∙ λ i → inr (push (x , ptSn n) i)) i))

  Triangle : (n : ℕ) (x : _) → Strict→Bob n x ≡ pushoutA→Bob n (Iso.inv (pushoutIsoₜ (suc n)) x)
  Triangle n (inl x) = Triangle-inl n x
  Triangle n (inr x) = Triangle-inr n (Iso.fun (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))) x)
  Triangle n (push (a , b) i) j =
    ((λ j → Strict→BobΩ n (Iso.fun (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))) a) (Iso.leftInv (IsoSphereSusp n) b (~ j)))
    ◁ help n (Iso.fun (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))) a) (Iso.fun (IsoSphereSusp n) b)
    ▷ cong (cong (λ w → pushoutA→Bob n (Iso.inv (compIso (IsoModifiedPushout n) (pushoutIsoₛ n)) w)))
           (rUnit (push (Iso.fun (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))) a , Iso.fun (IsoSphereSusp n) b)))) j i
    where

    help : (n : ℕ) (a : _) (b : Susp (S⁻ n))
      → Square (Strict→BobΩ n a (Iso.inv (IsoSphereSusp n) b))
                (λ i → pushoutA→Bob n (Iso.inv (compIso (IsoModifiedPushout n) (pushoutIsoₛ n)) (push (a , b) i)))
                (Triangle-inl n (pushoutMapₛ n (a , b)))
                (Triangle-inr n a)
    help n (inl (inl x)) b i j =
      hcomp (λ k → λ {(i = i1) → inl (inr (push (x , EquivSphereSusp n .fst b) j))
                     ; (j = i0) → compPath-filler' (sym (pushₗ))
                                     (λ i → inl (push (e C n .fst (α C (suc n)
                                                  (x , EquivSphereSusp n .fst b))) i)) k i
                     ; (j = i1) → compPath-filler' (sym (pushₗ))
                                     (λ i → inl ((push (α C (suc n) (x , ptSn n))
                                     ∙ (λ i₃ → inr (push (x , ptSn n) i₃))) i)) k i})
            (inl (hcomp (λ k → λ {(i = i0) → compPath-filler
                                                 (makePath Cʷ n (Iso.inv (IsoSphereSusp n) b) x)
                                                 (sym (makePath Cʷ n (IsoSphereSuspInv∙ n (k ∨ ~ i)) x)) k j
                                 ; (i = i1) → inr (push (x , EquivSphereSusp n .fst b) j)
                                 ; (j = i0) → push (e C n .fst (α C (suc n) (x , EquivSphereSusp n .fst b))) i
                                 ; (j = i1) → makePath Cʷ n (ptSn n) x (~ k ∨ i)})
                        (compPath-filler' (push (e C n .fst (α C (suc n) (x , EquivSphereSusp n .fst b))))
                                         (λ j → inr (push (x , EquivSphereSusp n .fst b) j)) (~ i) j)))
    help zero (inl (inr x)) north =
      λ j _ → ((λ i₁ → pushₗ (~ i₁)) ∙
       (λ i₁ → inl (push (seqMap f 1 (inr x)) i₁))) j
    help zero (inl (inr x)) south i j =
      hcomp (λ k → λ {(i = i0) → inm ((toSusp (QuotCW∙ B zero) (inr (invEq (CW₁-discrete B) x)) (~ j)))
                     ; (j = i0) → (sym pushᵣ ∙ λ i₂ → inr (push (seqMap g 1 (inr x)) i₂)) (k ∧ i)
                     ; (j = i1) → (sym pushₗ ∙ λ i₂ → inl (push (seqMap f 1 (inr x)) i₂)) (k ∧ i)})
            (inm (toSusp (QuotCW∙ B zero) (inr (inr x)) (~ j)))
    help (suc n) (inl (inr x)) b =
      cong (cong inm ∘ toSusp (QuotCW∙ B (suc n)))
        (cong (Strict→BobΩinm n x) (Iso.rightInv (IsoSphereSusp (suc n)) b)) ◁ main b -- 
      where
      pₗ = sym pushₗ ∙ λ i₂ → inl (push (seqMap f (suc (suc n)) (inr x)) i₂)
      pᵣ = sym pushᵣ ∙ (λ i₃ → inr (push (seqMap g (suc (suc n)) (inr x)) i₃))


      module _ {ℓ : Level} {A : Type ℓ} {x : A} (y : A) (pushₗ* : x ≡ y) (z : A) (inl-push-inr : y ≡ z) (σ⋆ : x ≡ x) (rC : refl ≡ σ⋆)  where
      mainN mainS : (i j k : I) → Bob (suc n)
      mainN = mainNGen {A = Bob (suc n)} (sym pushₗ) (λ i₂ → inl (push (seqMap f (suc (suc n)) (inr x)) i₂))
                       (cong inm (toSusp (QuotCW∙ B (suc n)) (inl tt))) (cong (cong inm) (sym (rCancel (merid (inl tt)))))
      mainS = mainSGen {A = Bob (suc n)} (sym pushₗ) (λ i₂ → inl (push (seqMap f (suc (suc n)) (inr x)) i₂))
                       (cong inm (toSusp (QuotCW∙ B (suc n)) (inl tt))) (cong (cong inm) (sym (rCancel (merid (inl tt)))))
                       (sym pushᵣ) (λ i₂ → inr (push (seqMap g (suc (suc n)) (inr x)) i₂))
                       ((λ i → inm (toSusp (QuotCW∙ B (suc n)) (inr (inr x)) i)))
                       λ j i → inm (toSusp (QuotCW∙ B (suc n)) (makePath Bʷ n (ptSn n) x j) i)

      term : (a : S₊ n) (i j k : I) → Bob (suc n)
      term a j k r = pushoutA→Bob (suc n) (Iso.inv (IsoModifiedPushout (suc n))
                                       (pushoutIsoₛ-filler2 (suc n) x a j k r))

      mainCube1 mainCube2  : (a : S₊ n)
        → Square (λ k → term a i0 k i1) (λ k → term a i1 k i1)
                (λ j → term a j i0 i1) (λ j → term a j i1 i1)
      mainCube1 a j k = term a j k i1
      mainCube2 a j k =
        hcomp (λ r → λ {(j = i0) → pushoutA→Bob (suc n) (Iso.inv (IsoModifiedPushout (suc n))
                                      (pushoutIsoₛ-inv↪ (suc n) (pushoutIsoₛ-filler0 (suc n) x a r k)))
                       ; (j = i1) → pushoutA→Bob (suc n) (push (inr x) (~ r ∧ k))
                       ; (k = i0) → pushoutA→Bob (suc n)
                                       (Iso.inv (IsoModifiedPushout (suc n))
                                         (invSides-hfill1 (λ i → inl (inl (seqMap f (suc (suc n)) (push (x , a) (~ i)))))
                                                     (λ _ → push (inr x) i0) j (~ r) i1))
                       ; (k = i1) → pushoutA→Bob (suc n)
                                       (Iso.inv (IsoModifiedPushout (suc n))
                                         (invSides-hfill1 (λ i → inr (inl (seqMap g (suc (suc n)) (push (x , a) (~ i)))))
                                                (λ i → push (inr x) (~ i)) j (~ r) i1))})
              (pushoutA→Bob (suc n) (push (push (x , a) j) k))

      cube3 : (a : S₊ n) (i j k : I) → Bob (suc n)
      cube3 a j k i =
        hfill (λ r → λ {(j = i0) →
          doubleCompPath-filler (λ i → inl (inr (inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))))
                                (cong (pushoutA→Bob (suc n)) (push (inl (α B (suc n) (x , a)))))
                                (λ i → inr (inr (inl (seqMap g (suc (suc n)) (push (x , a) i)))))
                                r k
                       ; (j = i1) → pushoutA→Bob (suc n) (push (inr x) (~ r ∧ k))
                       ; (k = i0) → invSides-hfill1 (λ i → inl (inr (inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))))
                                       refl j (~ r) i1
                       ; (k = i1) → invSides-hfill1 (λ i → inr (inr (inl (seqMap g (suc (suc n)) (push (x , a) (~ i))))))
                                       (sym (cong (pushoutA→Bob (suc n)) (push (inr x)))) j (~ r) i1})
              (inS (pushoutA→Bob (suc n) (push (push (x , a) j) k))) i

      lem2 : (a : S₊ n) → Cube (mainCube2 a) (λ j k → cube3 a j k i1)
                                (cong-∙∙ (pushoutA→Bob (suc n) ∘ Iso.inv (IsoModifiedPushout (suc n)) ∘ pushoutIsoₛ-inv↪ (suc n))
                                         (λ i → inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))
                                         (push (α B (suc n) (x , a)))
                                         ((λ i → inr (seqMap g (suc (suc n)) (push (x , a) i)))))
                                (λ _ k → cube3 a i1 k i1)
                                (λ j i → term a i i0 i1)
                                (λ j i → term a i i1 i1)
      lem2 a i j k =
        hcomp (λ r → λ {(j = i1) → cube3 a i1 k r
                       ; (j = i0) → (cong-∙∙-filler (pushoutA→Bob (suc n) ∘ Iso.inv (IsoModifiedPushout (suc n)) ∘ pushoutIsoₛ-inv↪ (suc n))
                                         (λ i → inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))
                                         (push (α B (suc n) (x , a)))
                                         ((λ i → inr (seqMap g (suc (suc n)) (push (x , a) i))))) r i k
                       ; (k = i0) → cong-invSides-hfill1 (pushoutA→Bob (suc n) ∘ Iso.inv (IsoModifiedPushout (suc n)))
                                      (λ i → inl (inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))) refl (~ i) j (~ r)
                       ; (k = i1) → cong-invSides-hfill1 (pushoutA→Bob (suc n) ∘ Iso.inv (IsoModifiedPushout (suc n)))
                                      (λ i → inr (inl (seqMap g (suc (suc n)) (push (x , a) (~ i)))))
                                      (sym (push (inr x))) (~ i) j (~ r)})
               (cube3 a j k i0)

      mainCubeEq : (a : _) → mainCube1 a ≡ mainCube2 a
      mainCubeEq a r j k =
        hcomp (λ w → λ {(j = i0) → pushoutA→Bob (suc n) (Iso.inv (IsoModifiedPushout (suc n))
                                      (pushoutIsoₛ-inv↪ (suc n) (pushoutIsoₛ-filler0 (suc n) x a w k)))
                       ; (r = i0) → pushoutA→Bob (suc n) (Iso.inv (IsoModifiedPushout (suc n))
                                       (pushoutIsoₛ-filler2 (suc n) x a j k w))
                       ; (j = i1) → pushoutA→Bob (suc n) (push (inr x) (~ w ∧ k))
                       ; (k = i0) → pushoutA→Bob (suc n)
                                       (Iso.inv (IsoModifiedPushout (suc n))
                                         (invSides-hfill1 (λ i → inl (inl (seqMap f (suc (suc n)) (push (x , a) (~ i)))))
                                                     (λ _ → push (inr x) i0) j (~ w) i1))
                       ; (k = i1) → pushoutA→Bob (suc n)
                                       (Iso.inv (IsoModifiedPushout (suc n))
                                         (invSides-hfill1 (λ i → inr (inl (seqMap g (suc (suc n)) (push (x , a) (~ i)))))
                                                (λ i → push (inr x) (~ i)) j (~ w) i1))})
              (pushoutA→Bob (suc n) (push (push (x , a) j) k))

      mainCubeEq' : (a : _) → Cube (mainCube1 a) (λ j k → cube3 a j k i1)
                                (cong-∙∙ (pushoutA→Bob (suc n) ∘ Iso.inv (IsoModifiedPushout (suc n)) ∘ pushoutIsoₛ-inv↪ (suc n))
                                         (λ i → inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))
                                         (push (α B (suc n) (x , a)))
                                         ((λ i → inr (seqMap g (suc (suc n)) (push (x , a) i)))))
                                (λ _ k → cube3 a i1 k i1)
                                (λ j i → term a i i0 i1)
                                (λ j i → term a i i1 i1)
      mainCubeEq' a = (mainCubeEq a) ◁ lem2 a

      main : (b : Susp (S₊ n))
        → Square (λ i₁ → inm (toSusp (QuotCW∙ B (suc n))
                            (Strict→BobΩinm n x b) i₁))
                  (λ i₁ → pushoutA→Bob (suc n)
                           (Iso.inv (IsoModifiedPushout (suc n))
                             (Iso.inv (pushoutIsoₛ (suc n)) (push (inl (inr x) , b) i₁))))
                  (Triangle-inl (suc n) (pushoutMapₛ (suc n) (inl (inr x) , b)))
                  pₗ
      main north i j = mainN i j i1
      main south i j = mainS i j i1
      main (merid a k) i j =
        hcomp (λ r → λ {(i = i0) → i=i0 {A = Bob (suc n) } _ (λ k j → inm (toSusp (QuotCW∙ B (suc n)) (makeLoop Bʷ n a x (~ k)) j))
                                      (sym (cong-∙∙ {A = pushoutA (suc (suc n))} (λ _ → inm north)
                                        (λ i₁ → inl (seqMap f (suc (suc n)) (push (x , a) (~ i₁))))
                                         (push (α B (suc n) (x , a)))
                                         (λ i₁ → inr (seqMap g (suc (suc n)) (push (x , a) i₁)))))
                                      (cong sym (sym (silly {A = pushoutA (suc (suc n))} (inm north) (inl (seqMap f (suc (suc n)) (inr x))))))
                                      r j k
                       ; (i = i1) → mainCubeEq' a (~ r) j k -- mainCubeEq' a (~ i1) j k
                       ; (j = i0) → cong-∙∙≡ _ _ (Triangle-inl (suc n)) (λ i → inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))
                                                              (push (α B (suc n) (x , a)))
                                                              (λ i → inr (seqMap g (suc (suc n)) (push (x , a) i))) (~ r) k i
                       ; (j = i1) → pₗ i
                       ; (k = i0) → mainN i j i1
                       ; (k = i1) → mainS i j i1})
          (hcomp (λ r → λ {(i = i0) → i=i0' r j k -- i=i0' r j k
                       ; (i = i1) → cube3 a j k r
                       ; (j = i0) → compAltFill _ _ (Triangle-inl (suc n)) (λ i → inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))
                                                              (push (α B (suc n) (x , a)))
                                                              (λ i → inr (seqMap g (suc (suc n)) (push (x , a) i))) k i r
                       ; (j = i1) → doubleCompPath-filler (sym pₗ) (λ i → inm (toSusp (QuotCW∙ B (suc n)) (inr (inr x)) i)) pᵣ i (~ r ∧ k)
                       ; (k = i0) → k=i0 r i j
                       ; (k = i1) → k=i1 r i j})
             (hcomp (λ r → λ {(i = i0) → compPath-filler' {_} {Path (Bob (suc n)) _ _}
                                                  ((λ j₂ i₂ → inm (rCancel (merid (inl tt)) (~ j₂) i₂)))
                                                  ((λ j₂ i₂ → inm (toSusp (QuotCW∙ B (suc n)) (makePath Bʷ n a x j₂) i₂))) r j k
                                  ; (i = i1) → hfill
                                                  (doubleComp-faces
                                                   (λ i₂ →
                                                      ((λ i₃ → pushₗ (~ i₃)) ∙
                                                       (λ i₃ → inl (push (seqMap f (suc (suc n)) (push (x , a) j)) i₃)))
                                                      (~ i₂))
                                                   ((λ i₂ → pushᵣ (~ i₂)) ∙
                                                    (λ i₂ → inr (push (seqMap g (suc (suc n)) (push (x , a) j)) i₂)))
                                                   k)
                                                  (inS (inm (toSusp (QuotCW∙ B (suc n)) (inr (push (x , a) j)) k))) r
                                  ; (j = i1) → doubleCompPath-filler (λ i₂ → pₗ (~ i₂)) (λ i₂ → inm (toSusp (QuotCW∙ B (suc n)) (inr (inr x)) i₂)) pᵣ (i ∧ r) k
                                  ; (k = i0) → ((sym pushₗ ∙ (λ w → inl (push (seqMap f (suc (suc n)) (push (x , a) j)) w))) (i ∧ r))
                                  ; (k = i1) → ((sym pushᵣ ∙ (λ w → inr (push (seqMap g (suc (suc n)) (push (x , a) j)) w))) (i ∧ r))})
                     (inm (toSusp (QuotCW∙ B (suc n))
                       (compPath-filler' (push (α B (suc n) (x , a))) (λ j → inr (push (x , a) j)) (~ i) j) k))))

        where

        k=i0Gen : {ℓ : Level} {A : Type ℓ} {x : A} (y : A) (pushₗ* : x ≡ y) (z : A)
                              (inl-push-inr : y ≡ z)
                              (z' : A)
                              (corrz : z ≡ z')
                              (inl-push-inr' : y ≡ z')
                              (sq : Square inl-push-inr inl-push-inr' refl corrz)
                              (σ⋆ : x ≡ x) (rC : refl ≡ σ⋆)
                → Cube (λ i j → (pushₗ* ∙ λ w → sq (~ j) w) i)
                    (λ i j → mainNGen pushₗ* inl-push-inr σ⋆ rC i j i1)
                    (λ r j → rC r j)
                    (λ r j → invSides-hfill1 corrz
                                          refl j (~ r) i1)
                    (λ r i → (pushₗ* ∙ λ w → sq (~ r) w) i)
                    (λ r i → (pushₗ* ∙ inl-push-inr) i)
        k=i0Gen {x = x} = J> (J> (J> (J> (J>
          λ r i j → hcomp (λ k → λ {(i = i0) → x
                                    ; (i = i1) → invSides-hfill1 R R j (~ r) k
                                    ; (j = i0) → (R ∙ R) i
                                    ; (j = i1) → (R ∙ R) i
                                    ; (r = i0) → (R ∙ R) i
                                    ; (r = i1) → mainNGen R R R refl i j i1})
            (hcomp (λ k → λ {(i = i0) → x
                         ; (i = i1) → (R ∙ R) k
                         ; (j = i0) → (R ∙ R) (i ∧ k)
                         ; (j = i1) → (R ∙ R) (i ∧ k)
                         ; (r = i0) → (R ∙ R) (i ∧ k) -- 
                         ; (r = i1) → mainNGen R R R refl i j k})
                   x)))))
             where
             R = refl {x = x}

        k=i0 : Cube (λ i j → (sym pushₗ ∙ λ w → inl (push (seqMap f (suc (suc n)) (push (x , a) j)) w)) i)
                    (λ i j → mainN i j i1)
                    (λ r j → inm (rCancel (merid (inl tt)) (~ r) j))
                    (λ r j → invSides-hfill1 (λ i → inl (inr (inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))))
                                          refl j (~ r) i1)
                    (λ r i → (sym pushₗ ∙ (λ i₂ → inl (push (seqMap f (suc (suc n)) (push (x , a) r)) i₂))) i)
                    (λ r i → pₗ i)
        k=i0 = k=i0Gen _ _ _ _ _ _ _ _ _ _

        k=i1Gen : {ℓ : Level} {A : Type ℓ}
          {x : A} (y : A) (pushₗ* : x ≡ y) (z : A) (inl-push-inr : y ≡ z) (σ⋆ : x ≡ x) (rC : refl ≡ σ⋆)
          (y' : A) (pushᵣ* : x ≡ y') (z' : A) (inr-push-inr : y' ≡ z') (σ⋆' : x ≡ x) (q : σ⋆ ≡ σ⋆')
          (z'' : A) (corrz : z' ≡ z'')
          (inr-push-inr' : y' ≡ z'')
          (sq : Square inr-push-inr inr-push-inr' refl corrz)
          → Cube (λ i j → (pushᵣ* ∙ (λ w → sq (~ j) w)) i)
                    (λ i j → mainSGen {A = A} pushₗ* inl-push-inr σ⋆ rC pushᵣ* inr-push-inr σ⋆' q i j i1)
                    (flipSquare (cong sym rC ∙ cong sym q) ▷ (λ i j → rC i j)) -- (flipSquare {!? ∙ ?!} ◁ {!!}) --  ∙ (λ r j → {!λ !})
                    (λ r j → invSides-hfill1  corrz ((sym (pushᵣ* ∙ inr-push-inr) ∙∙ sym σ⋆' ∙∙ (pushₗ* ∙ inl-push-inr))) j (~ r) i1)
                    (λ r i → (pushᵣ* ∙ (λ w → sq (~ r) w)) i)
                    (λ r i → doubleCompPath-filler (sym (pushₗ* ∙ inl-push-inr)) σ⋆' (pushᵣ* ∙ inr-push-inr) i (~ r))
        k=i1Gen {x = x} = J> (J> (J> (J> (J> (J> (J> (J> c)))))))
         where -- r i j
         R = refl {x = x}

         -- Very stupid hole... just refls everywhere...
         c : Cube (λ i j → (R ∙ R) i) (λ i j → mainSGen R R refl refl R refl refl refl i j i1)
                  (flipSquare (refl {x = R} ∙ refl) ▷ refl)
                  (λ r j → invSides-hfill1 R (sym (R ∙ R) ∙∙ R ∙∙ (R ∙ R)) j (~ r) i1)
                  (λ r i → (R ∙ R) i) λ r i → doubleCompPath-filler (sym (R ∙ R)) R (R ∙ R) i (~ r)
         c r i j = {!!}
         {- hcomp (λ k
            → λ {(i = i0) → {!mainSGen R R (λ _ → x) (λ _ → refl) R (λ _ → x) (λ _ → x)
         (λ _ _ → x) i i0 k!}
                ; (i = i1) → {!k!} -- invSides-hfill1 R (sym (R ∙ R) ∙∙ R ∙∙ (R ∙ R)) j (~ r) k -- invSides-hfill1 refl (sym (R ∙ refl) ∙∙ sym refl ∙∙ (refl ∙ refl)) j (~ r) i1
                ; (j = i0) → (R ∙ R) (i ∧ k) -- (R ∙ R) i
                ; (j = i1) → {!(R ∙ R) i!} -- (R ∙ R) i
                ; (r = i0) → mainSGen R R (λ _ → x) (λ _ → refl) R (λ _ → x) (λ _ → x) (λ _ _ → x) i i0 k -- (R ∙ R) i -- (R ∙ R) i
                ; (r = i1) → mainSGen R R refl refl R refl refl refl i j k -- mainSGen R R refl refl R refl refl refl i j k
                }) {!!}
                -}

        k=i1 : Cube (λ i j → (sym pushᵣ ∙ λ w → inr (push (seqMap g (suc (suc n)) (push (x , a) j)) w)) i)
                    (λ i j → mainS i j i1)
                    (flipSquare ((cong (cong inm) (cong sym (sym (rCancel (merid (inl tt)))))
                    ∙ cong (cong inm) (cong (sym ∘ toSusp (QuotCW∙ B (suc n)) ) (makePath Bʷ n (ptSn n) x))))
                    ▷ (λ i j → inm (rCancel (merid (inl tt)) (~ i) j)))
                    (λ r j → cube3 a j i1 r)
                    (λ r i → (sym pushᵣ ∙ (λ i₂ → inr (push (seqMap g (suc (suc n)) (push (x , a) r)) i₂))) i)
                    λ r i → doubleCompPath-filler (λ i₂ → pₗ (~ i₂))
                               (λ i₂ → inm (toSusp (QuotCW∙ B (suc n)) (inr (inr x)) i₂))
                               pᵣ i (~ r)
        k=i1 = k=i1Gen _ _ _ _ _ _  _ _ _ _ _ _ _ _ _ _

        i=i0Gen : {ℓ : Level} {A : Type ℓ}
          {x : A}
          (σ⋆ : x ≡ x) (rC : refl ≡ σ⋆)
          (σ⋆' : x ≡ x) (q : σ⋆ ≡ σ⋆')
          (LOOP : σ⋆ ≡ σ⋆)
          (q' : σ⋆ ≡ σ⋆')
          (pp : Square LOOP q' refl q)
          → Cube (rC ∙ q') -- (sym LOOP) ∙ q)
                  (sym (rUnit refl) ◁ flipSquare (sym LOOP)) -- (rC ◁ {!λ i j → qX i j!})
                  (rUnit (refl {x = x}))
                  (λ r k → σ⋆' (~ r ∧ k)) -- (
                  rC -- rC
                  ((flipSquare (cong sym rC ∙ cong sym q) ▷ (λ i j → rC i j))) -- 
        i=i0Gen {x = x} = J> (J> λ p
          → J> (sym (lUnit p) ◁ (cubePermute-ijk↦kji (cubePermute-ijk↦kji
                     (doubleCompPath-filler (sym (rUnit refl)) p refl)
                     ▷ (rUnit refl ∙ rUnit _))
                   ▷ cong₂ _◁_ refl (sym≡flipSquare (sym p)))))

        i=i0' : Cube {A = Bob (suc n)}
                     ((λ j i → inm (rCancel (merid (inl tt)) (~ j) i))
                       ∙ (λ j i → inm (toSusp (QuotCW∙ B (suc n)) (makePath Bʷ n a x j) i)))
                     (sym (rUnit (refl {x = inm north}))
                     ◁ (λ j₂ k₁ → inm (toSusp (QuotCW∙ B (suc n)) (makeLoop Bʷ n a x (~ k₁)) j₂)))
                     (rUnit (refl {x = inm north}))
                     (λ r k → inm (toSusp (QuotCW∙ B (suc n)) (inr (inr x)) (~ r ∧ k)))
                     (λ r j → inm (rCancel (merid (inl tt)) (~ r) j))
                     ((flipSquare
                         (cong (cong inm)
                          (cong sym (sym (rCancel (merid (pt (QuotCW∙ B (suc n)))))))
                          ∙
                          cong (cong inm)
                          (cong (sym ∘ toSusp (QuotCW∙ B (suc n)))
                           (makePath Bʷ n (ptSn n) x)))
                         ▷ (λ i₂ j₂ → inm (rCancel (merid (inl tt)) (~ i₂) j₂))))
        i=i0' = i=i0Gen _ _ _ _ _ _
          λ i j k → inm ((toSusp (QuotCW∙ B (suc n))
            (compPath-filler
              (makePath Bʷ n a x)
              (sym (makePath Bʷ n (ptSn n) x)) (~ i) j) k))

        i=i0 : ∀ {ℓ} {A : Type ℓ}  {x : A} (p : x ≡ x) (Q : p ≡ p)
             (s : refl ∙ refl {x = x} ≡ refl) (t : sym (rUnit refl) ≡ s)
          → Cube (sym (rUnit refl) ◁ (λ j k → (Q k j)))
                   (λ j k → (Q k j))
                  (λ r k → s r k)
                  (λ _ _ → x)
                  (λ _ i →  (p i))
                  λ _ i →  (p i)
        i=i0 {x = x} p Q s t = cong₂ _◁_ t refl
          ◁ symP (doubleWhiskFiller s (λ j k → (Q k j)) (λ _ _ → x))
    help n (inr x) b i j =
      hcomp (λ k → λ {(i = i1) → inr (inr (push (x , EquivSphereSusp n .fst b) j))
                     ; (j = i0) → compPath-filler' (sym (pushᵣ))
                                     (λ i → inr (push (e D n .fst (α D (suc n)
                                                  (x , EquivSphereSusp n .fst b))) i)) k i
                     ; (j = i1) → compPath-filler' (sym (pushᵣ))
                                     (λ i → inr ((push (α D (suc n) (x , ptSn n))
                                     ∙ (λ i₃ → inr (push (x , ptSn n) i₃))) i)) k i})
            (inr (hcomp (λ k → λ {(i = i0) → compPath-filler
                                                 (makePath Dʷ n (Iso.inv (IsoSphereSusp n) b) x)
                                                 (sym (makePath Dʷ n (IsoSphereSuspInv∙ n (k ∨ ~ i)) x)) k j
                                 ; (i = i1) → inr (push (x , EquivSphereSusp n .fst b) j)
                                 ; (j = i0) → push (e D n .fst (α D (suc n) (x , EquivSphereSusp n .fst b))) i
                                 ; (j = i1) → makePath Dʷ n (ptSn n) x (~ k ∨ i)})
                        (compPath-filler' (push (e D n .fst (α D (suc n) (x , EquivSphereSusp n .fst b))))
                                         (λ j → inr (push (x , EquivSphereSusp n .fst b) j)) (~ i) j)))

  Pˢn+1/Pn→Bob : (n : ℕ) → cofib {B = Pushout (pushoutMap (suc n)) fst} inl → Bob n
  Pˢn+1/Pn→Bob n (inl x) = inm north
  Pˢn+1/Pn→Bob n (inr x) = Strict→Bob n x
  Pˢn+1/Pn→Bob n (push a i) = inm north

  Pˢn+1/Pn→Pn+1/Pn : (n : ℕ) → cofib {B = Pushout (pushoutMap (suc n)) fst} inl → QuotCW pushoutSkel (suc n)
  Pˢn+1/Pn→Pn+1/Pn n (inl x) = inl x
  Pˢn+1/Pn→Pn+1/Pn n (inr x) = inr (Iso.inv (pushoutIsoₜ (suc n)) x)
  Pˢn+1/Pn→Pn+1/Pn n (push a i) = push a i

  Pn+1/Pn→Bob≡Pˢn+1/Pn→Bob : (n : ℕ) (x : _) → Pˢn+1/Pn→Bob n x ≡ Pn+1/Pn→Bob n (Pˢn+1/Pn→Pn+1/Pn n x)
  Pn+1/Pn→Bob≡Pˢn+1/Pn→Bob n (inl x) = refl
  Pn+1/Pn→Bob≡Pˢn+1/Pn→Bob n (inr x) = Triangle n x
  Pn+1/Pn→Bob≡Pˢn+1/Pn→Bob n (push a i) j = subpushout→Bob n a (~ i ∨ ~ j)

  fn+1/fn : (n : ℕ) → QuotCW B n → QuotCW C n
  fn+1/fn n = prefunctoriality.fn+1/fn {C = B} {D = C} (suc n) (cellMap→finCellMap (suc n) {B} {C} f) flast

  gn+1/gn : (n : ℕ) → QuotCW B n → QuotCW D n
  gn+1/gn n = prefunctoriality.fn+1/fn {C = B} {D = D} (suc n) (cellMap→finCellMap (suc n) {B} {D} g) flast

  ∂middle : (n : ℕ) → Susp (QuotCW B (suc n)) → 3⋁ (Susp∙ (QuotCW C (suc n))) (Susp∙ (Susp (QuotCW B n))) (Susp∙ (QuotCW D (suc n)))
  ∂middle n north = inm north
  ∂middle n south = inm north
  ∂middle n (merid b i) =
    (((sym pushₗ) ∙∙ ((λ i → inl (merid (fn+1/fn (suc n) b) i)) ∙ (λ i → inl (merid (inl tt) (~ i)))) ∙∙ pushₗ)
    ∙∙ ((λ i → inm (merid north i)) ∙ (λ i → inm (merid (suspFun (to_cofibCW n B) (δ (suc n) B b)) (~ i))))
    ∙∙ ((sym pushᵣ) ∙∙ ((λ i → inr (merid (inl tt) i)) ∙ (λ i → inr (merid (gn+1/gn (suc n) b) (~ i)))) ∙∙ pushᵣ)) i

  ∂BobΣ : (n : ℕ) → Bob (suc n) → 3⋁ (Susp∙ (QuotCW C (suc n))) (Susp∙ (Susp (QuotCW B n))) (Susp∙ (QuotCW D (suc n)))
  ∂BobΣ n (inl x) = inl (suspFun (to_cofibCW (suc n) C) (δ (suc (suc n)) C x))
  ∂BobΣ n (inm x) = ∂middle n x
  ∂BobΣ n (inr x) = inr (suspFun (to_cofibCW (suc n) D) (δ (suc (suc n)) D x))
  ∂BobΣ n (pushₗ i) = pushₗ i
  ∂BobΣ n (pushᵣ i) = pushᵣ i

  ∂Bob : (n : ℕ) → Bob (suc n) → Susp (Bob n)
  ∂Bob n x = 3⋁Susp-Susp3⋁ _ _ _ (∂BobΣ n x)

  easyHomotopy : (n : ℕ) → (x : QuotCW pushoutSkel (suc (suc n)))
    → ∂Bob n (Pn+1/Pn→Bob (suc n) x) ≡ (suspFun (Pn+1/Pn→Bob n) ∘ suspFun (to_cofibCW (suc n) pushoutSkel) ∘ δ (suc (suc n)) pushoutSkel) x
  easyHomotopy n x = {!!}
