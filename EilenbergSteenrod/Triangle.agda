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

  Strict→BobΩinm' : (n : ℕ) (w : Fin (card B n)) (s : Susp (S⁻ n))
    → QuotCW B n
  Strict→BobΩinm' n w north = inl tt
  Strict→BobΩinm' n w south = inl tt
  Strict→BobΩinm' (suc n) w (merid a i) = makeLoop Bʷ n a w i
  --

  Strict→BobΩinm : (n : ℕ) (w : Fin (card B (suc n))) (s : Susp (S₊ n))
    → QuotCW B (suc n)
  Strict→BobΩinm n w north = inl tt
  Strict→BobΩinm n w south = inl tt
  Strict→BobΩinm n w (merid a i) = makeLoop Bʷ n a w i

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
        (cong (Strict→BobΩinm n x) (Iso.rightInv (IsoSphereSusp (suc n)) b)) ◁ {!!} -- main b
      where
      pₗG : (a : S₊ n) (w : I) → Path (Bob (suc n)) _ _
      pₗG a w = sym pushₗ ∙ λ i₂ → inl (push (seqMap f (suc (suc n)) (push (x , a) w)) i₂)

      pᵣG : (a : S₊ n) (w : I) → Path (Bob (suc n)) _ _
      pᵣG a w = sym pushᵣ ∙ λ i₂ → inr (push (seqMap g (suc (suc n)) (push (x , a) w)) i₂)

      pₗ = sym pushₗ ∙ λ i₂ → inl (push (seqMap f (suc (suc n)) (inr x)) i₂)
      pᵣ = pᵣG (ptSn n) i1
      -- pᵣ = sym pushᵣ ∙ (λ i₃ → inr (push (seqMap g (suc (suc n)) (inr x)) i₃))

      mainNG mainSG : (a : S₊ n) (i j w k : I) → Bob (suc n)
      mainNG a i j w k =
        hfill (λ k → λ {(i = i0) → inm (rCancel (merid (inl tt)) (~ k) j)
                     ; (i = i1) → pₗG a (w ∨ j) k
                    ; (j = i0) → pₗG a w (i ∧ k) -- ({!!} ∙ {!!}) (i ∧ k) -- pₗ (i ∧ k)
                    ; (j = i1) → pₗ (i ∧ k)})
                    (inS (inm north)) k 
      mainSG a i j w k =
        hfill (λ k → λ {(i = i0) → inm (rCancel (merid (inl tt)) (~ k) j)
                     ; (i = i1) → doubleCompPath-filler
                                      (sym (pᵣG a (w ∨ j))) (λ i → inm (toSusp (QuotCW∙ B (suc n)) (inr (inr x)) (~ i))) pₗ k j
                    ; (j = i0) → pᵣG a w (i ∧ k) -- ({!!} ∙ {!!}) (i ∧ k) -- pₗ (i ∧ k)
                    ; (j = i1) → pₗ (i ∧ k)})
                    (inS (inm (((sym (rCancel (merid (inl tt))))
                     ∙ cong (toSusp (QuotCW∙ B (suc n))) (makePath Bʷ n (ptSn n) x)) i (~ j)))) k 

      mainN mainS : (i j k : I) → Bob (suc n)
      mainN i j k = mainNG (ptSn n) i j k i1 
      mainS i j k = mainSG (ptSn n) i j k i1 

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
      lem2 a = {!cong-∙∙-filler f p q r i1 j i!}

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

      -- MLB : (a : S₊ n)
      --   → (i j k : I) → Bob (suc n)
      -- MLB a i j k =
      --   hfill (λ k → λ { (i = i0) → inm (toSusp (QuotCW∙ B (suc n)) (makeLoop Bʷ n a x j) (~ k))
      --                  ; (i = i1) → cube3 a (~ k) j i1
      --                  ; (j = i0) → mainN i (~ k) i1
      --                  ; (j = i1) → mainS i (~ k) i1
      --                  })
      --         (inS (mainS i i1 i1))
      --         k


      -- mm :  (a : _)
      --   → Square (λ k → inm north) (λ k → cube3 a i0 k i1)
      --             (λ i₁ → mainN i₁ i0 i1) (λ i₁ → mainS i₁ i0 i1)
      -- mm a i j = hcomp (λ k → λ { (i = i0) → {!!}
      --                            ; (i = i1) → {!cube3 a i0 k i1!}
      --                            ; (j = i0) → {!!}
      --                            ; (j = i1) → {!!}
      --                  })
      --             {!!}

      -- ML : (a : _) → Cube (λ i j → MLB a i j i1) -- (λ i j → MLB a i j i1)
      --                      (λ i k → Triangle-inl (suc n) (pushoutMapₛ (suc n) (inl (inr x) , merid a k)) i)
      --                      (λ r k → inm north) (λ r k → mainCubeEq' a (~ r) i0 k) 
      --                      (λ r i → mainN i i0 i1) (λ r i → mainS i i0 i1)
      -- ML a r i j =
      --   hcomp (λ k → λ {(i = i0) → {!!} -- inm north
      --                  ; (i = i1) → {!!} -- cong-∙∙-filler (pushoutA→Bob (suc n) ∘ Iso.inv (IsoModifiedPushout (suc n)) ∘ pushoutIsoₛ-inv↪ (suc n))
      --                               --      (λ i → inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))
      --                               --      (push (α B (suc n) (x , a)))
      --                               --      ((λ i → inr (seqMap g (suc (suc n)) (push (x , a) i)))) k (~ r) j
      --                                    {- cong-∙∙-filler (pushoutA→Bob (suc n) ∘ Iso.inv (IsoModifiedPushout (suc n)) ∘ pushoutIsoₛ-inv↪ (suc n))
      --                                    (λ i → inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))
      --                                    (push (α B (suc n) (x , a)))
      --                                    ((λ i → inr (seqMap g (suc (suc n)) (push (x , a) i)))) k (~ r) j -}
      --                  ; (j = i0) → {!cong-∙∙-filler
      --    (λ x₂ →
      --       pushoutA→Bob (suc n)
      --       (Iso.inv (IsoModifiedPushout (suc n))
      --        (pushoutIsoₛ-inv↪ (suc n) x₂)))
      --    (λ i₂ → inl (seqMap f (suc (suc n)) (push (x , a) (~ i₂))))
      --    (push (α B (suc n) (x , a)))
      --    (λ i₂ → inr (seqMap g (suc (suc n)) (push (x , a) i₂))) k (~ r) i0!}
      --                  ; (j = i1) → {!!}
      --                  ; (r = i0) → {!!} -- MLB a i j k
      --                  ; (r = i1) → Triangle-inl (suc n)
      --                                  (doubleCompPath-filler (λ i → inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))
      --                                                         (push (α B (suc n) (x , a)))
      --                                                         (λ i → inr (seqMap g (suc (suc n)) (push (x , a) i))) k j) i})
      --          {!!}
      --   where -- r k i
      --   alem : Cube {A = Bob (suc n)}
      --               {!!} (λ k i → (sym pushₗ ∙ (λ i₁ → inl (push (seqMap f (suc (suc n)) (push (x , a) k)) i₁))) i)
      --               {!λ i j → pₗ (i ∧ j)!} (λ r i → (sym pushₗ ∙ (λ i₃ → inl (push (seqMap f (suc (suc n)) (inr x)) i₃))) i)
      --               {!!} (λ r k → inl (inr (inl (seqMap f (suc (suc n)) (push (x , a) k)))))
      --   alem = {!!}
      --   -- lem3 : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q r : y ≡ z) (s : q ≡ r)
      --   --   → Cube ?  (λ k i → (p ∙ s k) i) ? (λ s i → (p ∙ r) i) {!!} {!λ r k → q r!}
      --   -- lem3 = {!!}
      --   lem1 :
      --     Cube {A = Bob (suc n)}
      --       (λ j i → compPath-filler (λ k → inl (inr (inl (seqMap f (suc (suc n)) (push (x , a) k))))) (sym pₗ) (~ i) j)
      --       (λ k i → (sym pushₗ
      --                ∙ (λ i₂ → inl (push (seqMap f (suc (suc n))
      --                                (push (x , a) k)) i₂))) i)
      --       {!λ j i → pₗ (~ j ∧ i)!} (λ k i → pₗ i)
      --       (λ i j → {!!})
      --       (λ r k → inl (inr (inl (seqMap f (suc (suc n)) (push (x , a) k)))))
      --   lem1 = {!!}

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
        hcomp (λ r → λ {(i = i0) → i=i0 {A = Bob (suc n) } _ (λ k j → inm (toSusp (QuotCW∙ B (suc n)) (makeLoop Bʷ n a x k) j))
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
          (hcomp (λ r → λ {(i = i0) → {!!}
          {- doubleWhiskFiller
                  {A = λ i → Path (Bob (suc n)) (inm (toSusp (QuotCW∙ B (suc n)) (inl tt) i)) (inm (toSusp (QuotCW∙ B (suc n)) (inl tt) i))}
                                          (sym (rUnit {_} {Bob (suc n)} (refl {x = inm north})))
                                          (λ j₂ k₁ → inm (toSusp (QuotCW∙ B (suc n)) (makeLoop Bʷ n a x k₁) j₂))
                                          refl r j k
                                          -}
                       ; (i = i1) → cube3 a j k r
                       ; (j = i0) → compAltFill _ _ (Triangle-inl (suc n)) (λ i → inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))
                                                              (push (α B (suc n) (x , a)))
                                                              (λ i → inr (seqMap g (suc (suc n)) (push (x , a) i))) k i r
                       ; (j = i1) → doubleCompPath-filler (sym pₗ) (λ i → inm (toSusp (QuotCW∙ B (suc n)) (inr (inr x)) i)) pᵣ i (~ r ∧ k)
                       ; (k = i0) → k=i0 r i j
                       ; (k = i1) → k=i1 r i j})
                  {!!})
        where
        i=i02 : Cube (λ j k → {!!})
                    (λ j k → {!!})
                    (λ r k → {!!})
                    (λ r k → {!!})
                    (λ r j → {!!})
                    (λ r j → {!!}) -- r j k 
        i=i02 = {!!} 
        -- r i j
        k=i0 : Cube (λ i j → (sym pushₗ ∙ λ w → inl (push (seqMap f (suc (suc n)) (push (x , a) j)) w)) i)
                    (λ i j → mainN i j i1)
                    (λ r j → inm (rCancel (merid (inl tt)) (~ r) j))
                    (λ r j → invSides-hfill1 (λ i → inl (inr (inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))))
                                          refl j (~ r) i1)
                    (λ r i → (sym pushₗ ∙ (λ i₂ → inl (push (seqMap f (suc (suc n)) (push (x , a) r)) i₂))) i)
                    (λ r i → pₗ i)
        k=i0 r i j =
          hcomp (λ w → λ {(i = i0) → {!!}
                         ; (i = i1) → {!!}
                         ; (j = i0) → {!!}
                         ; (j = i1) → {!compPath-filler {_} {Bob (suc n)} (sym pushₗ) (λ i₃ → inl (inr (inl (seqMap f (suc (suc n)) (push (x , a) (~ i₃)))))) w i!}
                         ; (r = i0) → {!invSides-hfill1 {A = Bob (suc n)} (λ i → inl (inr (inl (seqMap f (suc (suc n)) (push (x , a) (~ i))))))
                                          refl j (~ r) w!}
                         ; (r = i1) → {!mainNG ai j (~ w)  i1!}})
                         {!!}

        k=i1 : Cube (λ i j → (sym pushᵣ ∙ λ w → inr (push (seqMap g (suc (suc n)) (push (x , a) j)) w)) i)
                    (λ i j → mainS i j i1)
                    (flipSquare (cong (cong inm) (cong sym (sym (rCancel (merid (inl tt))))
                    ∙ cong (sym ∘ toSusp (QuotCW∙ B (suc n))) (makePath Bʷ n a x)))
                    ▷ (λ i j → inm (rCancel (merid (inl tt)) (~ i) j)))
                    (λ r j → cube3 a j i1 r)
                    (λ r i → (sym pushᵣ ∙ (λ i₂ → inr (push (seqMap g (suc (suc n)) (push (x , a) r)) i₂))) i)
                    λ r i → doubleCompPath-filler (λ i₂ → pₗ (~ i₂))
                               (λ i₂ → inm (toSusp (QuotCW∙ B (suc n)) (inr (inr x)) i₂))
                               pᵣ i (~ r) -- (λ r i → pₗ i)
        k=i1 = {!!}


        i=i0 : ∀ {ℓ} {A : Type ℓ}  {x : A} (p : x ≡ x) (Q : p ≡ p)
             (s : refl ∙ refl {x = x} ≡ refl) (t : sym (rUnit refl) ≡ s)
          → Cube (sym (rUnit refl) ◁ (λ j k → (Q k j)))
                   (λ j k → (Q k j))
                  (λ r k → s r k) -- ( λ r k → s r k)
                  (λ _ _ → x) -- (λ _ _ → inm* x)
                  (λ _ i →  (p i)) -- (λ _ i → inm* (p i))
                  λ _ i →  (p i) -- λ _ i → inm* (p i) -- 
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
