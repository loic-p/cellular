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

module Bob (ℓ : Level) (Bʷ Cʷ Dʷ : CWskel ℓ) where

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
    hcomp (λ k → λ { (i = i0) → (sym pushₗ ∙ (λ i → inl (push (inl (seqMap f n a)) i))) (k ∧ (~ j))
                   ; (i = i1) → (sym pushᵣ ∙ (λ i → inr (push (inl (seqMap g n a)) i))) (k ∧ (~ j))
                   ; (j = i0) → doubleCompPath-filler (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i)))
                                                      (λ i → inm (toSusp (QuotCW∙ B n) (inr (inl a)) i))
                                                      (sym pushᵣ ∙ (λ i → inr (push (inl (seqMap g n a)) i))) k i
                   ; (j = i1) → inm north })
          (inm (hcomp (λ k → λ { (i = i0) → north
                               ; (i = i1) → merid (inl tt) (~ k)
                               ; (j = i0) → doubleCompPath-filler refl (merid (inr (inl a))) (sym (merid (inl tt))) k i
                               ; (j = i1) → merid (inl tt) (i ∧ (~ k)) })
                       (merid (push a (~ j)) i)))

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

  TriangleL : (n : ℕ) (x : _) → pushoutA→Bob n x ≡ Strict→Bob n (Iso.fun (pushoutIsoₜ (suc n)) x)
  TriangleL n (inl (inl x)) = {!push!} ∙ {!!}
  TriangleL n (inl (inr x)) = {!!}
  TriangleL n (inl (push a i)) = {!!}
  TriangleL n (inr x) = {!!}
  TriangleL n (push a i) = {!!}

  Triangle-inl : (n : ℕ) (x : _) → inm north ≡ pushoutA→Bob n (Iso.inv (pushoutIsoₜ (suc n)) (inl x))
  Triangle-inl n (inl x) = sym pushₗ ∙ λ i → inl (push x i)
  Triangle-inl n (inr x) = sym pushᵣ ∙ λ i → inr (push x i)
  Triangle-inl n (push a i) j =
    hcomp (λ k → λ {(i = i0) → (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i))) (~ j ∨ ~ k)
                   ; (i = i1) → (sym pushᵣ ∙ λ i → inr (push (inl (seqMap g n a)) i)) (j ∧ k)
                   ; (j = i0) → inm (rCancel (merid (inl tt)) k i)
                   ; (j = i1) → doubleCompPath-filler (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i)))
                                                       (λ i → inm (toSusp (QuotCW∙ B n) (inr (inl a)) i))
                                                       (sym pushᵣ ∙ λ i → inr (push (inl (seqMap g n a)) i)) k i})
          (inm (toSusp (QuotCW∙ B n) (push a j) i))

  Triangle-inr : (n : ℕ)  (x : _) → inm north ≡ pushoutA→Bob n (modifiedPushout→Pushout n (pushoutIsoₛ-inv n (inr x)))
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
        (cong (Strict→BobΩinm n x) (Iso.rightInv (IsoSphereSusp (suc n)) b)) ◁ main b
      where
      pₗ = sym pushₗ ∙ λ i₂ → inl (push (seqMap f (suc (suc n)) (inr x)) i₂)
      pᵣ = sym pushᵣ ∙ (λ i₃ → inr (push (seqMap g (suc (suc n)) (inr x)) i₃))

      mainN mainS : (i j k : I) → Bob (suc n)
      mainN i j k = hfill (λ k → λ {(i = i0) → inm (rCancel (merid (inl tt)) (~ k) j)
                     ; (i = i1) → pₗ k
                    ; (j = i0) → pₗ (i ∧ k)
                    ; (j = i1) → pₗ (i ∧ k)})
                    (inS (inm north)) k
      mainS i j k =
        hfill (λ k → λ {(i = i0) → inm (rCancel (merid (inl tt)) (~ k) j)
                       ; (i = i1) → doubleCompPath-filler
                                      (sym pᵣ) (λ i → inm (toSusp (QuotCW∙ B (suc n)) (inr (inr x)) (~ i))) pₗ k j
                       ; (j = i0) → pᵣ (k ∧ i)
                       ; (j = i1) → pₗ (k ∧ i)})
                (inS (inm (((sym (rCancel (merid (inl tt))))
                     ∙ cong (toSusp (QuotCW∙ B (suc n))) (makePath Bʷ n (ptSn n) x)) i (~ j)))) k

      main : (b : Susp (S₊ n))
        → Square (λ i₁ → inm (toSusp (QuotCW∙ B (suc n))
                            (Strict→BobΩinm n x b) i₁))
                  (λ i₁ → pushoutA→Bob (suc n)
                           (Iso.inv (IsoModifiedPushout (suc n))
                             (Iso.inv (pushoutIsoₛ (suc n)) (push (inl (inr x) , b) i₁))))
                  (Triangle-inl (suc n) (pushoutMapₛ (suc n) (inl (inr x) , b)))
                  (sym pushₗ ∙ λ i₂ → inl (push (seqMap f (suc (suc n)) (inr x)) i₂))
      main north i j = mainN i j i1
      main south i j = mainS i j i1
      main (merid a k) i j =
        hcomp (λ r → λ {(i = i0) → {!!}
                       ; (i = i1) → pushoutA→Bob (suc n) (Iso.inv (IsoModifiedPushout (suc n))
                                       (pushoutIsoₛ-filler2 (suc n) x a j k r))
                       ; (j = i0) → {!!}
                       ; (j = i1) → {!!}
                       ; (k = i0) → {!mainN i j i1!}
                       ; (k = i1) → {!mainS i j i1!}}) {!!}
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
