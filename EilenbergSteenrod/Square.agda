{-# OPTIONS --cubical --allow-unsolved-metas #-}
module EilenbergSteenrod.Square where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Pointed

open import Cubical.Homotopy.Loopspace

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
open import EilenbergSteenrod.Triangle

module _ (ℓ : Level) (Bʷ Cʷ Dʷ : CWskel ℓ)
  (fʷ : cellMap (str Bʷ) (str Cʷ))
  (gʷ : cellMap (str Bʷ) (str Dʷ)) where

  open Pushoutz ℓ Bʷ Cʷ Dʷ fʷ gʷ
  open Trianglez ℓ Bʷ Cʷ Dʷ fʷ gʷ
  open SequenceMap renaming (map to seqMap)

  fn+1/fn : (n : ℕ) → QuotCW B n → QuotCW C n
  fn+1/fn n = prefunctoriality.fn+1/fn {C = B} {D = C} (suc n) (cellMap→finCellMap (suc n) {B} {C} f) flast

  gn+1/gn : (n : ℕ) → QuotCW B n → QuotCW D n
  gn+1/gn n = prefunctoriality.fn+1/fn {C = B} {D = D} (suc n) (cellMap→finCellMap (suc n) {B} {D} g) flast

  -- first attempt at defining the boundary map for Bob
  ∂middle-old : (n : ℕ) → Susp (QuotCW B (suc n)) → 3⋁ (Susp∙ (QuotCW C (suc n))) (Susp∙ (Susp (QuotCW B n))) (Susp∙ (QuotCW D (suc n)))
  ∂middle-old n north = inm north
  ∂middle-old n south = inm north
  ∂middle-old n (merid b i) =
    (((sym pushₗ) ∙∙ (λ i → inl (toSusp (QuotCW∙ C (suc n)) ((fn+1/fn (suc n) b)) i)) ∙∙ pushₗ)
    ∙∙ (λ i → inm (toSusp (Susp∙ (QuotCW B n)) (suspFun (to_cofibCW n B) (δ (suc n) B b)) (~ i)))
    ∙∙ ((sym pushᵣ) ∙∙ (λ i → inr (toSusp (QuotCW∙ D (suc n)) ((gn+1/gn (suc n) b)) (~ i))) ∙∙ pushᵣ)) i


  ∂BobΣ : (n : ℕ) → Bob (suc n) → 3⋁ (Susp∙ (QuotCW C (suc n))) (Susp∙ (Susp (QuotCW B n))) (Susp∙ (QuotCW D (suc n)))
  ∂BobΣ n (inl x) = inl (suspFun (to_cofibCW (suc n) C) (δ (suc (suc n)) C x))
  ∂BobΣ n (inm x) = ∂middle-old n x
  ∂BobΣ n (inr x) = inr (suspFun (to_cofibCW (suc n) D) (δ (suc (suc n)) D x))
  ∂BobΣ n (pushₗ i) = pushₗ i
  ∂BobΣ n (pushᵣ i) = pushᵣ i

  ∂Bob-old : (n : ℕ) → Bob (suc n) → Susp (Bob n)
  ∂Bob-old n x = 3⋁Susp-Susp3⋁ _ _ _ (∂BobΣ n x)

  -- ∂Bob is a simplified version of ∂Bob-old
  ∂middle-aux : (n : ℕ) → (b : QuotCW B (suc n)) → typ (Ω (Susp∙ (Bob n)))
  ∂middle-aux n b =
    toSusp (Bob∙ n) (inl ((fn+1/fn (suc n) b)))
    ∙∙ sym (toSusp (Bob∙ n) (inm (suspFun (to_cofibCW n B) (δ (suc n) B b))))
    ∙∙ sym (toSusp (Bob∙ n) (inr ((gn+1/gn (suc n) b))))

  ∂middle : (n : ℕ) → Susp (QuotCW B (suc n)) → Susp (Bob n)
  ∂middle n north = north
  ∂middle n south = north
  ∂middle n (merid b i) = ∂middle-aux n b i

  ∂Bob : (n : ℕ) → Bob (suc n) → Susp (Bob n)
  ∂Bob n (inl x) = suspFun ((toBob_l n) ∘ (to_cofibCW (suc n) C)) (δ (suc (suc n)) C x)
  ∂Bob n (inm x) = ∂middle n x
  ∂Bob n (inr x) = suspFun ((toBob_r n) ∘ (to_cofibCW (suc n) D)) (δ (suc (suc n)) D x)
  ∂Bob n (pushₗ i) = north
  ∂Bob n (pushᵣ i) = north

  -- ∂Bob' is a simplified version of ∂Bob
  ∂middle-aux' : (n : ℕ) → (b : QuotCW B (suc n)) → typ (Ω (Susp∙ (Bob n)))
  ∂middle-aux' n b =
    merid (inl ((fn+1/fn (suc n) b)))
    ∙∙ (refl
       ∙∙ sym (merid (inm (suspFun (to_cofibCW n B) (δ (suc n) B b))))
       ∙∙ merid (inm north))
    ∙∙ sym (merid (inr ((gn+1/gn (suc n) b))))

  ∂middle' : (n : ℕ) → Susp (QuotCW B (suc n)) → Susp (Bob n)
  ∂middle' n north = north
  ∂middle' n south = north
  ∂middle' n (merid b i) = ∂middle-aux' n b i

  ∂Bob' : (n : ℕ) → Bob (suc n) → Susp (Bob n)
  ∂Bob' n (inl x) = suspFun ((toBob_l n) ∘ (to_cofibCW (suc n) C)) (δ (suc (suc n)) C x)
  ∂Bob' n (inm x) = ∂middle' n x
  ∂Bob' n (inr x) = suspFun ((toBob_r n) ∘ (to_cofibCW (suc n) D)) (δ (suc (suc n)) D x)
  ∂Bob' n (pushₗ i) = north
  ∂Bob' n (pushᵣ i) = north

  -- Proof that ∂Bob' ≡ ∂Bob
  ∂middle-aux-eq : (n : ℕ) → (b : QuotCW B (suc n)) → (∂middle-aux n b) ≡ (∂middle-aux' n b)
  ∂middle-aux-eq n b =
    (cong₂ (λ (p q : _≡_ {A = Susp (Bob n)} north north) → (p1 ∙ sym p0) ∙∙ p ∙∙ q) (symDistr p2 (sym p0)) (symDistr p3 (sym p0)))
    ∙ (doubleCompPath≡compPath (p1 ∙ sym p0) (p0 ∙ sym p2) (p0 ∙ sym p3))
    ∙ (assoc (p1 ∙ sym p0) (p0 ∙ sym p2) (p0 ∙ sym p3))
    ∙ cong (λ (p : _≡_ {A = Susp (Bob n)} north north) → p ∙ (p0 ∙ sym p3))
        ((assoc (p1 ∙ sym p0) p0 (sym p2))
        ∙ cong (λ (p : _≡_ {A = Susp (Bob n)} north south) → p ∙ (sym p2))
           (sym (assoc p1 (sym p0) p0)
           ∙ cong (λ (p : _≡_ {A = Susp (Bob n)} south south) → p1 ∙ p) (lCancel p0)
           ∙ (sym (rUnit p1))))
    ∙ sym (assoc p1 (sym p2) (p0 ∙ sym p3))
    ∙ cong (λ (p : _≡_ {A = Susp (Bob n)} south north) → p1 ∙ p) (assoc (sym p2) p0 (sym p3))
    ∙ sym (doubleCompPath≡compPath p1 (sym p2 ∙ p0) (sym p3))
    where
      p0 p1 p2 p3 : _≡_ {A = Susp (Bob n)} north south
      p0 = merid (inm north)
      p1 = merid (inl ((fn+1/fn (suc n) b)))
      p2 = merid (inm (suspFun (to_cofibCW n B) (δ (suc n) B b)))
      p3 = merid (inr ((gn+1/gn (suc n) b)))

  ∂Bob-eq : (n : ℕ) (x : Bob (suc n)) → ∂Bob n x ≡ ∂Bob' n x
  ∂Bob-eq n (inl x) = refl
  ∂Bob-eq n (inm north) = refl
  ∂Bob-eq n (inm south) = refl
  ∂Bob-eq n (inm (merid b i)) j = ∂middle-aux-eq n b j i
  ∂Bob-eq n (inr x) = refl
  ∂Bob-eq n (pushₗ i) = refl
  ∂Bob-eq n (pushᵣ i) = refl

  -- Now we need to compute ∂Bob' (Pn+1/Pn→Bob (suc n) x)
  -- First, we will simplify Pn+1/Pn→Bob
  subpushout→Bob-filler : (n : ℕ) → (a : B .fst n) → I → I → I → Bob n
  subpushout→Bob-filler n a i j =
    hfill (λ k → λ {(i = i0) → (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i))) (j ∨ ~ k)
                   ; (i = i1) → (sym pushᵣ ∙ λ i → inr (push (inl (seqMap g n a)) i)) (~ j ∧ k)
                   ; (j = i0) → doubleCompPath-filler (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i)))
                                                      (λ i → inm (toSusp (QuotCW∙ B n) (inr (inl a)) i))
                                                      (sym pushᵣ ∙ (λ i → inr (push (inl (seqMap g n a)) i))) k i
                   ; (j = i1) → inm (rCancel (merid (inl tt)) k i)})
          (inS (inm (toSusp (QuotCW∙ B n) (push a (~ j)) i)))

  prefiller0 : (n : ℕ) (a : B .fst n) → I → I → I → Susp (QuotCW B n)
  prefiller0 n a i j =
    hfill (λ k → λ { (i = i0) → merid (inl tt) (j ∧ (~ k))
                   ; (i = i1) → (doubleCompPath-filler refl (merid (inr (inl a))) (sym (merid (inl tt))) k j)
                   ; (j = i0) → north
                   ; (j = i1) → merid (inl tt) (~ k) })
          (inS (merid (push a i) j))

  filler0 : (n : ℕ) (a : B .fst n) → Square {A = Susp (QuotCW B n)} (λ i → north) (λ i → (toSusp (QuotCW∙ B n) (inr (inl a)) i)) refl refl
  filler0 n a i j = prefiller0 n a i j i1

  subpushout→Bob'-filler : (n : ℕ) → (a : B .fst n) → I → I → I → Bob n
  subpushout→Bob'-filler n a i j =
    hfill (λ k → λ {(i = i0) → (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i))) (j ∨ ~ k)
                   ; (i = i1) → (sym pushᵣ ∙ λ i → inr (push (inl (seqMap g n a)) i)) (~ j ∧ k)
                   ; (j = i0) → doubleCompPath-filler (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i)))
                                                      (λ i → inm (toSusp (QuotCW∙ B n) (inr (inl a)) i))
                                                      (sym pushᵣ ∙ (λ i → inr (push (inl (seqMap g n a)) i))) k i
                   ; (j = i1) → inm north})
          (inS (inm (filler0 n a (~ j) i)))

  subpushout→Bob' : (n : ℕ) → (x : pushoutA (suc n)) → pushoutA→Bob n (CW↪ pushoutSkel (suc n) x) ≡ inm north
  subpushout→Bob' n (inl x) i = (sym pushₗ ∙ (λ i → inl (push x i))) (~ i)
  subpushout→Bob' n (inr x) i = (sym pushᵣ ∙ (λ i → inr (push x i))) (~ i)
  subpushout→Bob' n (push a i) j = subpushout→Bob'-filler n a i j i1

  Pn+1/Pn→Bob' : (n : ℕ) → QuotCW pushoutSkel (suc n) → Bob n
  Pn+1/Pn→Bob' n (inl x) = inm north
  Pn+1/Pn→Bob' n (inr x) = pushoutA→Bob n x
  Pn+1/Pn→Bob' n (push a i) = subpushout→Bob' n a (~ i)

  -- Proof that Pn+1/Pn→Bob ≡ Pn+1/Pn→Bob'
  filler0-old : (n : ℕ) (a : B .fst n)
    → Square {A = Susp (QuotCW B n)} (merid (inl tt) ∙ (sym (merid (inl tt)))) (λ i → (toSusp (QuotCW∙ B n) (inr (inl a)) i)) refl refl
  filler0-old n a i j = toSusp (QuotCW∙ B n) (push a i) j

  filler0-eq : (n : ℕ) (a : B .fst n) → Cube {A = Susp (QuotCW B n)}
           (filler0-old n a) (filler0 n a) (λ i j → rCancel (merid (inl tt)) i j)
           (λ j i → (toSusp (QuotCW∙ B n) (inr (inl a)) i)) (λ i j → north) (λ i j → north)
  filler0-eq n a i j k =
    hcomp (λ l → λ { (i = i0) → doubleCompPath-filler refl (merid (push a j)) (sym (merid (inl tt))) l k
                   ; (i = i1) → prefiller0 n a j k l
                   ; (j = i0) → hcomp (λ j → λ { (i = i0) → doubleCompPath-filler refl (merid (inl tt)) (sym (merid (inl tt))) (l ∧ j) k
                                               ; (i = i1) → merid (inl tt) (k ∧ (~ l))
                                               ; (l = i0) → merid (inl tt) k
                                               ; (l = i1) → rCancel-filler (merid (inl tt)) j i k
                                               ; (k = i1) → merid (inl tt) ((~ i ∧ ~ j) ∨ (~ l))
                                               ; (k = i0) → north })
                                      (merid (inl tt) (k ∧ (~ (i ∧ l))))
                   ; (j = i1) → doubleCompPath-filler refl (merid (push a i1)) (sym (merid (inl tt))) l k
                   ; (k = i1) → merid (inl tt) (~ l)
                   ; (k = i0) → north })
          (merid (push a j) k)

  subpushout→Bob-eq : (n : ℕ) → (x : pushoutA (suc n)) → subpushout→Bob n x ≡ subpushout→Bob' n x
  subpushout→Bob-eq n (inl x) = refl
  subpushout→Bob-eq n (inr x) = refl
  subpushout→Bob-eq n (push a i) j k =
    hcomp (λ l → λ { (i = i0) → (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i))) (k ∨ ~ l)
                   ; (i = i1) → (sym pushᵣ ∙ λ i → inr (push (inl (seqMap g n a)) i)) (~ k ∧ l)
                   ; (j = i0) → subpushout→Bob-filler n a i k l
                   ; (j = i1) → subpushout→Bob'-filler n a i k l
                   ; (k = i1) → inm (rCancel (merid (inl tt)) (j ∨ l) i)
                   ; (k = i0) → doubleCompPath-filler (sym (sym pushₗ ∙ λ i → inl (push (inl (seqMap f n a)) i)))
                                                      (λ i → inm (toSusp (QuotCW∙ B n) (inr (inl a)) i))
                                                      (sym pushᵣ ∙ (λ i → inr (push (inl (seqMap g n a)) i))) l i })
          (inm (filler0-eq n a j (~ k) i))

  Pn+1/Pn→Bob-eq : (n : ℕ) → (x : QuotCW pushoutSkel (suc n)) → Pn+1/Pn→Bob n x ≡ Pn+1/Pn→Bob' n x
  Pn+1/Pn→Bob-eq n (inl x) = refl
  Pn+1/Pn→Bob-eq n (inr x) = refl
  Pn+1/Pn→Bob-eq n (push a i) j = subpushout→Bob-eq n a j (~ i)

  -- Next, we simplify ∂Bob' (Pn+1/Pn→Bob' (suc n) x)
  ∂filler0 : (n : ℕ) (a : B .fst (suc n))
    → Square {A = Susp (Bob n)} (λ i → north) (λ i → ∂middle' n (toSusp (QuotCW∙ B (suc n)) (inr (inl a)) i)) (λ i → north) (λ i → north)
  ∂filler0 n a i j = ∂Bob' n (inm (filler0 (suc n) a i j))

  filler2 : (n : ℕ) → Square (λ i → ∂middle' n (merid (inl tt) i)) refl refl refl
  filler2 n i j =
    hcomp (λ k → λ { (i = i0) → doubleCompPath-filler (merid (inl (inl tt)))
                                                      ((sym (merid (inm north))) ∙ (merid (inm north)))
                                                      (sym (merid (inr (inl tt)))) k j
                   ; (i = i1) → merid (inm north) (~ k)
                   ; (j = i0) → merid (pushₗ i) (~ k)
                   ; (j = i1) → merid (pushᵣ i) (~ k) })
          (rCancel (sym (merid (inm north))) i j)

  pre∂filler0' : (n : ℕ) (a : B .fst (suc n)) → I → I → I → Susp (Bob n)
  pre∂filler0' n a i j =
    hfill (λ k → λ { (i = i0) → filler2 n k j
                   ; (i = i1) → ∂middle-aux' n (inr (inl a)) j --constant
                   ; (j = i0) → north
                   ; (j = i1) → north })
          (inS (∂middle-aux' n (push a i) j))

  ∂filler0' : (n : ℕ) (a : B .fst (suc n))
    → Square {A = Susp (Bob n)} (λ i → north) (∂middle-aux' n (inr (inl a))) (λ i → north) (λ i → north)
  ∂filler0' n a i j = pre∂filler0' n a i j i1

  step1-cod : (n : ℕ) → (fst pushoutSkel (suc (suc (suc n)))) → Susp (Bob n)
  step1-cod n (inl x) = south
  step1-cod n (inr x) = south
  step1-cod n (push a i) =
    ((sym (merid (inl (inr (seqMap f (suc (suc n)) a)))))
    ∙∙ (∂middle-aux' n (inr a))
    ∙∙ (merid (inr (inr (seqMap g (suc (suc n)) a))))) i

  step1-filler : (n : ℕ) → (a : B .fst (suc n)) → I → I → I → Susp (Bob n)
  step1-filler n a i j =
    hfill (λ k → λ { (i = i0) → merid (inl (inr (inl (seqMap f (suc n) a)))) (k ∧ j)
                   ; (i = i1) → merid (inr (inr (inl (seqMap g (suc n) a)))) (k ∧ j)
                   ; (j = i0) → north
                   ; (j = i1) → doubleCompPath-filler (sym (merid (inl (inr (inl (seqMap f (suc n) a))))))
                                                      (∂middle-aux' n (inr (inl a)))
                                                      (merid (inr (inr (inl (seqMap g (suc n) a))))) k i })
          (inS (∂filler0' n a j i))

  step1 : (n : ℕ) → (x : QuotCW pushoutSkel (suc (suc n))) → Susp (Bob n)
  step1 n (inl x) = north
  step1 n (inr x) = step1-cod n x
  step1 n (push (inl c) i) = merid (inl (inr c)) i
  step1 n (push (inr d) i) = merid (inr (inr d)) i
  step1 n (push (push a i) j) = step1-filler n a i j i1

  -- proof that ∂Bob' ∘ Pn+1/Pn→Bob' ≡ step1
  prefiller3 : (n : ℕ) (b : QuotCW B (suc n)) → I → I → I → Susp (Bob n)
  prefiller3 n b i j =
    hfill (λ k → λ { (i = i0) → ∂middle' n (doubleCompPath-filler refl (merid b) (sym (merid (inl tt))) k j)
                   ; (i = i1) → ∂middle-aux' n b j
                   ; (j = i0) → north
                   ; (j = i1) → filler2 n i (~ k) })
          (inS (∂middle-aux' n b j))

  filler3 : (n : ℕ) (b : QuotCW B (suc n))
          → Square {A = Susp (Bob n)} (λ i → ∂middle' n (toSusp (QuotCW∙ B (suc n)) b i)) (∂middle-aux' n b) (λ i → north) (λ i → north)
  filler3 n b i j = prefiller3 n b i j i1

  filler4 : (n : ℕ) (a : B .fst (suc n))
    → Cube {A = Susp (Bob n)}
           (λ i j → ∂Bob' n (inm (filler0 (suc n) a i j)))
           (λ i j → ∂filler0' n a i j) (λ i j → north)
           (λ i j → filler3 n (inr (inl a)) i j) (λ i j → north) (λ i j → north)
  filler4 n a i j k =
    hcomp (λ l → λ { (i = i0) → ∂Bob' n (inm (prefiller0 (suc n) a j k l))
                   ; (i = i1) → pre∂filler0' n a j k l
                   ; (j = i0) → hcomp (λ j → λ { (i = i0) → filler2 n (~ j) (k ∧ ~ l)
                                               ; (i = i1) → filler2 n ((~ j) ∨ l) k
                                               ; (k = i0) → north
                                               ; (k = i1) → filler2 n (i ∨ (~ j)) (~ l)
                                               ; (l = i0) → filler2 n (~ j) k
                                               ; (l = i1) → north })
                                      north
                   ; (j = i1) → prefiller3 n (inr (inl a)) i k l
                   ; (k = i0) → north
                   ; (k = i1) → filler2 n i (~ l) })
          (∂middle-aux' n (push a j) k)

  filler5-l : (n : ℕ) (a : C .fst (suc (suc n))) →
    Square {A = Susp (Bob n)} (λ i → ∂Bob' n ((sym pushₗ ∙ λ i → inl (push a i)) i))
           (merid (inl (inr a))) (λ _ → north) (λ _ → south)
  filler5-l n a i j =
    hcomp (λ k → λ { (i = i0) → ∂Bob' n (doubleCompPath-filler refl (sym pushₗ) (λ i → inl (push a i)) k j)
                   ; (i = i1) → merid (inl (inr a)) j
                   ; (j = i0) → north
                   ; (j = i1) → merid (inl (inr a)) (k ∨ i) })
          (merid (inl (inr a)) (i ∧ j))

  filler5-r : (n : ℕ) (a : D .fst (suc (suc n))) →
    Square {A = Susp (Bob n)} (λ i → ∂Bob' n ((sym pushᵣ ∙ λ i → inr (push a i)) i))
           (merid (inr (inr a))) (λ _ → north) (λ _ → south)
  filler5-r n a i j =
    hcomp (λ k → λ { (i = i0) → ∂Bob' n (doubleCompPath-filler refl (sym pushᵣ) (λ i → inr (push a i)) k j)
                   ; (i = i1) → merid (inr (inr a)) j
                   ; (j = i0) → north
                   ; (j = i1) → merid (inr (inr a)) (k ∨ i) })
          (merid (inr (inr a)) (i ∧ j))

  step1-cod-eq : (n : ℕ) → (x : (fst pushoutSkel (suc (suc (suc n))))) → ∂Bob' n (pushoutA→Bob (suc n) x) ≡ step1-cod n x
  step1-cod-eq n (inl x) = refl
  step1-cod-eq n (inr x) = refl
  step1-cod-eq n (push a i) j =
    hcomp (λ k → λ { (i = i0) → filler5-l n (seqMap f (suc (suc n)) a) j k
                   ; (i = i1) → filler5-r n (seqMap g (suc (suc n)) a) j k
                   ; (j = i0) → ∂Bob' n (doubleCompPath-filler (sym (sym pushₗ ∙ λ i → inl (push (seqMap f (suc (suc n)) a) i)))
                                                               (λ i → inm (toSusp (QuotCW∙ B (suc n)) (inr a) i))
                                                               (sym pushᵣ ∙ (λ i → inr (push (seqMap g (suc (suc n)) a) i))) k i)
                   ; (j = i1) → doubleCompPath-filler (sym (merid (inl (inr (seqMap f (suc (suc n)) a)))))
                                                      (∂middle-aux' n (inr a))
                                                      (merid (inr (inr (seqMap g (suc (suc n)) a)))) k i })
          (filler3 n (inr a) j i)

  step1-eq : (n : ℕ) → (x : QuotCW pushoutSkel (suc (suc n))) → ∂Bob' n (Pn+1/Pn→Bob' (suc n) x) ≡ step1 n x
  step1-eq n (inl x) = refl
  step1-eq n (inr x) = step1-cod-eq n x
  step1-eq n (push (inl x) i) j = filler5-l n x j i
  step1-eq n (push (inr x) i) j = filler5-r n x j i
  step1-eq n (push (push a i) j) k =
    hcomp (λ l → λ { (i = i0) → filler5-l n (inl (seqMap f (suc n) a)) k (l ∧ j)
                   ; (i = i1) → filler5-r n (inl (seqMap g (suc n) a)) k (l ∧ j)
                   ; (j = i0) → north
                   ; (k = i0) → ∂Bob' n (subpushout→Bob'-filler (suc n) a i (~ j) l)
                   ; (k = i1) → step1-filler n a i j l })
          (filler4 n a k j i)

  -- further simplifying step1...
  -- step2-cod : (n : ℕ) → (fst pushoutSkel (suc (suc (suc n)))) → Susp (Bob n)
  -- step2-cod n (inl x) = south
  -- step2-cod n (inr x) = south
  -- step2-cod n (push a i) =
  --   (refl
  --   ∙∙ sym (merid (inm (suspFun (to_cofibCW n B) (δ (suc n) B (inr a)))))
  --   ∙∙ merid (inm north)) i

  -- step2-filler : (n : ℕ) → (a : B .fst (suc n)) → I → I → I → Susp (Bob n)
  -- step2-filler n a i j =
  --   hfill (λ k → λ { (i = i0) → ? --merid (inl (inr (inl (seqMap f (suc n) a)))) (k ∧ j)
  --                  ; (i = i1) → ? --merid (inr (inr (inl (seqMap g (suc n) a)))) (k ∧ j)
  --                  ; (j = i0) → north
  --                  ; (j = i1) → doubleCompPath-filler (sym (merid (inl (inr (inl (seqMap f (suc n) a))))))
  --                                                     (∂middle-aux' n (inr (inl a)))
  --                                                     (merid (inr (inr (inl (seqMap g (suc n) a))))) k i })
  --         (inS (∂filler0' n a j i))

  -- step2 : (n : ℕ) → (x : QuotCW pushoutSkel (suc (suc n))) → Susp (Bob n)
  -- step2 n (inl x) = north
  -- step2 n (inr x) = step2-cod n x
  -- step2 n (push (inl c) i) = merid (inl (inr c)) i
  -- step2 n (push (inr d) i) = merid (inr (inr d)) i
  -- step2 n (push (push a i) j) = step2-filler n a i j i1



  -- ∂Bob (inl (push (seqMap f (suc (suc n)) a) i))
  --   = merid (inl inr (seqMap f (suc (suc n)) a)) i

  -- step1 : (n : ℕ) → (x : QuotCW pushoutSkel (suc (suc n))) → Susp (Bob n)
  -- step1 n (inl x) = north
  -- step1 n (inr (inl x)) = south
  -- step1 n (inr (inr x)) = south
  -- step1 n (inr (push a i)) = (sym (merid (inm south)) ∙∙ refl ∙∙ merid (inm north)) i
  -- step1 n (push (inl c) i) = merid (inl (inr c)) i
  -- step1 n (push (inr d) i) = merid (inr (inr d)) i
  -- step1 n (push (push a i) j) =
  --   hcomp (λ k → λ { (i = i0) → merid (inl (push (seqMap f (suc n) a) k)) j
  --                  ; (i = i1) → merid (inr (push (seqMap g (suc n) a) k)) j
  --                  ; (j = i0) → north
  --                  ; (j = i1) → (sym (merid (inm south)) ∙∙ refl ∙∙ merid (inm north)) i })
  --         (hcomp (λ k → λ { (i = i0) → merid (pushₗ (~ k)) j
  --                         ; (i = i1) → merid (pushᵣ (~ k)) j
  --                         ; (j = i0) → north
  --                         ; (j = i1) → (sym (merid (inm (merid (inr a) k))) ∙∙ refl ∙∙ merid (inm north)) i })
  --                (doubleCompPath-filler (sym (merid (inm north))) refl (merid (inm north)) j i) )

  -- step1-eq : (n : ℕ) (x : QuotCW pushoutSkel (suc (suc n))) → ∂Bob' n (Pn+1/Pn→Bob (suc n) x) ≡ step1 n x
  -- step1-eq n x = {!!}
  -- step1-eq n (inr (push a i)) j =
  --   hcomp (λ k → λ { (i = i0) → {!!}
  --                  ; (i = i1) → {!!}
  --                  ; (j = i0) → ∂Bob' n (doubleCompPath-filler (sym (sym pushₗ ∙ λ i → inl (push (seqMap f (suc (suc n)) a) i)))
  --                                                              (λ i → inm (toSusp (QuotCW∙ B (suc n)) (inr a) i))
  --                                                              (sym pushᵣ ∙ (λ i → inr (push (seqMap g (suc (suc n)) a) i))) k i)
  --                  ; (j = i1) → {!!} })
  --         {!!}

  -- step2-eq : (n : ℕ) (x : QuotCW pushoutSkel (suc (suc n)))
  --   → step1 n x ≡ (suspFun (Pn+1/Pn→Bob n) ∘ suspFun (to_cofibCW (suc n) pushoutSkel) ∘ δ (suc (suc n)) pushoutSkel) x
  -- step2-eq n (inl x) = refl
  -- step2-eq n (inr (inl x)) = refl
  -- step2-eq n (inr (inr x)) = refl
  -- step2-eq n (inr (push a i)) j =
  --   hcomp (λ k → λ { (i = i0) → merid (inm north) ((~ j) ∨ k)
  --                  ; (i = i1) → merid (inm north) ((~ j) ∨ k)
  --                  ; (j = i0) → (sym (merid (inm (merid (inl tt) k))) ∙∙ refl ∙∙ merid (inm north)) i
  --                  ; (j = i1) → merid (inm north) k })
  --         (doubleCompPath-filler (sym (merid (inm north))) refl (merid (inm north)) (~ j) (~ i))
  -- step2-eq n (push (inl x) i) = refl
  -- step2-eq n (push (inr x) i) = refl
  -- step2-eq n (push (push a i) j) k = {!!}

  -- easyHomotopy : (n : ℕ) → (x : QuotCW pushoutSkel (suc (suc n)))
  --   → ∂Bob' n (Pn+1/Pn→Bob (suc n) x) ≡ (suspFun (Pn+1/Pn→Bob n) ∘ suspFun (to_cofibCW (suc n) pushoutSkel) ∘ δ (suc (suc n)) pushoutSkel) x
  -- easyHomotopy n x = {!!} --step1-eq n x ∙ step2-eq n x


  -- pre∂filler0' : (n : ℕ) (a : B .fst (suc n)) → I → I → I → Susp (Bob n)
  -- pre∂filler0' n a i j =
  --   hfill (λ k → λ { (i = i0) → {!rCancel (sym (merid (inm north))) (j) (~ k)!}
  --                  ; (i = i1) → doubleCompPath-filler (merid (inl (fn+1/fn (suc n) (inr (inl a)))))
  --                                                     (sym (merid (inm south)) ∙ merid (inm north))
  --                                                     (sym (merid (inr (gn+1/gn (suc n) (inr (inl a)))))) k j
  --                  ; (j = i0) → merid (inl ((fn+1/fn (suc n) (push a i)))) (~ k)
  --                  ; (j = i1) → merid (inr ((gn+1/gn (suc n) (push a i)))) (~ k) })
  --         (inS ((sym (merid (inm (suspFun (to_cofibCW n B) (δ (suc n) B (push a i))))) ∙ merid (inm north)) j))

  -- ∂filler0' : (n : ℕ) (a : B .fst (suc n))
  --   → Square {A = Susp (Bob n)} (λ i → north) (∂middle-aux' n (inr (inl a))) (λ i → north) (λ i → north)
  -- ∂filler0' n a i j = pre∂filler0' n a i j i1
