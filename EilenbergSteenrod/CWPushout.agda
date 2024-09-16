{-# OPTIONS --cubical #-}
module EilenbergSteenrod.CWPushout where

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

IsoSphereSusp : (n : ℕ) → Iso (S₊ n) (Susp (S⁻ n))
IsoSphereSusp zero = BoolIsoSusp⊥
IsoSphereSusp (suc n) = IsoSucSphereSusp n

finSplit3 : ∀ n m l → Fin (n +ℕ m +ℕ l) → ((Fin n) ⊎ (Fin m)) ⊎ (Fin l)
finSplit3 = {!!}

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

module _ (ℓ : Level) (B C D : CWskel ℓ)
  (f : cellMap B C)
  (g : cellMap B D) where

  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)

  2+ : ℕ → ℕ
  2+ n = suc (suc n)

  -- α' : (X : CWskel ℓ) → (n : ℕ) →

  strictA : CWskel ℓ → ℕ → Type ℓ
  strictA X zero = X .fst zero
  strictA X (suc n) = Pushout (α X n) fst

  strict²A : CWskel ℓ → ℕ → Type ℓ
  strict²A X zero = X .fst zero
  strict²A X (suc zero) = strictA X 1
  strict²A X (suc (suc n)) = Pushout (λ (a , x) → e X n .fst (α X (suc n) (a , Iso.inv (IsoSphereSusp n) x))) fst

  strictMap : {X Y : CWskel ℓ} (f : cellMap X Y) → (n : ℕ) → strictA X n → strictA Y n
  strictMap {X} {Y} f zero = ∣ f ∣ zero
  strictMap {X} {Y} f (suc n) (inl x) = inl (∣ f ∣ n x)
  strictMap {X} {Y} f (suc n) (inr x) = e Y n .fst (∣ f ∣ (suc n) (invEq (e X n) (inr x)))
  strictMap {X} {Y} f (suc n) (push a i) =
    ((λ i → secEq (e Y n) (inl (∣ f ∣ n (α X n a))) (~ i))
    ∙∙ (λ i → e Y n .fst (f .comm n (α X n a) i))
    ∙∙ (λ i → e Y n .fst (∣ f ∣ (suc n) (invEq (e X n) (push a i))))) i

  strictPushout : (n : ℕ) → Type ℓ
  strictPushout n = (Pushout {A = strictA B (suc n)} {B = strict²A C (2+ n)} {C = strict²A D (2+ n)}
                             (inl ∘ strictMap {B} {C} f (suc n)) (inl ∘ strictMap {B} {D} g (suc n)))

  pushoutA : ℕ → Type ℓ
  pushoutA zero = B .fst zero
  pushoutA (suc n) = Pushout {A = B .fst n} {B = strictA C (suc n)} {C = strictA D (suc n)} (inl ∘ ∣ f ∣ n) (inl ∘ ∣ g ∣ n)

  pushoutCells : ℕ → ℕ
  pushoutCells zero = (card C zero) +ℕ (card D zero)
  pushoutCells (suc n) = (card C (suc n)) +ℕ (card B n) +ℕ (card D (suc n))

  pushoutMap₀ : (Fin (pushoutCells zero)) × (S⁻ 0) → pushoutA 0
  pushoutMap₀ ()

  pushoutMapₛ : (n : ℕ) → (((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n))) × (Susp (S⁻ n)) → pushoutA (suc n)
  pushoutMapₛ n (inl (inl c) , x) = inl (e C n .fst (α C (suc n) (c ,  Iso.inv (IsoSphereSusp n) x)))
  pushoutMapₛ n (inl (inr b) , north) = inl (strictMap {B} {C} f (suc n) (inr b))
  pushoutMapₛ n (inl (inr b) , south) = inr (strictMap {B} {D} g (suc n) (inr b))
  pushoutMapₛ n (inl (inr b) , merid x i) =
    ((λ i → inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i))))
    ∙∙ (push (α B n (b , x)))
    ∙∙ (λ i → inr (strictMap {B} {D} g (suc n) (push (b , x) i)))) i
  pushoutMapₛ n (inr d , x) = inr (e D n .fst (α D (suc n) (d ,  Iso.inv (IsoSphereSusp n) x )))

  pushoutMap : (n : ℕ) → (Fin (pushoutCells n)) × (S⁻ n) → pushoutA n
  pushoutMap zero = pushoutMap₀
  pushoutMap (suc n) (a , x) = pushoutMapₛ n (finSplit3 (card C (suc n)) (card B n) (card D (suc n)) a
                                                   , Iso.fun (IsoSphereSusp n) x)

  pushoutIsoₛ-filler0 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → pushoutA (suc n)
  pushoutIsoₛ-filler0 n b x i j = (doubleCompPath-filler (λ i → inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i))))
                                                         (push (α B n (b , x)))
                                                         (λ i → inr (strictMap {B} {D} g (suc n) (push (b , x) i))) i j)

  pushoutIsoₛ-filler1 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → I → (Pushout (pushoutMapₛ n) fst)
  pushoutIsoₛ-filler1 n b x i j k =
    hfill (λ k → λ { (i = i0) → invSides-hfill2 (push (inl (inr b) , north))
                                                (λ i → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i))))) (~ j) (~ k) i1
                   ; (i = i1) → invSides-hfill2 (push (inl (inr b) , south))
                                                (λ i → inl (inr (strictMap {B} {D} g (suc n) (push (b , x) (~ i))))) (~ j) (~ k) i1
                   ; (j = i0) → inl (pushoutIsoₛ-filler0 n b x (~ k) i)
                   ; (j = i1) → doubleCompPath-filler (push (inl (inr b) , north))
                                                      (λ _ → inr (inl (inr b)))
                                                      (λ i → push (inl (inr b) , south) (~ i)) k i })
          (inS (push (inl (inr b) , merid x i) j)) k

  pushoutIsoₛ-fun : (n : ℕ) → strictPushout n → (Pushout (pushoutMapₛ n) fst)
  pushoutIsoₛ-fun n (inl (inl c)) = inl (inl c)
  pushoutIsoₛ-fun n (inl (inr c)) = inr (inl (inl c))
  pushoutIsoₛ-fun n (inl (push (c , x) i)) = push (inl (inl c) , x) i
  pushoutIsoₛ-fun n (inr (inl d)) = inl (inr d)
  pushoutIsoₛ-fun n (inr (inr d)) = inr (inr d)
  pushoutIsoₛ-fun n (inr (push (d , x) i)) = push (inr d , x) i
  pushoutIsoₛ-fun n (push (inl b) i) = inl (push b i)
  pushoutIsoₛ-fun n (push (inr b) i) = (push (inl (inr b) , north) ∙∙ refl ∙∙ (λ i → push (inl (inr b) , south) (~ i))) i
  pushoutIsoₛ-fun n (push (push (b , x) j) i) = pushoutIsoₛ-filler1 n b x i j i1

  pushoutIsoₛ-inv↪ : (n : ℕ) → pushoutA (suc n) → strictPushout n
  pushoutIsoₛ-inv↪ n (inl c) = inl (inl c)
  pushoutIsoₛ-inv↪ n (inr d) = inr (inl d)
  pushoutIsoₛ-inv↪ n (push b i) = push (inl b) i

  pushoutIsoₛ-filler2 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → I → strictPushout n
  pushoutIsoₛ-filler2 n b x i j k =
    hfill (λ k → λ { (i = i0) → pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x k j)
                   ; (i = i1) → push (inr b) ((~ k) ∧ j)
                   ; (j = i0) → invSides-hfill1 (λ i → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i)))))
                                                (λ _ → push (inr b) i0) i (~ k) i1
                   ; (j = i1) → invSides-hfill1 (λ i → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) (~ i)))))
                                                (λ i → push (inr b) (~ i)) i (~ k) i1 })
          (inS (push (push (b , x) i) j)) k

  pushoutIsoₛ-inv : (n : ℕ) → (Pushout (pushoutMapₛ n) fst) → strictPushout n
  pushoutIsoₛ-inv n (inl x) = pushoutIsoₛ-inv↪ n x
  pushoutIsoₛ-inv n (inr (inl (inl c))) = inl (inr c)
  pushoutIsoₛ-inv n (inr (inl (inr b))) = push (inr b) i0 --inl (inl (strictMap {B} {C} f (suc n) (inr b)))
  pushoutIsoₛ-inv n (inr (inr d)) = inr (inr d)
  pushoutIsoₛ-inv n (push (inl (inl c) , x) i) = inl (push (c , x) i)
  pushoutIsoₛ-inv n (push (inl (inr b) , north) i) = push (inr b) i0 --inl (inl (strictMap {B} {C} f (suc n) (inr b)))
  pushoutIsoₛ-inv n (push (inl (inr b) , south) i) = push (inr b) (~ i)
  pushoutIsoₛ-inv n (push (inl (inr b) , merid x j) i) = pushoutIsoₛ-filler2 n b x i j i1
  pushoutIsoₛ-inv n (push (inr d , x) i) = inr (push (d , x) i)

  pushoutIsoₛ-rightInv : (n : ℕ) → (x : Pushout (pushoutMapₛ n) fst) → pushoutIsoₛ-fun n (pushoutIsoₛ-inv n x) ≡ x
  pushoutIsoₛ-rightInv n (inl (inl c)) = refl
  pushoutIsoₛ-rightInv n (inl (inr d)) = refl
  pushoutIsoₛ-rightInv n (inl (push b i)) = refl
  pushoutIsoₛ-rightInv n (inr (inl (inl c))) = refl
  pushoutIsoₛ-rightInv n (inr (inl (inr b))) = push (inl (inr b) , north)
  pushoutIsoₛ-rightInv n (inr (inr d)) = refl
  pushoutIsoₛ-rightInv n (push (inl (inl c) , x) i) = refl
  pushoutIsoₛ-rightInv n (push (inl (inr b) , north) i) j = push (inl (inr b) , north) (i ∧ j)
  pushoutIsoₛ-rightInv n (push (inl (inr b) , south) i) j = {!!}
    -- doubleCompPath-filler (push (inl (inr b) , north))
    --                       (λ i → push (inl (inr b) , south) (~ i))
    --                       refl (~ j) (~ i)
  pushoutIsoₛ-rightInv n (push (inl (inr b) , merid x j) i) k =
    hcomp (λ l → λ { (i = i0) → {!!}
                   ; (i = i1) → {!!}
                   ; (j = i0) → {!!} -- standard filler
                   ; (j = i1) → {!!} -- complicated filler
                   ; (k = i0) → pushoutIsoₛ-fun n (pushoutIsoₛ-filler2 n b x i j l)
                   ; (k = i1) → push (inl (inr b) , merid x j) i })
          (pushoutIsoₛ-filler1 n b x j i (~ k))
  pushoutIsoₛ-rightInv n (push (inr d , x) i) = refl


  pushoutIsoₛ-leftInv : (n : ℕ) → (x : strictPushout n) → pushoutIsoₛ-inv n (pushoutIsoₛ-fun n x) ≡ x
  pushoutIsoₛ-leftInv n (inl (inl c)) = refl
  pushoutIsoₛ-leftInv n (inl (inr c)) = refl
  pushoutIsoₛ-leftInv n (inl (push (c , x) i)) = refl
  pushoutIsoₛ-leftInv n (inr (inl d)) = refl
  pushoutIsoₛ-leftInv n (inr (inr d)) = refl
  pushoutIsoₛ-leftInv n (inr (push (d , x) i)) = refl
  pushoutIsoₛ-leftInv n (push (inl b) i) = refl
  pushoutIsoₛ-leftInv n (push (inr b) i) k =
    hcomp (λ j → λ { (i = i0) → inl (inl (strictMap {B} {C} f (suc n) (inr b)))
                   ; (i = i1) → push (inr b) (k ∨ j)
                   ; (k = i0) → pushoutIsoₛ-inv n (doubleCompPath-filler (push (inl (inr b) , north)) refl
                                                                         (λ i → push (inl (inr b) , south) (~ i)) j i)
                   ; (k = i1) → push (inr b) i })
          (push (inr b) (i ∧ k))
  pushoutIsoₛ-leftInv n (push (push (b , x) j) i) k =
    hcomp (λ l → λ { (i = i0) → hcomp (λ i → λ { (j = i0) → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) ((~ l) ∧ (~ k)))))
                                               ; (j = i1) → inl (inl (e C n .fst (∣ f ∣ (suc n) (invEq (e B n) (inr b)))))
                                               ; (k = i0) → pushoutIsoₛ-inv n (invSides-hfill2 (push (inl (inr b) , north))
                                                                              (λ i → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i)))))
                                                                              (~ j) (~ l) i)
                                               ; (k = i1) → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) j)))
                                               ; (l = i0) → invSides-hfill1 (λ i → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (~ i)))))
                                                                            (λ _ → push (inr b) i0) (~ k) (~ j) i
                                               ; (l = i1) → inl (inl (strictMap {B} {C} f (suc n) (push (b , x) j))) })
                                      (inl (inl (strictMap {B} {C} f (suc n) (push (b , x) (((~ k) ∧ (~ l)) ∨ j)))))
                   ; (i = i1) → hcomp (λ i → λ { (j = i0) → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) ((~ l) ∧ (~ k)))))
                                               ; (j = i1) → push (inr b) (k ∨ ~ i ∨ l)
                                               ; (k = i0) → pushoutIsoₛ-inv n (invSides-hfill2 (push (inl (inr b) , south))
                                                                              (λ i → inl (inr (strictMap {B} {D} g (suc n) (push (b , x) (~ i)))))
                                                                              (~ j) (~ l) i)
                                               ; (k = i1) → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) j)))
                                               ; (l = i0) → invSides-hfill1 (λ i → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) (~ i)))))
                                                                            (λ i → push (inr b) (~ i)) (~ k) (~ j) i
                                               ; (l = i1) → inr (inl (strictMap {B} {D} g (suc n) (push (b , x) j))) })
                                      (inr (inl (strictMap {B} {D} g (suc n) (push (b , x) (((~ k) ∧ (~ l)) ∨ j)))))
                   ; (j = i0) → pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x ((~ k) ∧ (~ l)) i)
                   ; (j = i1) → hfill (λ j → λ { (i = i0) → inl (inl (strictMap {B} {C} f (suc n) (inr b)))
                                               ; (i = i1) → push (inr b) (k ∨ j)
                                               ; (k = i0) → pushoutIsoₛ-inv n (doubleCompPath-filler (push (inl (inr b) , north)) refl (λ i → push (inl (inr b) , south) (~ i)) j i)
                                               ; (k = i1) → push (inr b) i })
                                      (inS (push (inr b) (i ∧ k))) l
                   ; (k = i0) → pushoutIsoₛ-inv n (pushoutIsoₛ-filler1 n b x i j l)
                   ; (k = i1) → push (push (b , x) j) i })
          (pushoutIsoₛ-filler2 n b x j i (~ k))

  pushoutIsoₛ : (n : ℕ) → Iso (strictPushout n) (Pushout (pushoutMapₛ n) fst)
  pushoutIsoₛ n = iso (pushoutIsoₛ-fun n) (pushoutIsoₛ-inv n) (pushoutIsoₛ-rightInv n) (pushoutIsoₛ-leftInv n)

  pushoutSkel : CWskel ℓ
  pushoutSkel = pushoutA , (pushoutCells , pushoutMap , (B .snd .snd .snd .fst) , {!!})
