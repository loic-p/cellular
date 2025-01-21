{-# OPTIONS --cubical #-}
module Pushout.LoicPushout where

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


open import Pushout.WithSpheres

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

module Pash (ℓ : Level) (B' C' D' : CWskel ℓ)
  (f : cellMap (strictCWskel B') (strictCWskel C'))
  (g : cellMap (strictCWskel B') (strictCWskel D')) where
  private
    B = strictCWskel B'
    C = strictCWskel C'
    D = strictCWskel D'


-- module Pash (ℓ : Level) (B C D : CWskel ℓ)
--   (f : cellMap B C)
--   (g : cellMap B D) where

  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)

  2+ : ℕ → ℕ
  2+ n = suc (suc n)

  -- α' : (X : CWskel ℓ) → (n : ℕ) →

  strict²A : CWskel ℓ → ℕ → Type ℓ
  strict²A X zero = X .fst zero
  strict²A X (suc zero) = strictCWskel X .fst 1
  strict²A X (suc (suc n)) = Pushout (λ ax → (α (strictCWskel X) (suc n) (fst ax , Iso.inv (IsoSphereSusp n) (snd ax)))) fst

  strictMap : {X Y : CWskel ℓ} (f : cellMap (strictCWskel X) (strictCWskel Y)) → (n : ℕ) → strictCWskel X .fst n → strictCWskel Y .fst n
  strictMap {X} {Y} f zero = ∣ f ∣ zero
  strictMap {X} {Y} f (suc n) (inl x) = inl (∣ f ∣ n x)
  strictMap {X} {Y} f (suc n) (inr x) = ∣ f ∣ (suc n) (inr x)
  strictMap {X} {Y} f (suc n) (push a i) =
    (f .comm n (α (strictCWskel X) n a)
    ∙ cong (∣ f  ∣ (suc n)) (push a)) i

  strictMapStrict : {X Y : CWskel ℓ} (f : cellMap (strictCWskel X) (strictCWskel Y))
    → (n : ℕ) (x : _)
      → strictMap {X = X} {Y} f (suc n) x
         ≡ ∣ f ∣ (suc n) x
  strictMapStrict f n (inl x) = comm f n x
  strictMapStrict f n (inr x) = refl
  strictMapStrict {X = X} f n (push a i) j =
    compPath-filler' (comm f n (α (strictCWskel X) n a)) (cong (∣ f ∣ (suc n)) (push a)) (~ j) i

  strictPushout : (n : ℕ) → Type ℓ
  strictPushout n = (Pushout {A = fst B (suc n)} {B = strict²A C' (2+ n)} {C = strict²A D' (2+ n)}
                             (inl ∘ strictMap {B'} {C'} f (suc n)) (inl ∘ strictMap {B'} {D'} g (suc n)))

  pushoutA' : ℕ → Type ℓ
  pushoutA' zero = B .fst zero
  pushoutA' (suc n) = Pushout {A = B .fst n} {B = fst C (suc n)} {C = fst D (suc n)} (inl ∘ ∣ f ∣ n) (inl ∘ ∣ g ∣ n)

  pushoutCells' : ℕ → ℕ
  pushoutCells' zero = (card C zero) +ℕ (card D zero)
  pushoutCells' (suc n) = (card C (suc n)) +ℕ (card B n) +ℕ (card D (suc n))

  pushoutMap₀' : (Fin (pushoutCells' zero)) × (S⁻ 0) → pushoutA' 0
  pushoutMap₀' ()

  pushoutMapₛ' : (n : ℕ) → (((A C (suc n)) ⊎ (A B n)) ⊎ (A D (suc n))) × (Susp (S⁻ n)) → pushoutA' (suc n)
  pushoutMapₛ' n (inl (inl c) , x) = inl (e C n .fst (α C (suc n) (c ,  Iso.inv (IsoSphereSusp n) x)))
  pushoutMapₛ' n (inl (inr b) , north) = inl (strictMap {B'} {C'} f (suc n) (inr b))
  pushoutMapₛ' n (inl (inr b) , south) = inr (strictMap {B'} {D'} g (suc n) (inr b))
  pushoutMapₛ' n (inl (inr b) , merid x i) = --pushoutIsoₛ-filler0 n b x i1 i
    ((λ i → inl (strictMap {B'} {C'} f (suc n) (push (b , x) (~ i))))
    ∙∙ (push (α B n (b , x)))
    ∙∙ (λ i → inr (strictMap {B'} {D'} g (suc n) (push (b , x) i)))) i
  pushoutMapₛ' n (inr d , x) = inr (e D n .fst (α D (suc n) (d ,  Iso.inv (IsoSphereSusp n) x )))

  pushoutMapMain : (n : ℕ) → (Fin (pushoutCells' n)) × (S⁻ n) → pushoutA' n
  pushoutMapMain zero = pushoutMap₀'
  pushoutMapMain (suc n) (a , x) = pushoutMapₛ' n (finSplit3 (card C (suc n)) (card B n) (card D (suc n)) a
                                                   , Iso.fun (IsoSphereSusp n) x)

  pushoutIsoₛ-filler0 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → pushoutA' (suc n)
  pushoutIsoₛ-filler0 n b x i j = (doubleCompPath-filler (λ i → inl (strictMap {B'} {C'} f (suc n) (push (b , x) (~ i))))
                                                         (push (α B n (b , x)))
                                                         (λ i → inr (strictMap {B'} {D'} g (suc n) (push (b , x) i))) i j)

  pushoutIsoₛ-filler1 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → I → (Pushout (pushoutMapₛ' n) fst)
  pushoutIsoₛ-filler1 n b x i j k =
    hfill (λ k → λ { (i = i0) → invSides-hfill2 (push (inl (inr b) , north))
                                                (λ i → inl (inl (strictMap {B'} {C'} f (suc n) (push (b , x) (~ i))))) (~ j) (~ k) i1
                   ; (i = i1) → invSides-hfill2 (push (inl (inr b) , south))
                                                (λ i → inl (inr (strictMap {B'} {D'} g (suc n) (push (b , x) (~ i))))) (~ j) (~ k) i1
                   ; (j = i0) → inl (pushoutIsoₛ-filler0 n b x (~ k) i)
                   ; (j = i1) → doubleCompPath-filler (push (inl (inr b) , north))
                                                      (λ _ → inr (inl (inr b)))
                                                      (λ i → push (inl (inr b) , south) (~ i)) k i })
          (inS (push (inl (inr b) , merid x i) j)) k

  pushoutIsoₛ-inv↪ : (n : ℕ) → pushoutA' (suc n) → strictPushout n
  pushoutIsoₛ-inv↪ n (inl c) = inl (inl c)
  pushoutIsoₛ-inv↪ n (inr d) = inr (inl d)
  pushoutIsoₛ-inv↪ n (push b i) = push (inl b) i

  pushoutIsoₛ-filler2 : (n : ℕ) → (b : A B n) → (x : S⁻ n) → I → I → I → strictPushout n
  pushoutIsoₛ-filler2 n b x i j k =
    hfill (λ k → λ { (i = i0) → pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x k j)
                   ; (i = i1) → push (inr b) ((~ k) ∧ j)
                   ; (j = i0) → invSides-hfill1 (λ i → inl (inl (strictMap {B'} {C'} f (suc n) (push (b , x) (~ i)))))
                                                (λ _ → push (inr b) i0) i (~ k) i1
                   ; (j = i1) → invSides-hfill1 (λ i → inr (inl (strictMap {B'} {D'} g (suc n) (push (b , x) (~ i)))))
                                                (λ i → push (inr b) (~ i)) i (~ k) i1 })
          (inS (push (push (b , x) i) j)) k

  pushoutIsoₛ-filler3 : (n : ℕ) → (b : A B n) → I → I → I → Pushout (pushoutMapₛ' n) fst
  pushoutIsoₛ-filler3 n b j k l =
    hfill (λ l → λ { (j = i0) → push (inl (inr b) , south) i0
                   ; (j = i1) → doubleCompPath-filler (push (inl (inr b) , north))
                                                      (λ _ → inr (inl (inr b)))
                                                      (λ i → push (inl (inr b) , south) (~ i)) (~ k) (~ l)
                   ; (k = i0) → (push (inl (inr b) , north) ∙∙ (λ _ → inr (inl (inr b))) ∙∙ (λ i → push (inl (inr b) , south) (~ i))) (~ l ∨ ~ j)
                   ; (k = i1) → push (inl (inr b) , south) j })
          (inS (push (inl (inr b) , south) (j ∧ k))) l

  pushoutIsoₛ-filler4 : (n : ℕ) → (b : A B n) → I → I → I → Pushout (pushoutMapₛ' n) fst
  pushoutIsoₛ-filler4 n b i k j =
    hfill (λ j → λ { (i = i0) → push (inl (inr b) , south) i0
                   ; (i = i1) → pushoutIsoₛ-filler3 n b j k i1
                   ; (k = i0) → (push (inl (inr b) , north) ∙∙ (λ _ → inr (inl (inr b))) ∙∙ (λ i → push (inl (inr b) , south) (~ i))) (~ i ∨ ~ j)
                   ; (k = i1) → push (inl (inr b) , south) (i ∧ j) })
          (inS (push (inl (inr b) , south) i0)) j

  pushoutIsoₛ-fun : (n : ℕ) → strictPushout n → (Pushout (pushoutMapₛ' n) fst)
  pushoutIsoₛ-fun n (inl (inl c)) = inl (inl c)
  pushoutIsoₛ-fun n (inl (inr c)) = inr (inl (inl c))
  pushoutIsoₛ-fun n (inl (push (c , x) i)) = push (inl (inl c) , x) i
  pushoutIsoₛ-fun n (inr (inl d)) = inl (inr d)
  pushoutIsoₛ-fun n (inr (inr d)) = inr (inr d)
  pushoutIsoₛ-fun n (inr (push (d , x) i)) = push (inr d , x) i
  pushoutIsoₛ-fun n (push (inl b) i) = inl (push b i)
  pushoutIsoₛ-fun n (push (inr b) i) = (push (inl (inr b) , north) ∙∙ refl ∙∙ (λ i → push (inl (inr b) , south) (~ i))) i
  pushoutIsoₛ-fun n (push (push (b , x) j) i) = pushoutIsoₛ-filler1 n b x i j i1

  pushoutIsoₛ-inv : (n : ℕ) → (Pushout (pushoutMapₛ' n) fst) → strictPushout n
  pushoutIsoₛ-inv n (inl x) = pushoutIsoₛ-inv↪ n x
  pushoutIsoₛ-inv n (inr (inl (inl c))) = inl (inr c)
  pushoutIsoₛ-inv n (inr (inl (inr b))) = push (inr b) i0 --inl (inl (strictMap {B'} {C'} f (suc n) (inr b)))
  pushoutIsoₛ-inv n (inr (inr d)) = inr (inr d)
  pushoutIsoₛ-inv n (push (inl (inl c) , x) i) = inl (push (c , x) i)
  pushoutIsoₛ-inv n (push (inl (inr b) , north) i) = push (inr b) i0 --inl (inl (strictMap {B'} {C'} f (suc n) (inr b)))
  pushoutIsoₛ-inv n (push (inl (inr b) , south) i) = push (inr b) (~ i)
  pushoutIsoₛ-inv n (push (inl (inr b) , merid x j) i) = pushoutIsoₛ-filler2 n b x i j i1
  pushoutIsoₛ-inv n (push (inr d , x) i) = inr (push (d , x) i)

  pushoutIsoₛ-rightInv↪ : (n : ℕ) → (x : pushoutA' (suc n)) → pushoutIsoₛ-fun n (pushoutIsoₛ-inv↪ n x) ≡ inl x
  pushoutIsoₛ-rightInv↪ n (inl c) = refl
  pushoutIsoₛ-rightInv↪ n (inr d) = refl
  pushoutIsoₛ-rightInv↪ n (push b i) = refl

  pushoutIsoₛ-rightInv : (n : ℕ) → (x : Pushout (pushoutMapₛ' n) fst) → pushoutIsoₛ-fun n (pushoutIsoₛ-inv n x) ≡ x
  pushoutIsoₛ-rightInv n (inl x) = pushoutIsoₛ-rightInv↪ n x
  pushoutIsoₛ-rightInv n (inr (inl (inl c))) = refl
  pushoutIsoₛ-rightInv n (inr (inl (inr b))) = push (inl (inr b) , north)
  pushoutIsoₛ-rightInv n (inr (inr d)) = refl
  pushoutIsoₛ-rightInv n (push (inl (inl c) , x) i) = refl
  pushoutIsoₛ-rightInv n (push (inl (inr b) , north) i) k = push (inl (inr b) , north) (i ∧ k)
  pushoutIsoₛ-rightInv n (push (inl (inr b) , south) i) k = pushoutIsoₛ-filler4 n b i k i1
  pushoutIsoₛ-rightInv n (push (inl (inr b) , merid x j) i) k =
    hcomp (λ l → λ { (i = i0) → hcomp (λ i → λ { (j = i0) → inl (pushoutIsoₛ-filler0 n b x (i ∧ (k ∨ l)) i0)
                                               ; (j = i1) → inl (pushoutIsoₛ-filler0 n b x (i ∧ (k ∨ l)) i1)
                                               ; (k = i0) → pushoutIsoₛ-fun n (pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x (l ∧ i) j))
                                               ; (k = i1) → pushoutIsoₛ-rightInv↪ n (pushoutIsoₛ-filler0 n b x i j) i1
                                               ; (l = i0) → inl (pushoutIsoₛ-filler0 n b x (i ∧ k) j)
                                               ; (l = i1) → pushoutIsoₛ-rightInv↪ n (pushoutIsoₛ-filler0 n b x i j) k })
                                      (inl (push (α B n (b , x)) j))
                   ; (i = i1) → doubleCompPath-filler (push (inl (inr b) , north))
                                                      (λ _ → inr (inl (inr b)))
                                                      (λ i → push (inl (inr b) , south) (~ i)) (~ k) (~ l ∧ j)
                   ; (j = i0) → hcomp (λ j → λ { (i = i0) → inl (pushoutIsoₛ-filler0 n b x (k ∨ l) i0)
                                               ; (i = i1) → push (inl (inr b) , north) (k ∧ j)
                                               ; (k = i0) → pushoutIsoₛ-fun n (invSides-hfill1
                                                                (λ i → inl (inl (strictMap {B'} {C'} f (suc n) (push (b , x) (~ i)))))
                                                                (λ _ → push (inr b) i0) i (~ l) j)
                                               ; (k = i1) → push (inl (inr b) , north) (i ∧ j) --?
                                               ; (l = i0) → invSides-hfill2 (push (inl (inr b) , north))
                                                                            (λ i → inl (inl (strictMap {B'} {C'} f (suc n) (push (b , x) (~ i)))))
                                                                            (~ i) ( k) j
                                               ; (l = i1) → push (inl (inr b) , north) (i ∧ k ∧ j) })
                                      (inl (pushoutIsoₛ-filler0 n b x (i ∨ k ∨ l) i0))
                   ; (j = i1) → hcomp (λ j → λ { (i = i0) → inl (pushoutIsoₛ-filler0 n b x (k ∨ l) i1)
                                               ; (i = i1) → pushoutIsoₛ-filler3 n b j k l
                                               ; (k = i0) → pushoutIsoₛ-fun n (invSides-hfill1
                                                                (λ i → inr (inl (strictMap {B'} {D'} g (suc n) (push (b , x) (~ i)))))
                                                                (λ i → push (inr b) (~ i)) i (~ l) j)
                                               ; (k = i1) → push (inl (inr b) , south) (i ∧ j)
                                               ; (l = i0) → invSides-hfill2 (push (inl (inr b) , south))
                                                                            (λ i → inl (inr (strictMap {B'} {D'} g (suc n) (push (b , x) (~ i)))))
                                                                            (~ i) ( k) j
                                               ; (l = i1) → pushoutIsoₛ-filler4 n b i k j })
                                      (inl (pushoutIsoₛ-filler0 n b x (i ∨ k ∨ l) i1))
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
    hcomp (λ j → λ { (i = i0) → inl (inl (strictMap {B'} {C'} f (suc n) (inr b)))
                   ; (i = i1) → push (inr b) (k ∨ j)
                   ; (k = i0) → pushoutIsoₛ-inv n (doubleCompPath-filler (push (inl (inr b) , north)) refl
                                                                         (λ i → push (inl (inr b) , south) (~ i)) j i)
                   ; (k = i1) → push (inr b) i })
          (push (inr b) (i ∧ k))
  pushoutIsoₛ-leftInv n (push (push (b , x) j) i) k =
    hcomp (λ l → λ { (i = i0) → hcomp (λ i → λ { (j = i0) → inl (inl (strictMap {B'} {C'} f (suc n) (push (b , x) ((~ l) ∧ (~ k)))))
                                               ; (j = i1) → inl (inl (e C n .fst (∣ f ∣ (suc n) (invEq (e B n) (inr b)))))
                                               ; (k = i0) → pushoutIsoₛ-inv n (invSides-hfill2 (push (inl (inr b) , north))
                                                                              (λ i → inl (inl (strictMap {B'} {C'} f (suc n) (push (b , x) (~ i)))))
                                                                              (~ j) (~ l) i)
                                               ; (k = i1) → inl (inl (strictMap {B'} {C'} f (suc n) (push (b , x) j)))
                                               ; (l = i0) → invSides-hfill1 (λ i → inl (inl (strictMap {B'} {C'} f (suc n) (push (b , x) (~ i)))))
                                                                            (λ _ → push (inr b) i0) (~ k) (~ j) i
                                               ; (l = i1) → inl (inl (strictMap {B'} {C'} f (suc n) (push (b , x) j))) })
                                      (inl (inl (strictMap {B'} {C'} f (suc n) (push (b , x) (((~ k) ∧ (~ l)) ∨ j)))))
                   ; (i = i1) → hcomp (λ i → λ { (j = i0) → inr (inl (strictMap {B'} {D'} g (suc n) (push (b , x) ((~ l) ∧ (~ k)))))
                                               ; (j = i1) → push (inr b) (k ∨ ~ i ∨ l)
                                               ; (k = i0) → pushoutIsoₛ-inv n (invSides-hfill2 (push (inl (inr b) , south))
                                                                              (λ i → inl (inr (strictMap {B'} {D'} g (suc n) (push (b , x) (~ i)))))
                                                                              (~ j) (~ l) i)
                                               ; (k = i1) → inr (inl (strictMap {B'} {D'} g (suc n) (push (b , x) j)))
                                               ; (l = i0) → invSides-hfill1 (λ i → inr (inl (strictMap {B'} {D'} g (suc n) (push (b , x) (~ i)))))
                                                                            (λ i → push (inr b) (~ i)) (~ k) (~ j) i
                                               ; (l = i1) → inr (inl (strictMap {B'} {D'} g (suc n) (push (b , x) j))) })
                                      (inr (inl (strictMap {B'} {D'} g (suc n) (push (b , x) (((~ k) ∧ (~ l)) ∨ j)))))
                   ; (j = i0) → pushoutIsoₛ-inv↪ n (pushoutIsoₛ-filler0 n b x ((~ k) ∧ (~ l)) i)
                   ; (j = i1) → hfill (λ j → λ { (i = i0) → inl (inl (strictMap {B'} {C'} f (suc n) (inr b)))
                                               ; (i = i1) → push (inr b) (k ∨ j)
                                               ; (k = i0) → pushoutIsoₛ-inv n (doubleCompPath-filler (push (inl (inr b) , north)) refl (λ i → push (inl (inr b) , south) (~ i)) j i)
                                               ; (k = i1) → push (inr b) i })
                                      (inS (push (inr b) (i ∧ k))) l
                   ; (k = i0) → pushoutIsoₛ-inv n (pushoutIsoₛ-filler1 n b x i j l)
                   ; (k = i1) → push (push (b , x) j) i })
          (pushoutIsoₛ-filler2 n b x j i (~ k))

  pushoutIsoₛ : (n : ℕ) → Iso (strictPushout n) (Pushout (pushoutMapₛ' n) fst)
  pushoutIsoₛ n = iso (pushoutIsoₛ-fun n) (pushoutIsoₛ-inv n) (pushoutIsoₛ-rightInv n) (pushoutIsoₛ-leftInv n)




module _ (ℓ : Level) (B' C' D' : CWskel ℓ)
  (f : cellMap (strictCWskel B') (strictCWskel C'))
  (g : cellMap (strictCWskel B') (strictCWskel D')) where
  private
    B = strictCWskel B'
    C = strictCWskel C'
    D = strictCWskel D'

  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)

  open Pash ℓ B' C' D' f g

  open import Cubical.Foundations.Equiv.HalfAdjoint
  module _ (E' : CWskel ℓ) (n : ℕ) where
    private
      E = strictCWskel E'

      HA : (n : ℕ) → _ 
      HA n = equiv→HAEquiv (isoToEquiv (IsoSphereSusp n))

      IsoSphereSusp' : (n : ℕ) → Iso _ _
      IsoSphereSusp' n = isHAEquiv→Iso (HA n .snd)

    strict²A→ : (strict²A E' (2+ n)) → (fst E (suc (suc n)))
    strict²A→ (inl x) = inl x
    strict²A→ (inr x) = inr x
    strict²A→ (push a i) = push ((fst a) , Iso.inv (IsoSphereSusp n) (snd a)) i

    strict²A← : (fst E (suc (suc n))) → (strict²A E' (2+ n)) 
    strict²A← (inl x) = inl x
    strict²A← (inr x) = inr x
    strict²A← (push a i) =
      ((λ i → inl (α E  (suc n) (fst a , Iso.leftInv (IsoSphereSusp' n) (snd a) (~ i))))
      ∙ push ((fst a) , Iso.fun (IsoSphereSusp n) (snd a))) i

    strictPushoutIso : Iso (strict²A E' (2+ n))  (fst E (suc (suc n)))
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

      help : Path (Path (strict²A E' (2+ n)) _ _) (cong strict²A← (push (fst a , Iso.inv (IsoSphereSusp n) (snd a)))) (push a) 
      help = (λ i → (λ j → inl (α E (suc n) ((fst a) , PP j i)))
                    ∙ push (fst a , Iso.rightInv (IsoSphereSusp' n) (snd a) i))
           ∙ sym (lUnit _)

  strictPushoutIsoL : (n : ℕ) → Iso  (strict²A C' (2+ n)) (fst C (suc (suc n)))
  strictPushoutIsoL n = strictPushoutIso C' n

  strictPushoutIsoR : (n : ℕ) → Iso  (strict²A D' (2+ n)) (fst D (suc (suc n)))
  strictPushoutIsoR n = strictPushoutIso D' n

  strictMap≡L  : {!!}
  strictMap≡L = {!!}


  pushoutPushoutStrictIso : (n : ℕ) → Iso (strictPushout n) (pushoutA' (suc (suc n))) 
  pushoutPushoutStrictIso n =
    pushoutIso _ _ _ _  (idEquiv _) (isoToEquiv (strictPushoutIsoL n)) (isoToEquiv (strictPushoutIsoR n))
      (funExt λ x i → inl (strictMapStrict f n x i))
      (funExt λ x i → inl (strictMapStrict g n x i))

  pushoutIsoₛMain : (n : ℕ) → Iso (Pushout (pushoutMapₛ' n) fst) (pushoutA' (suc (suc n)))
  pushoutIsoₛMain n = compIso (invIso (pushoutIsoₛ n)) (pushoutPushoutStrictIso n)

  permute⊎Iso1 : (n : ℕ) → ((A C (suc n) ⊎ A D (suc n)) ⊎ A B n) ≃
                            ((A C (suc n) ⊎ A B n) ⊎ A D (suc n))
  permute⊎Iso1 n = 
    (compEquiv ⊎-assoc-≃ (compEquiv (⊎-equiv (idEquiv _) ⊎-swap-≃) (invEquiv ⊎-assoc-≃)))

  permute⊎IsoFull : (n : ℕ) → ((A C (suc n) ⊎ A D (suc n)) ⊎ A B n) × S₊ n ≃
                            ((A C (suc n) ⊎ A B n) ⊎ A D (suc n)) × Susp (S⁻ n)
  permute⊎IsoFull n = Σ-cong-equiv
    (permute⊎Iso1 n)
    λ _ → isoToEquiv (IsoSphereSusp n)

  pushoutAEquiv→ : (n : ℕ) → (pushoutA {B = B} {C = C} {D = D} f g n) → (pushoutA' n)
  pushoutAEquiv→ zero (lift lower₁) = lower₁
  pushoutAEquiv→ (suc n) (inl x) = inl (e C n .fst x)
  pushoutAEquiv→ (suc n) (inr x) = inr (e D n .fst x)
  pushoutAEquiv→ (suc n) (push a i) =
    ((λ i → inl (e C n .fst (comm f n a (~ i))))
    ∙∙ push a
    ∙∙ λ i → inr (e D n .fst (comm g n a i))) i


  pushoutAEquiv← : (n : ℕ) → (pushoutA' n) → (pushoutA {B = B} {C = C} {D = D} f g n)
  pushoutAEquiv← zero lower₁ = lift lower₁
  pushoutAEquiv← (suc n) (inl x) = inl (invEq (e C n) x)
  pushoutAEquiv← (suc n) (inr x) = inr (invEq (e D n) x)
  pushoutAEquiv← (suc n) (push a i) =
    ((λ i → inl (comm f n a i)) ∙∙ push a ∙∙ λ i → inr (comm g n a (~ i)) ) i

  sidefiller : (x : A B 1) (b : Bool) (i j k : I) → pushoutA' 2
  sidefiller x b i j k =
    hfill (λ k → λ {(i = i0) → inl (compPath-filler' (comm f (suc zero) (α B (suc zero) (x , b)))
                                                       (λ i → ∣ f ∣ (suc (suc zero)) (push (x , b) i)) j k)
                   ; (i = i1) → inr (compPath-filler' (comm g (suc zero) (α B (suc zero) (x , b)))
                                                       (λ i → ∣ g ∣ (suc (suc zero)) (push (x , b) i)) j k)
                   ; (j = i0) → pushoutAEquiv→ 2 (pushoutMapₛ-filler {B = B} {C} {D} f g zero x b i k)
                   ; (j = i1) → doubleCompPath-filler
                                  ((λ i → inl ((comm f 1 (α B (suc zero) (x , b))
                                             ∙ (λ i → ∣ f ∣ 2 (push (x , b) i))) (~ i))))
                                   (push (α B (suc zero) (x , b)))
                                  (λ i → inr ((comm g 1 (α B (suc zero) (x , b))
                                             ∙ (λ i → ∣ g ∣ 2 (push (x , b) i))) i)) k i})
           (inS (doubleCompPath-filler (λ i → inl (comm f (suc zero) (α B (suc zero) (x , b)) (~ i)))
                                  (push (α B (suc zero) (x , b)))
                                  (λ i → inr (comm g (suc zero) (α B (suc zero) (x , b)) i)) (~ j) i)) k

  pushoutEquivComm : (n : ℕ) → (x : ((A C (suc (suc n)) ⊎ A D (suc (suc n))) ⊎ A B (suc n)) × S₊ (suc n)) →
                                 (pushoutAEquiv→ (suc (suc n))  ∘ pushoutMapₛ {B = B} {C} {D} f g (suc n)) x ≡
                                 (pushoutMapₛ' (suc n) ∘ fst (permute⊎IsoFull (suc n))) x
  pushoutEquivComm n (inl (inl x) , y) i =
    inl (fst (e C (suc n)) (α C (suc (suc n)) (x , Iso.leftInv (IsoSphereSusp (suc n)) y (~ i))))
  pushoutEquivComm n (inl (inr x) , y) i =
    inr (fst (e D (suc n)) (α D (suc (suc n)) (x , Iso.leftInv (IsoSphereSusp (suc n)) y (~ i))))
  pushoutEquivComm zero (inr x , base) = refl
  pushoutEquivComm zero (inr x , loop i) j =
    hcomp (λ k → λ {(i = i0) → sidefiller x false (~ k) j i1
                  ; (i = i1) → sidefiller x true (~ k) j i1
                  ; (j = i0) → pushoutAEquiv→ 2 (doubleCompPath-filler
                                 (λ i → pushoutMapₛ-filler {B = B} {C} {D} f g zero x false i i1) refl
                                 (λ i → pushoutMapₛ-filler {B = B} {C} {D} f g zero x true (~ i) i1) k i)
                  ; (j = i1) → pushoutMapₛ' (suc zero) (inl (inr x)
                              , compPath-filler'' (merid false) (sym (merid true)) k i)})
          (inr (∣ g ∣ 2 (inr x)))

  pushoutEquivComm (suc n) (inr x , north) = refl
  pushoutEquivComm (suc n) (inr x , south) = refl
  pushoutEquivComm (suc n) (inr x , merid a i) j =
    hcomp (λ k → λ {(i = i0) → {!!}
                  ; (i = i1) → {!!}
                  ; (j = i0) → pushoutAEquiv→ (suc (suc (suc n)))
                                   {!!}
                  ; (j = i1) → {!!}})
            {!!}

  pushoutAEquiv : (n : ℕ) → Iso (pushoutA {B = B} {C = C} {D = D} f g (suc n)) (pushoutA' (suc n))
  Iso.fun (pushoutAEquiv n) = pushoutAEquiv→ (suc n)
  Iso.inv (pushoutAEquiv n) = pushoutAEquiv← (suc n)
  Iso.rightInv (pushoutAEquiv n) x = {!!}
  Iso.leftInv (pushoutAEquiv n) x = {!!}

  -- IsoStrictPushoutA : (n : ℕ) → Iso (strictPushout n) (pushoutA {B = B} {C} {D} f g (suc (suc n)))
  -- IsoStrictPushoutA n = pushoutIso _ _ _ _ (invEquiv (e B n)) {!idEquiv _!} {!!} {!!} {!!}

  btmIso : Iso (Pushout (pushoutMapₛ {B = B} {C = C} {D = D} f g zero) fst)
               (Pushout (pushoutMapₛ' zero) fst)
  Iso.fun btmIso (inl (inl x)) = inl (inl x)
  Iso.fun btmIso (inl (inr x)) = inl (inr x)
  Iso.fun btmIso (inl (push a i)) = {!!}
  Iso.fun btmIso (inr (inl (inl x))) = {!!}
  Iso.fun btmIso (inr (inl (inr x))) = {!!}
  Iso.fun btmIso (inr (inr x)) = {!!}
  Iso.fun btmIso (push (inl a , s) i) = {!!}
  Iso.fun btmIso (push (inr x , s) i) = {!!}
  Iso.inv btmIso x = {!!}
  Iso.rightInv btmIso x = {!!}
  Iso.leftInv btmIso x = {!!}

  iso3 : (n : ℕ) → Iso (Pushout (pushoutMapₛ {B = B} {C = C} {D = D} f g (suc n)) fst)
                                  (Pushout (pushoutMapₛ' (suc n)) fst)
  iso3 n = pushoutIso _ _ _ _ (permute⊎IsoFull (suc n)) (isoToEquiv (pushoutAEquiv (suc n))) (permute⊎Iso1 (suc n))
                              (funExt (pushoutEquivComm n))
                              refl


  iso4 : (n : ℕ) → Iso (Pushout (pushoutMapₛ {B = B} {C = C} {D = D} f g (suc n)) fst) (pushoutA {B = B} {C}{D} f g (suc (suc (suc n))))
  iso4 n = compIso (iso3 n) (compIso (pushoutIsoₛMain (suc n)) (invIso (pushoutAEquiv (suc (suc n)))))

  iso4' : (n : ℕ) → Iso (Pushout (pushoutMapₛ {B = B} {C = C} {D = D} f g (suc n)) fst) _
  iso4' n = compIso (iso3 n) (pushoutIsoₛMain (suc n))

  anotherIsoL'-f : {!!}
  anotherIsoL'-f = {!!}

  anotherIsoL' : (n : ℕ) (r : _)
    → pushoutAEquiv→ (suc (suc (suc n))) (PushoutPushoutMap→PushoutA {B = B} {C} {D} f g (suc n) (inl r))
     ≡ Iso.fun (iso4' n) (inl r)
  anotherIsoL' n (inl x) = refl
  anotherIsoL' n (inr x) = refl
  anotherIsoL' n (push a i) j =
    hcomp (λ k → λ {(i = i0) → inl (inl (comm f (suc n) a (~ j ∨ k)))
                  ; (i = i1) → inr (inl (comm g (suc n) a (~ j ∨ k)))
                  ; (j = i0) → HH k i
                  ; (j = i1) →   (Iso.fun (pushoutPushoutStrictIso (suc n))
                                   (Iso.inv (pushoutIsoₛ (suc n))
                                     (inl (doubleCompPath-filler (λ i → inl ((comm f (suc n) a (~ i))))
                                       (push a)
                                       (λ i → inr ((comm g (suc n) a i))) k i))))})
          (doubleCompPath-filler (λ i₁ → inl (inl (comm f (suc n) a i₁)))
                                 (push (inl a))
                                 (λ i₁ → inr (inl (comm g (suc n) a (~ i₁)))) j i) 
    where
    HH : Square (push (inl a)) (cong (pushoutAEquiv→ (suc (suc (suc n))))
                       (cong (pushoutA↑ {B = B} {C} {D} f g (suc n)) (push a)))
                refl refl
    HH i j = hcomp (λ k → λ {(i = i0) → push (inl a) j
                  ; (i = i1) → pushoutAEquiv→ (suc (suc (suc n)))
                                 (doubleCompPath-filler
                                    (λ i → inl (comm f (suc (suc n)) (inl a) i))
                                    (push (inl a))
                                    (λ i → inr (comm g (suc (suc n)) (inl a) (~ i))) k j)
                  ; (j = i0) → inl (comm f (suc (suc n)) (inl a) (~ k ∧ i))
                  ; (j = i1) → inr (comm g (suc (suc n)) (inl a) (~ k ∧ i))})
             (doubleCompPath-filler
               (λ i → inl (comm f (suc (suc n)) (inl a) (~ i)))
              (push (inl a))
              (λ i → inr (comm g (suc (suc n)) (inl a) i)) i j) 

  anotherIsoR' : (n : ℕ) (r : _)
    → pushoutAEquiv→ (suc (suc (suc n))) (PushoutPushoutMap→PushoutA {B = B} {C} {D} f g (suc n) (inr r))
     ≡ Iso.fun (iso4' n) (inr r)
  anotherIsoR' n (inl (inl x)) = refl
  anotherIsoR' n (inl (inr x)) = refl
  anotherIsoR' n (inr x) = refl

  -- anotherIso' : (n : ℕ) (r : _)
  --   → pushoutAEquiv→ (suc (suc (suc n))) (PushoutPushoutMap→PushoutA {B = B} {C} {D} f g (suc n) r)
  --    ≡ Iso.fun (iso4' n) r
  -- anotherIso' n (inl x) = anotherIsoL' n x
  -- anotherIso' n (inr x) = anotherIsoR' n x
  -- anotherIso' n (push (inl (inl x) , s) i) = {!!}
  -- {- {!Iso.fun (iso4' n) (push (inl (inl x) , s) i) --- cong (Iso.fun (iso4' n)) (push (inl (inl x) , s))!}
  --   where
  --   help : cong (Iso.fun (iso4' n)) (push (inl (inl x) , s))
  --        ≡ (λ i → inl (push (x , s) i)) 
  --   help i j = hcomp (λ k → λ {(i = i0) → {!!}
  --                             ; (i = i1) → {!!}
  --                             ; (j = i0) → {!!}
  --                             ; (j = i1) → {!!}})
  --                    {!!}
  --                    -}
  -- anotherIso' n (push (inl (inr x) , s) i) = {!!}
  -- anotherIso' zero (push (inr x , s) i) = {!!}
  -- anotherIso' (suc n) (push (inr x , s) i) = {!!}
{-
    where
    help : cong (Iso.fun (iso4' n)) (push b)
         ≡ {!!}
         ∙ {!Iso.fun (iso4' n) (inr (fst b))!}
    help = cong-∙∙ (Iso.fun (pushoutIsoₛMain (suc n)))
                (λ i → inl (pushoutEquivComm n b i))
                (push (fst (permute⊎IsoFull (suc n)) b))
                refl
         ∙ sym (compPath≡compPath' _ _)
         ∙ cong₂ _∙_ {!!} {!!}
         ∙ {!cong-∙∙ (Iso.fun (pushoutIsoₛMain (suc n)))
                (λ i → inl (pushoutEquivComm n b i))
                (push (fst (permute⊎IsoFull (suc n)) b))
                refl!} 
-}

  anotherIsoL : (n : ℕ) (r : _)
    → PushoutPushoutMap→PushoutA {B = B} {C} {D} f g (suc n) (inl r)
     ≡ Iso.fun (iso4 n) (inl r)
  anotherIsoL n (inl x) = refl
  anotherIsoL n (inr x) = refl
  anotherIsoL n (push a i) j =
    hcomp (λ k → λ {(i = i0) → {!!}
                  ; (i = i1) → inr {!comm g (suc (suc n)) (CW↪ B (suc n) a) (~ k)!}
                  ; (j = i0) → {!!} -- doubleCompPath-filler (λ i₁ → inl (comm f (suc (suc n)) (CW↪ B (suc n) a) i₁))
                               --    (push (CW↪ B (suc n) a))
                               --    (λ i₁ → inr (comm g (suc (suc n)) (CW↪ B (suc n) a) (~ i₁))) k i
                  ; (j = i1) → pushoutAEquiv← (suc (suc (suc n)))
                                 (Iso.fun (pushoutPushoutStrictIso (suc n))
                                   (Iso.inv (pushoutIsoₛ (suc n))
                                     (inl (doubleCompPath-filler (λ i → inl ((comm f (suc n) a (~ i))))
                                       (push a)
                                       (λ i → inr ((comm g (suc n) a i))) k i))))})
          {!Iso.fun (pushoutPushoutStrictIso (suc n)) (push (inl a) ?)!} 
    where
    he : (x : _) → Iso.fun (iso4 n) (inl x)
                  ≡ pushoutAEquiv← (suc (suc (suc n)))
                     (Iso.fun (pushoutPushoutStrictIso (suc n))
                       (Iso.inv (pushoutIsoₛ (suc n)) (inl (pushoutAEquiv→ (suc (suc n)) x))))
    he x = {!Iso.inv (pushoutIsoₛ (suc n)) (inl (pushoutAEquiv→ (suc (suc n)) (push a i)))!} -- λ x → refl ∙ {!cong (pushoutAEquiv← (suc (suc n))) ?!} ∙ {!!}


  pushoutA↑3 : (n : ℕ) → pushoutA {B = B} {C} {D} f g (suc n) → (pushoutA' (suc (suc n)))
  pushoutA↑3 n (inl x) = inl (CW↪ C (suc n) x)
  pushoutA↑3 n (inr x) = inr (CW↪ D (suc n) x)
  pushoutA↑3 n (push a i) = push (CW↪ B n a) i

  PushoutPushoutMap→PushoutABot3 :
    (n : ℕ) (x : A B n) (s : S₊ n)
    → Path (pushoutA' (suc (suc n))) (pushoutA↑3 n (pushoutMapₛ  {B = B} {C} {D} f g n (inr x , s)))
            (inl (CW↪ C (suc n) ((∣ f ∣ (suc n) (invEq (e B n) (inr x))))))
  PushoutPushoutMap→PushoutABot3 zero x false = refl
  PushoutPushoutMap→PushoutABot3 zero x true = sym (push (inr x))
  PushoutPushoutMap→PushoutABot3 (suc zero) x base = refl
  PushoutPushoutMap→PushoutABot3 (suc zero) x (loop i) j =
    hcomp (λ k → λ {(i = i0) → inl (CW↪ C 2 (∣ f ∣ 2 (invEq (e B 1) (push (x , false) (~ j ∨ k)))))
                  ; (i = i1) → inl (CW↪ C 2 (∣ f ∣ 2 (invEq (e B 1) (push (x , true) (~ j ∨ k)))))
                  ; (j = i0) → pushoutA↑3 (suc zero)
                                    (doubleCompPath-filler (λ i → pushoutMapₛ-filler {B = B} {C} {D} f g zero x false i i1)
                                       refl
                                       (λ i₁ → pushoutMapₛ-filler {B = B} {C} {D} f g zero x true (~ i₁) i1) i1 i)
                  ; (j = i1) → inl (CW↪ C 2 (∣ f ∣ 2 (invEq (e B 1) (compPath-filler'' ((push (x , false))) (sym (push (x , true))) (~ k) i))))})
     (hcomp (λ k → λ {(i = i0) → pushoutA↑3 (suc zero) (pushoutMapₛ-filler {B = B} {C} {D} f g zero x false (~ k) (~ j))
                     ; (i = i1) → pushoutA↑3 (suc zero) (pushoutMapₛ-filler {B = B} {C} {D} f g zero x true (~ k) (~ j))
                  ; (j = i0) → pushoutA↑3 (suc zero) (doubleCompPath-filler (λ i → pushoutMapₛ-filler {B = B} {C} {D} f g zero x false i i1)
                                                         refl
                                                         (λ i₁ → pushoutMapₛ-filler {B = B} {C} {D} f g zero x true (~ i₁) i1) k i)
                  ; (j = i1) → doubleCompPath-filler
                                 (sym (push (inl (α B 1 (x , false)))))
                                 (λ i → inl (CW↪ C 2 (∣ f ∣ 2 (invEq (e B 1)
                                   (compPath-filler'' ((push (x , false))) (sym (push (x , true))) i1 i)))))
                                 (push (inl (α B 1 (x , true)))) (~ k) i})
            {!!})
  PushoutPushoutMap→PushoutABot3 (suc (suc n)) x north = refl
  PushoutPushoutMap→PushoutABot3 (suc (suc n)) x south = sym (push (inr x))
  PushoutPushoutMap→PushoutABot3 (suc (suc n)) x (merid a i) j =
    hcomp (λ k → λ {(i = i0) → inl (inl (∣ f ∣ (suc (suc (suc n))) (push (x , a) k)))
                  ; (i = i1) → push (push (x , a) k) (~ j)
                  ; (j = i0) → pushoutA↑3 (suc (suc n))
                                  (doubleCompPath-filler (λ i → inl (∣ f ∣ (suc (suc (suc n)))
                                                                    (push (x , a) (~ i))))
                                                         (push (α B (suc (suc n)) (x , a)))
                                                         (λ i → inr (∣ g ∣ (suc (suc (suc n)))
                                                                    (push (x , a) i))) k i)
                  ; (j = i1) → inl (inl (∣ f ∣ (suc (suc (suc n))) (push (x , a) k)))})
          (push (inl (α B (suc (suc n)) (x , a))) (~ j ∧ i))


  PushoutPushoutMap→PushoutA3 : (n : ℕ) →  (Pushout (pushoutMapₛ {B = B} {C} {D} f g n) (λ r → fst r)) → (pushoutA' (suc (suc n)))
  PushoutPushoutMap→PushoutA3 n (inl x) = pushoutA↑3 n x
  PushoutPushoutMap→PushoutA3 n (inr (inl (inl x))) = inl (invEq (e C (suc n)) (inr x))
  PushoutPushoutMap→PushoutA3 n (inr (inl (inr x))) = inr (invEq (e D (suc n)) (inr x))
  PushoutPushoutMap→PushoutA3 n (inr (inr x)) = inl (CW↪ C (suc n) ((∣ f ∣ (suc n) (invEq (e B n) (inr x))))) --  
  PushoutPushoutMap→PushoutA3 n (push (inl (inl x) , s) i) = inl (invEq (e C (suc n)) ((push (x , s)) i))
  PushoutPushoutMap→PushoutA3 n (push (inl (inr x) , s) i) = inr (invEq (e D (suc n)) ((push (x , s)) i))
  PushoutPushoutMap→PushoutA3 n (push (inr x , s) i) = PushoutPushoutMap→PushoutABot3 n x s i
  {-
  iso4 : (n : ℕ) → Iso (Pushout (pushoutMapₛ {B = B} {C = C} {D = D} f g (suc n)) fst) (pushoutA {B = B} {C}{D} f g (suc (suc (suc n))))
  iso4 n = compIso (iso3 n) (compIso (pushoutIsoₛMain (suc n)) 
-}

  -- anotherIso : (n : ℕ) (r : _) → PushoutPushoutMap→PushoutA {B = B} {C} {D} f g (suc n) r ≡ Iso.fun (iso4 n) r
  -- anotherIso n (inl x) = anotherIsoL n x
  -- anotherIso n (inr (inl (inl x))) = refl
  -- anotherIso n (inr (inl (inr x))) = refl
  -- anotherIso n (inr (inr x)) = refl
  -- anotherIso n (push (inl (inl x) , s) i) j = {!!}
  --   where
  --   help : {!!} ≡ {!!}
  --   help = {!!}
  -- anotherIso n (push (inl (inr x) , s) i) = {!!}
  -- anotherIso zero (push (inr x , s) i) = {!Iso.fun (iso4 zero) (push (inr x , s) i)!}
  -- anotherIso (suc n) (push (inr x , s) i) j = {!s!}

  -- -- -- it remains to show that strictPushout is the same as the regular pushout...

  -- -- pushoutSkel : CWskel ℓ
  -- -- pushoutSkel = pushoutA' , (pushoutCells' , pushoutMapMain , (B .snd .snd .snd .fst) , {!λ n → compEquiv !})
