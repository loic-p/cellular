{-# OPTIONS --cubical --lossy-unification --allow-unsolved-metas #-}
module Pushout.General where

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

open import Pushout.WithSpheres


open import Cubical.Data.Empty


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

module _ (B' C' D' : CWskel ℓ-zero)
         (f' : cellMap (strictCWskel B') (strictCWskel C'))
         (g' : cellMap (strictCWskel B') (strictCWskel D')) where
  private
    B = strictCWskel B'
    C = strictCWskel C'
    D = strictCWskel D'
    f = strictCwMap f'
    g = strictCwMap g'



  pushoutA* : ℕ → Type ℓ-zero
  pushoutA* zero = (B .fst zero)
  pushoutA* (suc n) =
    Pushout {A = fst B n} {B = fst C (suc n)} {C = fst D (suc n)}
       (∣ f ∣ (suc n) ∘ CW↪ B n) (∣ g ∣ (suc n) ∘ CW↪ B n)

  pushoutMapₛ-filler* : (n : ℕ) → (A B (suc n)) → S₊ n
                     → I → I → pushoutA* (suc (suc n))
  pushoutMapₛ-filler* n b x i k =
    doubleCompPath-filler ((λ i → inl (∣ f ∣ (suc (suc n)) (invEq (e B (suc n)) (push (b , x) (~ i))))))
      (push (α B (suc n) (b , x)))
      (λ i → inr (∣ g ∣ (suc (suc n)) (invEq (e B (suc n)) (push (b , x) i)))) k i

  pushoutMapₛ* : (n : ℕ) → (((A C (suc n)) ⊎ (A D (suc n))) ⊎ (A B n)) × S₊ n → pushoutA* (suc n)
  pushoutMapₛ* n (inl (inl x) , y) = inl (α C (suc n) (x , y))
  pushoutMapₛ* n (inl (inr x) , y) = inr (α D (suc n) (x , y))
  pushoutMapₛ* zero (inr x , false) = inl (∣ f ∣ (suc zero) ( (inr x)))
  pushoutMapₛ* zero (inr x , true) = inr (∣ g ∣ (suc zero) ( (inr x)))
  pushoutMapₛ* (suc zero) (inr x , base) = inl (∣ f ∣ (suc (suc zero)) (invEq (e B (suc zero)) (inr x)))
  pushoutMapₛ* (suc zero) (inr x , loop i) =
     ((λ i → pushoutMapₛ-filler* zero x false i i1) ∙∙ refl ∙∙ λ i → pushoutMapₛ-filler* zero x true (~ i) i1) i
  pushoutMapₛ* (suc (suc n)) (inr b , north) = inl (∣ f ∣ (suc (suc (suc n))) ( (inr b)))
  pushoutMapₛ* (suc (suc n)) (inr b , south) = inr (∣ g ∣ (suc (suc (suc n))) ((inr b)))
  pushoutMapₛ* (suc (suc n)) (inr b , merid a i) = pushoutMapₛ-filler* (suc n) b a i i1

  -- pushoutMapₛ-filler₁ : (x : A B (suc zero)) (b : Bool)
  --                    → I → I → pushoutA (suc zero)
  -- pushoutMapₛ-filler₁ x b i k =
  --   {!doubleCompPath-filler (λ i → inl (∣ f ∣ 2 (invEq (e B 1) (push (x , b) (~ i)))))
  --    (λ i → ((push (α B (suc zero) (x , b))) i))
  --    (λ i → (inr (∣ g ∣ 2 (invEq (e B 1) (push (x , b) i))))) k i!}

  PushoutA→PushoutPushoutMap*L : (n : ℕ) → (c : fst C (suc (suc n))) → (Pushout (pushoutMapₛ* n) fst)
  PushoutA→PushoutPushoutMap*L n (inl x) = inl (inl x)
  PushoutA→PushoutPushoutMap*L n (inr x) = inr (inl (inl x))
  PushoutA→PushoutPushoutMap*L n (push a i) = push ((inl (inl (fst a))) , (snd a)) i

  PushoutA→PushoutPushoutMap*R : (n : ℕ) → (c : fst D (suc (suc n))) → (Pushout (pushoutMapₛ* n) fst)
  PushoutA→PushoutPushoutMap*R n (inl x) = inl (inr x)
  PushoutA→PushoutPushoutMap*R n (inr x) = inr (inl (inr x))
  PushoutA→PushoutPushoutMap*R n (push a i) = push ((inl (inr (fst a))) , (snd a)) i



  PushoutA→PushoutPushoutMapLR-push-filler₀bot* : (t : A B (suc zero)) (i j k : I) → Pushout (pushoutMapₛ* (suc zero)) fst
  PushoutA→PushoutPushoutMapLR-push-filler₀bot* t i j k =
    PushoutA→PushoutPushoutMapLRGen0 inl
      (λ i₁ → inl (∣ f ∣ 2 (invEq (e B 1) (push (t , false) (~ i₁)))))
      (push (α B 1 (t , false)))
      (λ i₁ → inr (∣ g ∣ 2 (invEq (e B 1) (push (t , false) i₁))))
      (λ i₁ → inl (∣ f ∣ 2 (invEq (e B 1) (push (t , true) (~ i₁)))))
      (push (α B 1 (t , true)))
      (λ i₁ → inr (∣ g ∣ 2 (invEq (e B 1) (push (t , true) i₁))))
      (push (inr t , base)) (λ i j → push (inr t , loop i) (~ j)) i j i1

  PushoutA→PushoutPushoutMapLR-push-filler* : (n : ℕ) (t : A B (suc n)) (s : S₊ n) → (i j k : I) → Pushout (pushoutMapₛ* (suc n)) fst
  PushoutA→PushoutPushoutMapLR-push-filler* zero t false i j k =
    hfill (λ k → λ {(i = i0) → inl (pushoutMapₛ-filler* zero t false j (~ k))
                   ; (i = i1) → inl (pushoutMapₛ-filler* zero t true j i1)
                   ; (j = i0) → inl (inl (∣ f ∣ 2 (invEq (e B 1) (push (t , false) (i ∨ ~ k)))))
                   ; (j = i1) → inl (inr (∣ g ∣ 2 (invEq (e B 1) (push (t , false) (i ∨ ~ k)))))})
     (inS (PushoutA→PushoutPushoutMapLR-push-filler₀bot* t i j i1))
     k
  PushoutA→PushoutPushoutMapLR-push-filler* zero t true i j k = inl (pushoutMapₛ-filler* zero t true j i)
  PushoutA→PushoutPushoutMapLR-push-filler* (suc n) t s i j k =
    PushoutA→PushoutPushoutMapLRGen>1
      inl
      (λ i → inl (∣ f ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (t , s) i))))
      (push (α B (suc (suc n)) (t , s)))
      (λ i → inr (∣ g ∣ (suc (suc (suc n))) (invEq (e B (suc (suc n))) (push (t , s) (~ i)))))
      (push (inr t , north))
      (push (inr t , south))
      (λ j i → (push (inr t , merid s j)) i)
      i j k

  PushoutA→PushoutPushoutMap*Fill>2 : (n : ℕ) (t : _) (s : _) → (i j k : I) → Pushout (pushoutMapₛ* (suc (suc n))) fst 
  PushoutA→PushoutPushoutMap*Fill>2 n t s i j k =
    hfill (λ k → λ {(i = i0) →  inl (pushoutMapₛ-filler* (suc n) t s j (~ k))
                   ; (i = i1) → compPath-filler'' (push (inr t , north)) (sym (push (inr t , south))) k j
                   ; (j = i0) → invSides-filler (push (inr t , north))
                                                 (λ k → inl (inl (∣ f ∣ (suc (suc (suc n))) (push (t , s) (~ k))))) k i
                   ; (j = i1) → invSides-filler (push (inr t , south))
                                                 ((λ k → inl (inr (∣ g ∣ (suc (suc (suc n))) (push (t , s) (~ k)))))) k i})
          (inS (push (inr t , merid s j) i))
          k

  PushoutA→PushoutPushoutMap* : (n : ℕ) → (pushoutA* (suc (suc n))) → (Pushout (pushoutMapₛ* n) fst)
  PushoutA→PushoutPushoutMap* n (inl x) = PushoutA→PushoutPushoutMap*L n x
  PushoutA→PushoutPushoutMap* n (inr x) = PushoutA→PushoutPushoutMap*R n x
  PushoutA→PushoutPushoutMap* n (push (inl x) i) = inl (push x i)
  PushoutA→PushoutPushoutMap* zero (push (inr x) i) =  (push ((inr x) , false) ∙∙ refl ∙∙ sym (push ((inr x) , true))) i
  PushoutA→PushoutPushoutMap* (suc zero) (push (inr x) i) = inl (pushoutMapₛ-filler* zero x true i i1)
  PushoutA→PushoutPushoutMap* (suc (suc n)) (push (inr x) i) = (push ((inr x) , north) ∙ sym (push ((inr x) , south))) i
  PushoutA→PushoutPushoutMap* (suc zero) (push (push (a , false) i) j) = PushoutA→PushoutPushoutMapLR-push-filler* zero a false i j i1 
  PushoutA→PushoutPushoutMap* (suc zero) (push (push (a , true) i) j) =  inl (pushoutMapₛ-filler* zero a true j i)
  PushoutA→PushoutPushoutMap* (suc (suc n)) (push (push (t , s) i) j) =
    PushoutA→PushoutPushoutMap*Fill>2 n t s i j i1

  pushoutA↑* : (n : ℕ) → (pushoutA* (suc n)) → (pushoutA* (suc (suc n)))
  pushoutA↑* n (inl x) = inl (inl x)
  pushoutA↑* n (inr x) = inr (inl x)
  pushoutA↑* n (push a i) = push (CW↪ B n a) i


  PushoutPushoutMap→PushoutA*Fill>2 : (n : ℕ) (x : _) (a : _) → (i j k : I) → pushoutA* (suc (suc (suc (suc n))))
  PushoutPushoutMap→PushoutA*Fill>2 n x a i j k =
    hfill (λ k → λ {(i = i0) → pushoutA↑* (suc (suc n)) (pushoutMapₛ-filler* (suc n) x a j k)
                   ; (i = i1) → inl  (∣ f ∣ (suc (suc (suc (suc n)))) (CW↪ B (suc (suc (suc n))) (push (x , a) k)))
                   ; (j = i0) → inl (inl (∣ f ∣ (suc (suc (suc n))) ((push (x , a) k))))
                   ; (j = i1) → push (push (x , a) k) (~ i)})
          (inS (push (CW↪ B (suc (suc n)) (α B (suc (suc n)) (x , a))) (j ∧ ~ i))) k

  PushoutPushoutMap→PushoutA* : (n : ℕ) → (Pushout (pushoutMapₛ* n) fst) → (pushoutA* (suc (suc n)))
  PushoutPushoutMap→PushoutA* n (inl x) = pushoutA↑* n x
  PushoutPushoutMap→PushoutA* n (inr (inl (inl x))) = inl (inr x)
  PushoutPushoutMap→PushoutA* n (inr (inl (inr x))) = inr (invEq (e D (suc n)) (inr x))
  PushoutPushoutMap→PushoutA* n (inr (inr x)) = inl (CW↪ C (suc n) ((∣ f ∣ (suc n) (invEq (e B n) (inr x)))))
  PushoutPushoutMap→PushoutA* n (push (inl (inl x) , b) i) =
    inl (((push (x , b)) i))
  PushoutPushoutMap→PushoutA* n (push (inl (inr x) , b) i) =
    inr ( ((push (x , b)) i))
  PushoutPushoutMap→PushoutA* zero (push (inr x , false) i) = inl (inl (∣ f ∣ 1 ((inr x))))
  PushoutPushoutMap→PushoutA* zero (push (inr x , true) i) = push (inr x) (~ i)
  PushoutPushoutMap→PushoutA* (suc zero) (push (inr x , base) i) = inl (inl (∣ f ∣ 2 (invEq (e B 1) (inr x))))
  PushoutPushoutMap→PushoutA* (suc zero) (push (inr x , loop j) i) =
    hcomp (λ k → λ {(i = i0) → pushoutA↑* (suc zero) {!doubleCompPath-filler ? ? ?!} -- pushoutA↑* (suc (suc n)) (pushoutMapₛ-filler* (suc n) x a j k)
                   ; (i = i1) → {!!}
                   ; (j = i0) → {!!}
                   ; (j = i1) → {!!}})
           {!!}
  PushoutPushoutMap→PushoutA* (suc (suc n)) (push (inr x , north) i) = inl (inl (∣ f ∣ (suc (suc (suc n)))  (inr x)))
  PushoutPushoutMap→PushoutA* (suc (suc n)) (push (inr x , south) i) = push (inr x) (~ i)
  PushoutPushoutMap→PushoutA* (suc (suc n)) (push (inr x , merid a j) i) =
    PushoutPushoutMap→PushoutA*Fill>2 n x a i j i1

    -- pushoutA↑* (suc (suc n)) {!pushoutMapₛ-filler* (suc n) x a i₁ (~ i) !}


  PushoutFam : (n : ℕ) (x : _) → PushoutPushoutMap→PushoutA* n (PushoutA→PushoutPushoutMap* n x) ≡ x
  PushoutFam n (inl (inl x)) = refl
  PushoutFam n (inl (inr x)) = refl
  PushoutFam n (inl (push a i)) = refl
  PushoutFam n (inr (inl x)) = refl
  PushoutFam n (inr (inr x)) = refl
  PushoutFam n (inr (push a i)) = refl
  PushoutFam n (push (inl x) i) = refl
  PushoutFam zero (push (inr x) i) j = {!!} -- 
  PushoutFam (suc zero) (push (inr x) i) = {!!}
  PushoutFam (suc (suc n)) (push (inr x) i) j =
    PushoutPushoutMap→PushoutA* (suc (suc n))
      (compPath-filler' (push (inr x , north)) (sym (push (inr x , south))) (~ j) i)
  PushoutFam (suc zero) (push (push a i) j) = {!!}
  PushoutFam (suc (suc n)) (push (push (t , s) i) j) k = {!!}
  {-
    hcomp (λ r → λ {(i = i0) → PushoutPushoutMap→PushoutA* (suc (suc n))
                                  (PushoutA→PushoutPushoutMap*Fill>2 n t s i0 j r)
                   ; (i = i1) → {!PushoutPushoutMap→PushoutA* (suc (suc n))
                                  (compPath-filler' (push (inr t , north)) (sym (push (inr t , south))) (~ k) j)!}
                   ; (j = i0) → PushoutPushoutMap→PushoutA* (suc (suc n)) (PushoutA→PushoutPushoutMap*Fill>2 n t s i j r)  -- 
                   ; (j = i1) → PushoutPushoutMap→PushoutA* (suc (suc n)) (PushoutA→PushoutPushoutMap*Fill>2 n t s i j r) -- 
                   ; (k = i0) → PushoutPushoutMap→PushoutA* (suc (suc n)) (PushoutA→PushoutPushoutMap*Fill>2 n t s i j r) -- 
                   ; (k = i1) → k1 r j i})
          {!!}
          -}
      where -- r j i

      mainn : Cube (λ i j → PushoutPushoutMap→PushoutA* (suc (suc n))
                              (PushoutA→PushoutPushoutMap* (suc (suc n))
                                (push (push (t , s) j) i)))
            (λ j i → push (push (t , s) i) j)
            (λ j i → inl (inl (strictMapFun f' (suc (suc (suc n))) (push (t , s) i))))
           (λ j i → inr (inl (strictMapFun g' (suc (suc (suc n))) (push (t , s) i))))
           (λ k j → push (CW↪ B (suc (suc n)) (strictifyFamα B' (suc (suc n)) (t , s))) j)
           (λ k j → PushoutPushoutMap→PushoutA* (suc (suc n))
                   (compPath-filler' (push (inr t , north)) (sym (push (inr t , south))) (~ k) j))
      mainn = cong-hcomp (PushoutPushoutMap→PushoutA* (suc (suc n)))
            ◁ λ r i j →
              hcomp (λ k → λ {(i = i0) → {!!}
                   ; (i = i1) → {!!}
                   ; (j = i0) → {!!}
                   ; (j = i1) → {!!}
                   ; (r = i1) → {!!}})
                     {!!}

      invSides-fillerLOL : ∀ {ℓ} {A B : Type ℓ} {x : A} (y : A) (p : x ≡ y) (z : A) (q : x ≡ z)
        → {x' : A} (y' : A) (p' : x' ≡ y') (z' : A) (q' : x' ≡ z')
        → (F : A → B)
        → Cube {!!} {!!}
                (λ r i → F (invSides-filler p q r i))
                (λ r i → F (invSides-filler p q r i) )
                {!!}
                {!!}
      invSides-fillerLOL = {!PushoutPushoutMap→PushoutA* (suc (suc n))!}

      k1 : Cube
              (λ i j → PushoutPushoutMap→PushoutA* (suc (suc n))
                           (PushoutA→PushoutPushoutMap*Fill>2 n t s j i i0))
              (λ j i → push (push (t , s) i) j)
           
              (λ r i → PushoutPushoutMap→PushoutA* (suc (suc n))
                     (invSides-filler (push (inr t , north))
                                                 ((λ k → inl (inl (∣ f ∣ (suc (suc (suc n))) (push (t , s) (~ k)))))) r i))
              (λ r i → PushoutPushoutMap→PushoutA* (suc (suc n))
                     (invSides-filler (push (inr t , south))
                                                 ((λ k → inl (inr (∣ g ∣ (suc (suc (suc n))) (push (t , s) (~ k)))))) r i))

           (λ r j → PushoutPushoutMap→PushoutA* (suc (suc n))
                       (PushoutA→PushoutPushoutMap*Fill>2 n t s i0 j r))
           (λ i j → push (inr t) (i ∧ j))
          
      k1 r j i =
      -- cong-hcomp (PushoutPushoutMap→PushoutA* (suc (suc n)))
      --    ◁ {!!} -- cubePermute-ijk↦kji {!!} -- (cubePermute-ijk↦kji ?) -- ({!!} ◁ {!!})
      --    ▷ sym (cong-hcomp (PushoutPushoutMap→PushoutA* (suc (suc n))))
         hcomp (λ k → λ {(i = i0) → {!!} -- PushoutPushoutMap→PushoutA* (suc (suc n)) (inl (pushoutMapₛ-filler* (suc n) t s j (~ r ∨ ~ k)))
                   ; (i = i1) →  {!!} -- s1 k j r -- push (inr t) (j ∧ (r ∨ ~ k)) --  -- 
                   ; (j = i0) → PushoutPushoutMap→PushoutA* (suc (suc n))
                                    (invSides-filler-filler (push (inr t , north))  ((λ k → inl (inl (∣ f ∣ (suc (suc (suc n))) (push (t , s) (~ k)))))) r i k)
                   ; (j = i1) → PushoutPushoutMap→PushoutA* (suc (suc n))
                                    (invSides-filler-filler (push (inr t , south))  ((λ k → inl (inr (∣ g ∣ (suc (suc (suc n))) (push (t , s) (~ k)))))) r i k)
                   ; (r = i0) → PushoutPushoutMap→PushoutA*Fill>2 n t s (i ∧ k) j i1
                   ; (r = i1) →  push (push (t , s) (i ∨ ~ k)) j})
          {!PushoutPushoutMap→PushoutA*Fill>2 n t s i0 j (~ r)!}
          
          where
          s1 : Cube (λ j k → {!PushoutPushoutMap→PushoutA*Fill>2 n t s i0 j (~ k)!}) (λ j r → push (inr t) (r ∧ j))
                          (λ k r → inl (inl (∣ f ∣ (suc (suc (suc n))) (inr t))))
                          (λ k r → push (inr t) (r ∨ ~ k))
                          (λ k j → PushoutPushoutMap→PushoutA*Fill>2 n t s k j i1)
                          (λ k j → push (inr t) j)
          s1 = {!!}


-- PushoutRec : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
--   {f : A → B} {g : A → C} (inl* : B → D) (inr* : C → D) (comm : (c : A) → inl* (f c) ≡ inr* (g c))
--   → Pushout f g → D
-- PushoutRec inl* inr* comm (inl x) = inl* x
-- PushoutRec inl* inr* comm (inr x) = inr* x
-- PushoutRec inl* inr* comm (push a i) = comm a i

-- module _ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
--   {f : A → B} {g : A → C} {D : Type ℓ''} (inl* : B → D)
--   (P : (r : Pushout f g → D) → ((x : _) → r (inl x) ≡ inl* x) → Type ℓ''')
--   (ind : (inr* : C → D) (comm : (c : A) → inl* (f c) ≡ inr* (g c)) → P (PushoutRec inl* inr* comm) λ _ → refl)
--   where
--   private
--     ΣTy : Type _
--     ΣTy = Σ[ F ∈ (Pushout f g → D) ] ((x : _) → F (inl x) ≡ inl* x)

--   module _ (F : Pushout f g → D) (com : ((x : _) → F (inl x) ≡ inl* x)) where
--     indPushout≡ : Path ΣTy (F , com) (PushoutRec inl* (F ∘ inr) (λ c → sym (com (f c)) ∙ cong F (push c)) , λ _ → refl)
--     fst (indPushout≡ i) (inl x) = com x i
--     fst (indPushout≡ i) (inr x) = F (inr x)
--     fst (indPushout≡ i) (push a j) = compPath-filler' (sym (com (f a))) (cong F (push a)) i j
--     snd (indPushout≡ i) j k = com j (i ∨ k)

--     indPushout : P F com
--     indPushout = subst (λ FG → P (fst FG) (snd FG)) (sym indPushout≡)
--                        (ind (F ∘ inr) λ c → sym (com (f c)) ∙ cong F (push c))

--   module _ where
--     indPushoutβ : (inr* : C → D) (comm : (c : A) → inl* (f c) ≡ inr* (g c))
--       →  indPushout (PushoutRec inl* inr* comm) (λ _ → refl) ≡ ind inr* comm
--     indPushoutβ inr* comm = {!!}
-- {-
-- (λ i → subst (λ FG → P (fst FG) (snd FG)) (λ j → {!help i j!})
--                                            {!!}) ∙ {!!}
--       where
--       PP : Path ΣTy ((PushoutRec inl* (PushoutRec inl* inr* comm ∘ inr)
--                     (λ c → sym refl ∙ cong (PushoutRec inl* inr* comm) (push c))
--                     , (λ z → refl))) ((PushoutRec inl* inr* comm) , ((λ z → refl))) 
--       PP = {!!}

--       help : Square (indPushout≡ (PushoutRec inl* inr* comm) λ _ → refl) refl (sym PP) refl
--       help = {!!}

--     indPushoutβs : (inr* : C → D) (comm : (c : A) → inl* (f c) ≡ inr* (g c))
--       → indPushout≡ (PushoutRec inl* inr* comm) (λ _ → refl) ≡ ΣPathP ({!!} , {!!})
--     indPushoutβs = {!!}
-- -}


-- module PushoutGeneral
--   (lev : ℕ)
--   {ℓ} {Bₙ Bₙ₊₁ Bₙ₊₂ : Type ℓ} (Bmₙ : ℕ)
--     (Bαₙ : Fin Bmₙ × S⁻ lev → Bₙ)
--     (Beₙ : Bₙ₊₁ ≃ Pushout Bαₙ fst) (Bmₙ₊₁ : ℕ)
--     (Bαₙ₊₁ : Fin Bmₙ₊₁ × S₊ lev → Bₙ₊₁)
--     (Beₙ₊₁ : Bₙ₊₂ ≃ Pushout Bαₙ₊₁ fst)

--     {Cₙ Cₙ₊₁ Cₙ₊₂ : Type ℓ} (Cmₙ : ℕ)
--     (Cαₙ : Fin Cmₙ × S⁻ lev → Cₙ)
--     (Ceₙ : Cₙ₊₁ ≃ Pushout Cαₙ fst) (Cmₙ₊₁ : ℕ)
--     (Cαₙ₊₁ : Fin Cmₙ₊₁ × S₊ lev → Cₙ₊₁)
--     (Ceₙ₊₁ : Cₙ₊₂ ≃ Pushout Cαₙ₊₁ fst)

--     {Dₙ Dₙ₊₁ Dₙ₊₂ : Type ℓ} (Dmₙ : ℕ)
--     (Dαₙ : Fin Dmₙ × S⁻ lev → Dₙ)
--     (Deₙ : Dₙ₊₁ ≃ Pushout Dαₙ fst) (Dmₙ₊₁ : ℕ)
--     (Dαₙ₊₁ : Fin Dmₙ₊₁ × S₊ lev → Dₙ₊₁)
--     (Deₙ₊₁ : Dₙ₊₂ ≃ Pushout Dαₙ₊₁ fst)

--     (fₙ : Bₙ → Cₙ) 
--     (fₙ₊₁ : Bₙ₊₁ → Cₙ₊₁) (fₙc : (x : Bₙ) → fₙ₊₁ (invEq Beₙ (inl x)) ≡ invEq Ceₙ (inl (fₙ x)))
--     (fₙ₊₂ : Bₙ₊₂ → Cₙ₊₂) (fₙ₊₁c : (x : Bₙ₊₁) → fₙ₊₂ (invEq Beₙ₊₁ (inl x)) ≡ invEq Ceₙ₊₁ (inl (fₙ₊₁ x)))

--     (gₙ : Bₙ → Dₙ) 
--     (gₙ₊₁ : Bₙ₊₁ → Dₙ₊₁) (gₙc : (x : Bₙ) → gₙ₊₁ (invEq Beₙ (inl x)) ≡ invEq Deₙ (inl (gₙ x)))
--     (gₙ₊₂ : Bₙ₊₂ → Dₙ₊₂) (gₙ₊₁c : (x : Bₙ₊₁) → gₙ₊₂ (invEq Beₙ₊₁ (inl x)) ≡ invEq Deₙ₊₁ (inl (gₙ₊₁ x)))
    
--     where
--     Pushoutₙ : Type _
--     Pushoutₙ = Pushout ((invEq Ceₙ ∘ inl) ∘ fₙ) ((invEq Deₙ ∘ inl) ∘ gₙ)

--     Pushoutₙ₊₁ : Type _
--     Pushoutₙ₊₁ = Pushout ((invEq Ceₙ₊₁ ∘ inl) ∘ fₙ₊₁) ((invEq Deₙ₊₁ ∘ inl) ∘ gₙ₊₁)


--     ∃α : Type _
--     ∃α = Σ[ α ∈ (((Fin Cmₙ₊₁ ⊎ Fin Dmₙ₊₁) ⊎ Fin Bmₙ) × S₊ lev → Pushoutₙ) ] Pushout α fst ≃ Pushoutₙ₊₁


-- module _
--   (lev : ℕ)
--   {ℓ} {Bₙ : Type ℓ} (Bmₙ : ℕ)
--     (Bαₙ : Fin Bmₙ × S⁻ lev → Bₙ) (Bmₙ₊₁ : ℕ)
--     (Bαₙ₊₁ : Fin Bmₙ₊₁ × S₊ lev → Pushout Bαₙ fst)

--     {Cₙ : Type ℓ} (Cmₙ : ℕ)
--     (Cαₙ : Fin Cmₙ × S⁻ lev → Cₙ) (Cmₙ₊₁ : ℕ)
--     (Cαₙ₊₁ : Fin Cmₙ₊₁ × S₊ lev → Pushout Cαₙ fst)

--     {Dₙ  : Type ℓ} (Dmₙ : ℕ)
--     (Dαₙ : Fin Dmₙ × S⁻ lev → Dₙ) (Dmₙ₊₁ : ℕ)
--     (Dαₙ₊₁ : Fin Dmₙ₊₁ × S₊ lev → Pushout Dαₙ fst)

--     (fₙ : Bₙ → Cₙ) 
--     (fₙ₊₁ : Fin Bmₙ → Pushout Cαₙ fst) (fₙc : (c : Fin Bmₙ × S⁻ lev) → inl (fₙ (Bαₙ c)) ≡ fₙ₊₁ (fst c))
--     (fₙ₊₂ : Fin Bmₙ₊₁ → Pushout Cαₙ₊₁ fst)
--     (fₙ₊₁c : (c : Fin Bmₙ₊₁ × S₊ lev) → inl (PushoutRec (λ x → inl (fₙ x)) fₙ₊₁ fₙc (Bαₙ₊₁ c)) ≡ fₙ₊₂ (fst c))

--     (gₙ : Bₙ → Dₙ) 
--     (gₙ₊₁ : Fin Bmₙ → Pushout Dαₙ fst) (gₙc : (c : Fin Bmₙ × S⁻ lev) → inl (gₙ (Bαₙ c)) ≡ gₙ₊₁ (fst c))
--     (gₙ₊₂ : Fin Bmₙ₊₁ → Pushout Dαₙ₊₁ fst)
--     (gₙ₊₁c : (c : Fin Bmₙ₊₁ × S₊ lev) → inl (PushoutRec (λ x → inl (gₙ x)) gₙ₊₁ gₙc (Bαₙ₊₁ c)) ≡ gₙ₊₂ (fst c))


--    where
--    module M = PushoutGeneral lev Bmₙ Bαₙ (idEquiv _) Bmₙ₊₁ Bαₙ₊₁ (idEquiv _)
--                                  Cmₙ Cαₙ (idEquiv _) Cmₙ₊₁ Cαₙ₊₁ (idEquiv _)
--                                  Dmₙ Dαₙ (idEquiv _) Dmₙ₊₁ Dαₙ₊₁ (idEquiv _)
--                                  fₙ
--                                  (PushoutRec (inl ∘ fₙ) fₙ₊₁ fₙc) (λ _ → refl)
--                                  (PushoutRec (λ x → inl (PushoutRec (inl ∘ fₙ) fₙ₊₁ fₙc x)) fₙ₊₂ fₙ₊₁c)
--                                  (λ _ → refl)
--                                  gₙ
--                                  (PushoutRec (inl ∘ gₙ) gₙ₊₁ gₙc) (λ _ → refl)
--                                  (PushoutRec (λ x → inl (PushoutRec (inl ∘ gₙ) gₙ₊₁ gₙc x)) gₙ₊₂ gₙ₊₁c)
--                                  (λ _ → refl)

-- {-

--   (lev : ℕ)
--   {ℓ} {Bₙ : Type ℓ} (Bmₙ : ℕ)
--     (Bαₙ : Fin Bmₙ × S⁻ lev → Bₙ) (Bmₙ₊₁ : ℕ)
--     (Bαₙ₊₁ : Fin Bmₙ₊₁ × S₊ lev → Pushout Bαₙ fst)
-- -}

-- -- module _ {Bₙ₋₁ : Type} {Cₙ : Type} {Dₙ : Type} -- where
-- --   {∣B∣ₙ₋₁ ∣B∣ₙ ∣B∣ₙ₊₁ ∣C∣ₙ ∣C∣ₙ₊₁ ∣C∣ₙ₊₂ ∣D∣ₙ ∣D∣ₙ₊₁ ∣D∣ₙ₊₂ : ℕ}
-- --   (n : ℕ)
-- --   {αBₙ₋₁ : Fin ∣B∣ₙ₋₁ × S₊ n → Bₙ₋₁}
-- --   {αBₙ : Fin ∣B∣ₙ × S₊ (suc n) → Pushout αBₙ₋₁ fst}
-- --   {αBₙ₊₁ : Fin ∣B∣ₙ₊₁ × S₊ (suc (suc n)) → Pushout αBₙ fst}
-- --   {αCₙ : Fin ∣C∣ₙ × S₊ (suc n) → Cₙ}
-- --   {αCₙ₊₁ : Fin ∣C∣ₙ₊₁ × S₊ (suc (suc n)) → Pushout αCₙ fst}
-- --   {αCₙ₊₂ : Fin ∣C∣ₙ₊₂ × S₊ (suc (suc (suc n))) → Pushout αCₙ₊₁ fst}
-- --   {αDₙ : Fin ∣D∣ₙ × S₊ (suc n) → Dₙ}
-- --   {αDₙ₊₁ : Fin ∣D∣ₙ₊₁ × S₊ (suc (suc n)) → Pushout αDₙ fst}
-- --   {αDₙ₊₂ : Fin ∣D∣ₙ₊₂ × S₊ (suc (suc (suc n))) → Pushout αDₙ₊₁ fst}
-- --   {fₙ : Bₙ₋₁ → Cₙ} {gₙ : Bₙ₋₁ → Dₙ}
-- --   {fₙ₊₁ : Pushout αBₙ₋₁ fst → Pushout αCₙ fst}
-- --   {gₙ₊₁ : Pushout αBₙ₋₁ fst → Pushout αDₙ fst}
-- --   {fₙ₊₂ : Pushout αBₙ fst → Pushout αCₙ₊₁ fst}
-- --   {gₙ₊₂ : Pushout αBₙ fst → Pushout αDₙ₊₁ fst}
-- --   {fₙ-comm : (a : _) → fₙ₊₁ (inl a) ≡ inl (fₙ a)}
-- --   {gₙ-comm : (a : _) → gₙ₊₁ (inl a) ≡ inl (gₙ a)}
-- --   {fₙ₊₁-comm : (a : _) → fₙ₊₂ (inl a) ≡ inl (fₙ₊₁ a)}
-- --   {gₙ₊₁-comm : (a : _) → gₙ₊₂ (inl a) ≡ inl (gₙ₊₁ a)}
-- --   where




-- -- module _ {Bₙ₋₁ : Type} {Cₙ : Type} {Dₙ : Type} -- where
-- --   {∣B∣ₙ₋₁ ∣B∣ₙ ∣B∣ₙ₊₁ ∣C∣ₙ ∣C∣ₙ₊₁ ∣C∣ₙ₊₂ ∣D∣ₙ ∣D∣ₙ₊₁ ∣D∣ₙ₊₂ : ℕ}
-- --   (n : ℕ)
-- --   {αBₙ₋₁ : Fin ∣B∣ₙ₋₁ × S₊ n → Bₙ₋₁}
-- --   {αBₙ : Fin ∣B∣ₙ × S₊ (suc n) → Pushout αBₙ₋₁ fst}
-- --   {αBₙ₊₁ : Fin ∣B∣ₙ₊₁ × S₊ (suc (suc n)) → Pushout αBₙ fst}
-- --   {αCₙ : Fin ∣C∣ₙ × S₊ (suc n) → Cₙ}
-- --   {αCₙ₊₁ : Fin ∣C∣ₙ₊₁ × S₊ (suc (suc n)) → Pushout αCₙ fst}
-- --   {αCₙ₊₂ : Fin ∣C∣ₙ₊₂ × S₊ (suc (suc (suc n))) → Pushout αCₙ₊₁ fst}
-- --   {αDₙ : Fin ∣D∣ₙ × S₊ (suc n) → Dₙ}
-- --   {αDₙ₊₁ : Fin ∣D∣ₙ₊₁ × S₊ (suc (suc n)) → Pushout αDₙ fst}
-- --   {αDₙ₊₂ : Fin ∣D∣ₙ₊₂ × S₊ (suc (suc (suc n))) → Pushout αDₙ₊₁ fst}
-- --   {fₙ : Bₙ₋₁ → Cₙ} {gₙ : Bₙ₋₁ → Dₙ}
-- --   {fₙ₊₁ : Pushout αBₙ₋₁ fst → Pushout αCₙ fst}
-- --   {gₙ₊₁ : Pushout αBₙ₋₁ fst → Pushout αDₙ fst}
-- --   {fₙ₊₂ : Pushout αBₙ fst → Pushout αCₙ₊₁ fst}
-- --   {gₙ₊₂ : Pushout αBₙ fst → Pushout αDₙ₊₁ fst}
-- --   {fₙ-comm : (a : _) → fₙ₊₁ (inl a) ≡ inl (fₙ a)}
-- --   {gₙ-comm : (a : _) → gₙ₊₁ (inl a) ≡ inl (gₙ a)}
-- --   {fₙ₊₁-comm : (a : _) → fₙ₊₂ (inl a) ≡ inl (fₙ₊₁ a)}
-- --   {gₙ₊₁-comm : (a : _) → gₙ₊₂ (inl a) ≡ inl (gₙ₊₁ a)}
  
-- --   where
-- --   Pₙ = Pushout fₙ gₙ
-- --   Pₙ₊₁ = Pushout fₙ₊₁ gₙ₊₁
-- --   Pₙ₊₂ = Pushout fₙ₊₂ gₙ₊₂

-- --   ιPₙ : Pₙ → Pₙ₊₁
-- --   ιPₙ (inl x) = inl (inl x)
-- --   ιPₙ (inr x) = inr (inl x)
-- --   ιPₙ (push a i) =  ((λ j → inl (fₙ-comm a (~ j))) ∙∙ push (inl a) ∙∙ λ j → inr (gₙ-comm a j)) i

-- --   ιPₙ₊₁ : Pₙ₊₁ → Pₙ₊₂
-- --   ιPₙ₊₁ (inl x) = inl (inl x)
-- --   ιPₙ₊₁ (inr x) = inr (inl x)
-- --   ιPₙ₊₁ (push a i) =  ((λ j → inl (fₙ₊₁-comm a (~ j))) ∙∙ push (inl a) ∙∙ λ j → inr (gₙ₊₁-comm a j)) i

-- --   module _ (e : {!!}) where



-- -- -- --  {αDₙ₋₁ : ∣B∣ₙ₋₁ × S₊ n → Bₙ₋₁}
-- -- --   {αₙ₋₁ αₙ : {!!}}
-- -- --   where
-- -- --   Pₙ : {!!}
-- -- --   Pₙ = {!!}

-- -- -- -- module _ {Bₙ₋₁ Bₙ Bₙ₊₁ : Type} {Cₙ Cₙ₊₁ Cₙ₊₂ : Type} {Dₙ Dₙ₊₁ Dₙ₊₂ : Type} {Pₙ Pₙ+₁ Pₙ₊₂ : Type}
-- -- -- --   (fₙ₋₁ : Bₙ₋₁ → Cₙ) (fₙ : Bₙ → Cₙ₊₁) (fₙ₊₁ : Bₙ₊₁ → Cₙ₊₂)
-- -- -- --   (gₙ₋₁ : Bₙ₋₁ → Dₙ) (gₙ : Bₙ → Dₙ₊₁) (gₙ₊₁ : Bₙ₊₁ → Dₙ₊₂)
-- -- -- --   (ιB : {!!})
-- -- -- --   (αₙ : {!!}) where
