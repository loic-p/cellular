{-# OPTIONS --cubical --lossy-unification --allow-unsolved-metas #-}
module Pushout.Attempt5Cont where

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


open import Pushout.Attempt5

private
  variable
    ℓ ℓ' : Level
preBTCGen : {A : Type ℓ'} {Cₙ Cₙ₊₁ : Type ℓ} (n : ℕ)
    (αₙ : A × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → (x : A)
    → S₊∙ n →∙ (cofib (invEq e ∘ inl) , inl tt)
fst (preBTCGen zero αₙ e x) false = inr (invEq e (inr x))
fst (preBTCGen zero αₙ e x) true = inl tt
fst (preBTCGen (suc zero) αₙ e x) base = inl tt
fst (preBTCGen (suc zero) αₙ e x) (loop i) =
    (push (αₙ (x , false))
  ∙∙ (λ j → inr (invEq e ((push (x , false) ∙ sym (push (x , true))) j)))
  ∙∙ sym (push (αₙ (x , true)))) i
fst (preBTCGen (suc (suc n)) αₙ e x) north = inl tt
fst (preBTCGen (suc (suc n)) αₙ e x) south = inl tt
fst (preBTCGen (suc (suc n)) αₙ e x) (merid a i) =
  (push (αₙ (x , a))
  ∙∙ (λ j → inr (invEq e ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) j)))
  ∙∙ sym (push (αₙ (x , ptSn (suc n))))) i
snd (preBTCGen zero αₙ e x) = refl
snd (preBTCGen (suc zero) αₙ e x) = refl
snd (preBTCGen (suc (suc n)) αₙ e x) = refl

module _  where
  Pushout→BouquetGen : {A : Type ℓ'} {Cₙ Cₙ₊₁ : Type ℓ} (n : ℕ)
    (αₙ : A × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst)
    → Pushout αₙ fst → SphereBouquet n A
  Pushout→BouquetGen n αₙ e (inl x) = inl tt
  Pushout→BouquetGen zero αₙ e (inr x) = inr (x , false)
  Pushout→BouquetGen (suc n) αₙ e (inr x) = inr (x , ptSn (suc n))
  Pushout→BouquetGen (suc n) αₙ e (push a i) =
    (push (a .fst) ∙ λ i → inr (a .fst , σSn n (a .snd) i)) i

-- Maps back and forth
module BouquetFunsGen {A : Type ℓ'} {Cₙ Cₙ₊₁ : Type ℓ} (n : ℕ)
    (αₙ : A × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where
  CTB : cofib (invEq e ∘ inl) → SphereBouquet n A
  CTB (inl x) = inl tt
  CTB (inr x) = Pushout→BouquetGen n αₙ e (fst e x)
  CTB (push a i) = Pushout→BouquetGen n αₙ e (secEq e (inl a) (~ i))

  BTC : SphereBouquet n A → cofib (invEq e ∘ inl)
  BTC (inl x) = inl tt
  BTC (inr x) = preBTCGen n αₙ e (fst x) .fst (snd x)
  BTC (push a i) = preBTCGen n αₙ e a .snd (~ i)

module _ (isEquivPushoutA→PushoutPushoutMapStrict : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
  (f : cellMap B C)
  (g : cellMap B D)
   → (n : ℕ) → retract (PushoutPushoutMap→PushoutA f g n) (PushoutA→PushoutPushoutMap f g n)
               × section (PushoutPushoutMap→PushoutA f g n) (PushoutA→PushoutPushoutMap f g n)) where
  open MOOO isEquivPushoutA→PushoutPushoutMapStrict

  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)
  open import Cubical.HITs.Wedge
  open import Cubical.Foundations.Pointed



  sphereBouquetSuspIso∙ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → Iso.fun (sphereBouquetSuspIso {A = A} {n}) north ≡ inl tt
  sphereBouquetSuspIso∙ {n = zero} = refl
  sphereBouquetSuspIso∙ {n = suc n} = refl

  QuotCW : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Type ℓ 
  QuotCW C n = cofib (CW↪ C n)

  QuotCW∙ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Pointed ℓ 
  QuotCW∙ C n = QuotCW C n , inl tt

  module _ {ℓ ℓ' ℓ'' : Level} {B' : CWskel ℓ} {D' : CWskel ℓ''}
    (f : cellMap (strictCWskel B') (strictCWskel D')) where
    private
      B = strictCWskel B'
      D = strictCWskel D'
      C = UnitCWskel

    open MIAU f


    bouquetFun1 : (n : ℕ) → SphereBouquet n (Fin (card cofibCWskel n)) → QuotCW cofibCWskel n
    bouquetFun1 n = BouquetFuns.BTC n (card cofibCWskel n) (α cofibCWskel n) (e cofibCWskel n)


    SphereBouquetCellEquiv : (n m : ℕ)
      → SphereBouquet n (Fin (card cofibCWskel m)) ≃ (SplitBouquet n (card C m) (card D m) (pushoutMidCells terminalCW f m))
    SphereBouquetCellEquiv n m = isoToEquiv (compIso (sphereBouquetIso n) (Iso-sumSphereBouquet-SplitBouquet n))

    bouquetFun1' : (n : ℕ) → SplitBouquet n (card C n) (card D n) (pushoutMidCells terminalCW f n)
                            → QuotCW cofibCWskel n
    bouquetFun1' n = bouquetFun1 n ∘ invEq (SphereBouquetCellEquiv n n)

    -- bottom left fun
    bouquetFun'-inl : (n : ℕ) → (SphereBouquet∙ (suc n) (Fin zero) ⋁ SphereBouquet∙ (suc n) (Fin (card D (suc n))))
                               → (QuotCW D (suc n))
    bouquetFun'-inl n (inl x) = inl tt
    bouquetFun'-inl n (inr x) = BouquetFuns.BTC (suc n) (card D (suc n)) (α D (suc n)) (e D (suc n)) x
    bouquetFun'-inl n (push a i) = inl tt

    bouquetFun' : (n : ℕ) → SplitBouquet (suc n) zero (card D (suc n)) (pushoutMidCells terminalCW f (suc n))
                            → (QuotCW∙ D (suc n)) ⋁ Susp∙ (QuotCW B n)
    bouquetFun' n (inl x) = inl (bouquetFun'-inl n x)
    bouquetFun' n (inr x) = inr (suspFun (BouquetFuns.BTC n (card B n) (α B n) (e B n)) (Iso.inv sphereBouquetSuspIso x))
    bouquetFun' zero (push a i) = push tt i
    bouquetFun' (suc n) (push a i) = push tt i

    -- its inverse
    -- bouquetFunInv-inl : (n : ℕ) → (SphereBouquet∙ (suc n) (Fin zero) ⋁ SphereBouquet∙ (suc n) (Fin (card D (suc n))))
    --                            → (QuotCW D (suc n))
    -- bouquetFunInv-inl n (inl x) = inl tt
    -- bouquetFunInv-inl n (inr x) = BouquetFuns.BTC (suc n) (card D (suc n)) (α D (suc n)) (e D (suc n)) x
    -- bouquetFunInv-inl n (push a i) = inl tt

    bouquetFunInv : (n : ℕ) → (QuotCW∙ D (suc n)) ⋁ Susp∙ (QuotCW B n)
      → SplitBouquet (suc n) zero (card D (suc n)) (pushoutMidCells terminalCW f (suc n))
    bouquetFunInv n (inl x) =
      inl (inr (BouquetFuns.CTB (suc n) (card D (suc n)) (α D (suc n)) (e D (suc n)) x))
    bouquetFunInv n (inr x) = inr (Iso.fun sphereBouquetSuspIso
                                    (suspFun (BouquetFuns.CTB n (card B n) (α B n) (e B n)) x))
    bouquetFunInv zero (push a i) = ((λ i → inl (push tt (~ i))) ∙ push tt) i
    bouquetFunInv (suc n) (push a i) = ((λ i → inl (push tt (~ i))) ∙ push tt) i

    SphereBouquetSplit : (n : ℕ) → Type
    SphereBouquetSplit n = SphereBouquet (suc (suc n)) (Fin (card D (suc (suc n))) ⊎ Fin (card B (suc n)))

    cofibskel' : (n : ℕ) → Type _
    cofibskel' n = Pushout (pushoutMapₛ terminalCW f n) fst

    Iso-cofibskel' : (n : ℕ) → (fst cofibCWskel (suc (suc n))) ≃ (cofibskel' n)
    Iso-cofibskel' = eCWPushout terminalCW f

    cofibskel'↑ : (n : ℕ) → cofibskel' n → cofibskel' (suc n)
    cofibskel'↑ n x = inl (invEq (Iso-cofibskel' n) x)

    cofibskelQuot : (n : ℕ) → Type _
    cofibskelQuot n = cofib {A = cofibskel' n} {B = cofibskel' (suc n)} (cofibskel'↑ n)

    module _ (n : ℕ) where
      module M = BouquetFunsGen {Cₙ = cofibskel' n} {cofibskel' (suc n)}
                 {! ? ∘ ?!} {!!} {!compEquiv ? (eCWPushout terminalCW f n)!}
    

    -- sinl : (n :  ℕ) → fst D (suc (suc n)) → cofibskel' n 
    -- sinl n (inl x) = inl (inr x)
    -- sinl n (inr x) = inr (inr {!x!}) -- inl (inr (inr {!x!}))
    -- sinl n (push (d , a) i) = (({!!} ∙ (λ i → inl (push {!a!} i)) ∙ {!!}) ∙ push (inl (inr d) , Iso.fun (IsoSphereSusp n) a) ∙ {!!}) i


    -- cofibskelQuot≃ : (n : ℕ) → cofibskelQuot n ≃ QuotCW cofibCWskel (suc (suc n))
    -- cofibskelQuot≃ n =
    --   pushoutEquiv _ _ _ _
    --   (invEquiv (Iso-cofibskel' n)) (idEquiv _) (invEquiv (Iso-cofibskel' (suc n)))
    --   (λ _ _ → tt) (funExt λ x → refl)


    -- -- correct type
    -- bouquetFun3 : (n : ℕ) → SplitBouquet (suc (suc n)) zero (card D (suc (suc n))) (card B (suc n))
    --                        → cofibskelQuot n
    -- bouquetFun3 n = {!!}

    -- bouquetFun2Inl : (n : ℕ) → SphereBouquet (suc (suc n)) (Fin (card D (suc (suc n)))) → cofibskelQuot n
    -- bouquetFun2Inl n (inl x) = inl tt
    -- bouquetFun2Inl n (inr (x , north)) = inr (inr (inl (inr x)))
    -- bouquetFun2Inl n (inr (x , south)) = inr (inr (inl (inr x)))
    -- bouquetFun2Inl n (inr (x , merid a i)) =
    --   ({!!}
    --   ∙ push {!!} -- (inl (inr {!α D (suc (suc n)) (x , a)!})) -- push (inl ?(inr {!!})) -- push (sinl n (α D (suc (suc n)) (x , a)) )
    --   ∙ {!!} -- refl
    --   ∙ (λ i → inr (push ((inl (inr x)) , Iso.fun (IsoSphereSusp (suc n))  a) i))
    --   ∙ refl) i
    -- {-
    --   ({!!}
    --   ∙ (λ i → inr (push {!!} (~ i))) -- (push {! (α D (suc (suc n)) (x , a))!} -- push (inl (inr (inr {!x!})))
    --   ∙ {!!}
    --    ∙ (λ i → inr (push ((inl (inr x)) , (Iso.fun (IsoSphereSusp (suc n)) a)) i))
    --    ∙) i
    --    -}
    -- bouquetFun2Inl n (push a i) = {!!}

    -- bouquetFunInv?L : (n : ℕ) → pushoutA terminalCW f (suc (suc n))
    --                            → SplitBouquet (suc (suc n)) zero (card D (suc (suc n))) (card B (suc n))
    -- bouquetFunInv?L n (inl x) = inr (inl tt)
    -- bouquetFunInv?L n (inr x) = inl (inr (inl tt))
    -- bouquetFunInv?L n (push a i) = (sym (push tt) ∙ λ i → inl (push tt i)) i

    -- bouquetFunInv?LVanishFull : (n : ℕ) (x : _)
    --   → bouquetFunInv?L n x ≡ inr (inl tt)
    -- bouquetFunInv?LVanishFull n (inl x) = refl -- 
    -- bouquetFunInv?LVanishFull n (inr x) = sym (sym (push tt)  ∙ λ i → inl (push tt i))
    -- bouquetFunInv?LVanishFull n (push a i) j = (sym (push tt)  ∙ λ i → inl (push tt i)) (i ∧ ~ j)

    -- bouquetFunInv?LVanish : (n : ℕ) (x : _) (a : _)
    --   → bouquetFunInv?L n (pushoutMapₛ terminalCW f (suc n) (inr x , a))
    --   ≡ inr (inr (x , north))
    -- bouquetFunInv?LVanish n x north i = inr (push x i)
    -- bouquetFunInv?LVanish n x south i = (sym (sym (push tt) ∙ λ i → inl (push tt i)) ∙ λ i → inr (push x i)) i
    -- bouquetFunInv?LVanish n x (merid a i) j =
    --    hcomp (λ k → λ {(i = i0) → inr (push x (j ∧ k))
    --                   ; (i = i1) → compPath-filler (sym (sym (push tt) ∙ λ i → inl (push tt i)))
    --                                                 (λ i → inr (push x i)) k j
    --                   ; (j = i0) → bouquetFunInv?L n (pushoutMapₛ-filler terminalCW f (suc n) x a i k)
    --                   ; (j = i1) → inr (push x k)})
    --          (((sym (push tt) ∙ λ i → inl (push tt i))) (i ∧ ~ j))

    -- bouquetFunInv? : (n : ℕ) → cofibskelQuot n
    --                          → SplitBouquet (suc (suc n)) zero (card D (suc (suc n))) (card B (suc n))
    -- bouquetFunInv? n (inl x) = inl (inr (inl tt))
    -- bouquetFunInv? n (inr (inl x)) = bouquetFunInv?L n x
    -- bouquetFunInv? n (inr (inr (inl (inr x)))) = inl (inr (inr (x , north)))
    -- bouquetFunInv? n (inr (inr (inr x))) = inr (inr (x , north))
    -- bouquetFunInv? n (inr (push (inl (inr x) , y) i)) =
    --   inl (inr ((push x ∙ λ i → inr (x , σS (Iso.inv (IsoSphereSusp (suc n)) y) i)) i))
    -- bouquetFunInv? n (inr (push (inr x , a) i)) =
    --   (bouquetFunInv?LVanishFull n (pushoutMapₛ terminalCW f (suc n) (inr x , a))
    --   ∙ λ i → inr ((push x ∙ λ i → inr (x , σS (Iso.inv (IsoSphereSusp (suc n)) a) i)) i)) i
    -- bouquetFunInv? n (push a i) =
    --   (bouquetFunInv?LVanishFull n (invEq (Iso-cofibskel' n) a)
    --   ∙ (sym (push tt)  ∙ λ i → inl (push tt i))) (~ i)

    -- topSqCommL : (n : ℕ) (x : _) →
    --   bouquetFun1' (suc (suc n)) (bouquetFunInv?L n x) ≡ fst (cofibskelQuot≃ n) (inr (inl x))
    -- topSqCommL n (inl x) = push (inl tt)
    -- topSqCommL n (inr x) = push (inr x)
    -- topSqCommL n (push a i) j =
    --   hcomp (λ k → λ {(i = i0) → push (inl tt) j
    --                  ; (i = i1) → push (push a k) j
    --                  ; (j = i0) → bouquetFun1' (suc (suc n)) (compPath-filler' (sym (push tt)) (λ i → inl (push tt i)) k i)
    --                  ; (j = i1) → inr (CW↪ cofibCWskel (suc (suc n)) ((push a) (i ∧ k)))})
    --     (push (inl tt) j)

    -- topSqComm : (n : ℕ) (x : _) → bouquetFun1' (suc (suc n)) (bouquetFunInv? n x) ≡ fst (cofibskelQuot≃ n) x
    -- topSqComm n (inl x) = refl
    -- topSqComm n (inr (inl x)) = topSqCommL n x
    -- topSqComm n (inr (inr (inl (inr x)))) = ({!!} ∙ push (inr {!x!})) ∙ {!Iso.inv (IsoSucSphereSusp n) north!}
    --   ∙ cong (fst (cofibskelQuot≃ n)) (push {!!} ∙ {!!} ∙ λ i → inr (push ((inl (inr x)) , north) i))
    -- topSqComm n (inr (inr (inr x))) = {!!}
    -- topSqComm n (inr (push a i)) = {!!}
    -- topSqComm n (push (inl x) i) = {!!}
    -- topSqComm n (push (inr x) i) = {!x!}
    -- topSqComm n (push (push a i₁) i) = {!a!}

    -- bouquetFun2 : (n : ℕ) → SplitBouquet (suc (suc n)) zero (card D (suc (suc n))) (card B (suc n))
    --                        → cofibskelQuot n
    -- bouquetFun2 n (inl (inl x)) = inl tt
    -- bouquetFun2 n (inl (inr x)) = bouquetFun2Inl n x
    -- bouquetFun2 n (inl (push a i)) = inl tt
    -- bouquetFun2 n (inr (inl x)) = inl tt
    -- bouquetFun2 n (inr (inr x)) = {!snd x!}
    -- bouquetFun2 n (inr (push a i)) = {!pushoutMidCells terminalCW f (suc (suc n))!}
    -- bouquetFun2 n (push a i) = {!!}

    -- cofib→wedgeInr : (n : ℕ) → cofibskel' (suc n) → (QuotCW∙ D (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc n))
    -- cofib→wedgeInr n (inl x) = inl (inl tt)
    -- cofib→wedgeInr n (inr (inl (inr x))) = inl (inr (inr x))
    -- cofib→wedgeInr n (inr (inr x)) = inr north
    -- cofib→wedgeInr n (push (inl (inr x) , b) i) =
    --   ((λ i → inl (push (α D (suc (suc n)) (x , Iso.inv (IsoSphereSusp (suc n)) b)) i)) ∙ (λ i → inl (inr (push (x , Iso.inv (IsoSphereSusp (suc n)) b) i)))) i
    -- cofib→wedgeInr n (push (inr x , b) i) = (push tt ∙ λ i → inr (toSusp (_ , inl tt) (haha b x) i)) i
    --   where
    --   haha : (x : Susp (S₊ n)) (y : A B (suc n)) → QuotCW B (suc n)
    --   haha north y = inl tt
    --   haha south y = inr (inr y)
    --   haha (merid a i) y =
    --     (push (α B (suc n) (y , a)) ∙ λ i → inr ((push (y , a)) i)) i

    -- cofib→wedge : (n : ℕ) → cofibskelQuot n → (QuotCW∙ D (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc n))
    -- cofib→wedge n (inl x) = inl (inl tt)
    -- cofib→wedge n (inr x) = cofib→wedgeInr n x
    -- cofib→wedge n (push a i) = inl (inl tt)

    -- leftSquareComm-inr : (n : ℕ) (x : cofibskel' (suc n))
    --   → Pushout→Bouquet (suc (suc n))
    --   (card cofibCWskel (suc (suc n))) (α cofibCWskel (suc (suc n)))
    --   (e cofibCWskel (suc (suc n)))
    --   (fst (e cofibCWskel (suc (suc n)))
    --    (fst (invEquiv (Iso-cofibskel' (suc n))) x))
    --   ≡
    --   invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
    --   (bouquetFunInv (suc n) (cofib→wedgeInr n x))
    -- leftSquareComm-inr n x = {!(bouquetFunInv (suc n) (cofib→wedgeInr n x))!}

    -- -- leftSquareComm : (n : ℕ) (x : cofibskelQuot n)
    -- --   → BouquetFuns.CTB (suc (suc n)) (card cofibCWskel (suc (suc n)))
    -- --           (α cofibCWskel (suc (suc n))) (e cofibCWskel (suc (suc n)))
    -- --             (cofibskelQuot≃ n .fst x)
    -- --   ≡ invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n))) (bouquetFunInv (suc n) (cofib→wedge n x))
    -- -- leftSquareComm n (inl x) = refl
    -- -- leftSquareComm n (inr x) = leftSquareComm-inr n x
    -- -- leftSquareComm n (push a i) = {!!}
    -- --   where
    -- --   CTBL : (n : ℕ) → _
    -- --   CTBL n = BouquetFuns.CTB (suc (suc n))
    -- --                         (card cofibCWskel (suc (suc n))) (α cofibCWskel (suc (suc n)))
    -- --                           (e cofibCWskel (suc (suc n)))

    -- --   lem : Square (λ i → CTBL n (cofibskelQuot≃ n .fst (push a i)))
    -- --                (cong (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
    -- --                     ∘ (bouquetFunInv (suc n)) ∘ (cofib→wedge n)) (push a))
    -- --         refl (leftSquareComm-inr n (cofibskel'↑ n a))
    -- --   lem = (cong (cong (CTBL n)) (sym (rUnit (push (PushoutPushoutMap→PushoutA terminalCW f n a))))
    -- --       ∙ {!secEq (e cofibCWskel (suc (suc n)))!})
    -- --       ◁ {!!}




