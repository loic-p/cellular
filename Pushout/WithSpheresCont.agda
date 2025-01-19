{-# OPTIONS --cubical --lossy-unification --allow-unsolved-metas #-}
module Pushout.WithSpheresCont where

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


open import Pushout.WithSpheres
open import Pushout.BouquetFunsGen

-- invSides-filler-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → (i j k : _) → A
-- invSides-filler-filler {x = x} p q i j k =
--   hfill (λ k → λ { (i = i0) → p (k ∧ j)
--                  ; (i = i1) → q (~ j ∧ k)
--                  ; (j = i0) → q (i ∧ k)
--                  ; (j = i1) → p (~ i ∧ k)})
--         (inS x)
--         k

module _ {ℓ ℓ'} (A : Pointed ℓ) {B : Pointed ℓ'} (f g : Susp∙ (typ A) →∙ B)
  where
  cong-·Susp-meridPt : cong (·Susp A f g .fst) (merid (pt A)) ≡ refl
  cong-·Susp-meridPt =
    cong₂ _∙_ (h _ _ _ (sym (cong (cong (fst f)) (rCancel (merid (pt A))))))
              (h _ _ _ (sym (cong (cong (fst g)) (rCancel (merid (pt A))))))
    ∙ sym (rUnit refl)
    where
    h : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) (q : y ≡ y)
      → refl ≡ q
      → p ∙∙ q ∙∙ sym p ≡ refl
    h = J> (J> (sym (rUnit refl)))

  Susp∙toSusp : (a : _) → cong (·Susp A f g .fst) (toSusp A a) ≡ cong (·Susp A f g .fst) (merid a)
  Susp∙toSusp a = cong-∙ (·Susp A f g .fst)  _ _
    ∙ cong₂ _∙_ refl (cong sym (cong-·Susp-meridPt)) ∙ sym (rUnit _)

  ·toSusp : (a : _) → toSusp B (·Susp A f g .fst a) ≡ toSusp B (fst f a) ∙ toSusp B (fst g a)
  ·toSusp = {!!}

⋁→Homogeneous≡' : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'}  {C : Type ℓ''}
  (h : (c : C) → isHomogeneous (C , c))
  (f g : A ⋁ B →  C)
  → ((x : _) → f (inl x) ≡ g (inl x))
  → ((x : _) → f (inr x) ≡ g (inr x))
  → (x : _) → f x ≡ g x
⋁→Homogeneous≡' {A = A} {B = B} {C = C} h f g idl idr =
  λ { (inl x) i → main i .fst (inl x)
    ; (inr x) → idr x
    ; (push a i) j
      → hcomp (λ k → λ {(i = i0) → main j .fst (inl (pt A))
                       ; (i = i1) → idr (pt B) (j ∧ k)
                       ; (j = i0) → f (push tt i)
                       ; (j = i1) → compPath-filler (cong g (push tt))
                                      (sym (idr (pt B))) (~ k) i})
              (main j .snd i)}
  where
  filler = doubleCompPath-filler
             (cong g (push tt)) (sym (idr (pt B))) (sym (cong f (push tt)))
  
  F G : (fst A ⊎ fst B , inl (pt A)) →∙ (C , f (inr (pt B)))
  fst F = ⊎.rec (f ∘ inl) (f ∘ inr)
  snd F = cong f (push tt)
  fst G = ⊎.rec (g ∘ inl) (g ∘ inr)
  snd G = cong g (push tt) ∙ sym (idr (pt B))

  main : F ≡ G
  main = →∙Homogeneous≡ (h _) (funExt (⊎.elim idl idr))

module _ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') where
  ⋁→Susp : Susp (A ⋁ B) → Susp∙ (typ A) ⋁ Susp∙ (typ B)
  ⋁→Susp north = inl north
  ⋁→Susp south = inl north
  ⋁→Susp (merid (inl x) i) = inl (toSusp A x i)
  ⋁→Susp (merid (inr x) i) = (push tt ∙∙ (λ i → inr (toSusp B x i)) ∙∙ sym (push tt)) i
  ⋁→Susp (merid (push a i) j) = lem i j
    where
    lem : Path (Path (Susp∙ (typ A) ⋁ Susp∙ (typ B)) _ _)
               (λ i → inl (toSusp A (pt A) i))
               (push tt ∙∙ (λ i → inr (toSusp B (pt B) i)) ∙∙ sym (push tt))
    lem = (λ j i → inl (rCancel (merid (pt A)) j i))
        ∙∙ sym (∙∙lCancel _)
        ∙∙ cong₃ _∙∙_∙∙_ refl (λ j i → inr (rCancel (merid (pt B)) (~ j) i)) refl

  Susp→⋁ : (Susp∙ (typ A) ⋁ Susp∙ (typ B)) → Susp (A ⋁ B)
  Susp→⋁ (inl x) = suspFun inl x
  Susp→⋁ (inr x) = suspFun inr x
  Susp→⋁ (push a i) = north

  SuspWedgeIso : Iso (Susp (A ⋁ B)) (Susp∙ (typ A) ⋁ Susp∙ (typ B))
  Iso.fun SuspWedgeIso = ⋁→Susp
  Iso.inv SuspWedgeIso = Susp→⋁
  Iso.rightInv SuspWedgeIso (inl north) = refl
  Iso.rightInv SuspWedgeIso (inl south) j = inl (merid (pt A) j)
  Iso.rightInv SuspWedgeIso (inl (merid a i)) j = inl (compPath-filler (merid a) (sym (merid (pt A))) (~ j) i)
  Iso.rightInv SuspWedgeIso (inr north) = push tt
  Iso.rightInv SuspWedgeIso (inr south) = push tt ∙ λ i → inr (merid (pt B) i)
  Iso.rightInv SuspWedgeIso (inr (merid a i)) j =
    hcomp (λ k → λ {(i = i0) → push tt (j ∨ ~ k)
                   ; (i = i1) → compPath-filler' (push tt) (λ i → inr (merid (pt B) i)) k j
                   ; (j = i0) → doubleCompPath-filler (push tt) (λ i → inr (toSusp B a i)) (sym (push tt)) k i
                   ; (j = i1) → inr (merid a i)})
          (inr (compPath-filler (merid a) (sym (merid (pt B))) (~ j) i))
  Iso.rightInv SuspWedgeIso (push a i) j = push tt (i ∧ j)
  Iso.leftInv SuspWedgeIso north = refl
  Iso.leftInv SuspWedgeIso south = merid (inl (pt A))
  Iso.leftInv SuspWedgeIso (merid a i) j =
    (h a ◁ symP (compPath-filler (merid a) (sym (merid (inl (pt A)))))) j i
    where
    h : (a : _) → cong Susp→⋁ (cong ⋁→Susp (merid a)) ≡ toSusp (_ , inl (pt A)) a
    h = ⋁→Homogeneous≡' (λ _ → isHomogeneousPath _ _) _ _
      (λ x → cong-∙ (Susp→⋁ ∘ inl) _ _)
      (λ x → cong-∙∙ Susp→⋁ (push tt) _ (sym (push tt))
         ∙ sym (rUnit (λ i → Susp→⋁ (inr (toSusp B x i))))
         ∙ cong-∙ (Susp→⋁ ∘ inr) _ _
         ∙ cong₂ _∙_ refl (cong (sym ∘ merid) (sym (push tt))))

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

  module _ {B' D' : CWskel ℓ-zero}
    (f : cellMap (strictCWskel B') (strictCWskel D')) where
    private
      B = strictCWskel B'
      D = strictCWskel D'
      C = UnitCWskel

    open MIAU f


    bouquetFun1 : (n : ℕ) → SphereBouquet n (Fin (card cofibCWskel n)) → QuotCW cofibCWskel n
    bouquetFun1 n = BouquetFuns.BTC n (card cofibCWskel n) (α cofibCWskel n) (e cofibCWskel n)

    bouquetFun← : (n : ℕ) → QuotCW cofibCWskel n → SphereBouquet n (Fin (card cofibCWskel n))
    bouquetFun← n = BouquetFuns.CTB n (card cofibCWskel n) (α cofibCWskel n) (e cofibCWskel n)

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

    cofibskelQuot≃ : (n : ℕ) → cofibskelQuot n ≃ QuotCW cofibCWskel (suc (suc n))
    cofibskelQuot≃ n =
      pushoutEquiv _ _ _ _
      (invEquiv (Iso-cofibskel' n)) (idEquiv _) (invEquiv (Iso-cofibskel' (suc n)))
      (λ _ _ → tt) (funExt λ x → refl)

    cofib→wedgeInrσ : (n : ℕ) (x : S₊ n) (y : A B n) → QuotCW B n
    cofib→wedgeInrσ n x y = preBTC n (card B n) (α B n) (e B n) y .fst x

    cofib→wedgeInrσmerid : (n : ℕ) (y : _)
      → cong (λ x → cofib→wedgeInrσ (suc (suc n)) x y) (merid (ptSn (suc n))) ≡ refl
    cofib→wedgeInrσmerid n y =
      cong₃ _∙∙_∙∙_ refl (λ j i → inr (rCancel (push (y , ptSn (suc n))) j i)) refl ∙ ∙∙lCancel _

    cofib→wedgeInr : (n : ℕ) → cofibskel' (suc n) → (QuotCW∙ D (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc n))
    cofib→wedgeInr n (inl x) = inl (inl tt)
    cofib→wedgeInr n (inr (inl (inr x))) = inl (inr (inr x))
    cofib→wedgeInr n (inr (inr x)) = inr north
    cofib→wedgeInr n (push (inl (inr x) , b) i) =
      ((λ i → inl (push (α D (suc (suc n)) (x , b)) i)) ∙ (λ i → inl (inr (push (x , b) i)))) i
    cofib→wedgeInr n (push (inr x , b) i) =
      (push tt ∙ λ i → inr (toSusp (_ , inl tt) (cofib→wedgeInrσ (suc n) b x) i)) i

    cofib→wedge : (n : ℕ) → cofibskelQuot n → (QuotCW∙ D (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc n))
    cofib→wedge n (inl x) = inl (inl tt)
    cofib→wedge n (inr x) = cofib→wedgeInr n x
    cofib→wedge n (push a i) = inl (inl tt)

    private
      leftSquareComm-inr-inr : (n : ℕ) (w : _)
        → Pushout→Bouquet (suc (suc n))
        (card cofibCWskel (suc (suc n))) (α cofibCWskel (suc (suc n)))
        (e cofibCWskel (suc (suc n)))
        (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun (inr w))
        ≡
        invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
        (bouquetFunInv (suc n) (cofib→wedgeInr n (inr w)))
      leftSquareComm-inr-inr n (inl (inr x)) = refl
      leftSquareComm-inr-inr n (inr x) = sym (push (Iso.fun Iso-Fin⊎Fin-Fin+ (inr x)))

      leftSquareComm-inr : (n : ℕ) (x : cofibskel' (suc n))
        → Pushout→Bouquet (suc (suc n))
        (card cofibCWskel (suc (suc n))) (α cofibCWskel (suc (suc n)))
        (e cofibCWskel (suc (suc n)))
        (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun x)
        ≡
        invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
        (bouquetFunInv (suc n) (cofib→wedgeInr n x))
      leftSquareComm-inr n (inl x) = refl
      leftSquareComm-inr n (inr x) = leftSquareComm-inr-inr n x
      leftSquareComm-inr n (push (w , x) i) j = main n x w j i
        where
        PB : (n : ℕ) → _
        PB n = Pushout→Bouquet (suc (suc n))
                      (card cofibCWskel (suc (suc n))) (α cofibCWskel (suc (suc n)))
                      (e cofibCWskel (suc (suc n)))

        pf : (n : ℕ) (x : _ ) (w : _)
          → Square (push (invEq (finSplit3≃ _ _ _) w)
                         ∙ (λ i → inr ((invEq (finSplit3≃ _ _ _) w , σSn (suc n) x i))))
                    (λ i → invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
                                   (bouquetFunInv (suc n) (cofib→wedgeInr n (push (w , x) i))))
                   refl (leftSquareComm-inr-inr n w)
        pf n x (inl (inr s)) =
            lUnit _
          ∙ cong₂ _∙_ refl (sym (cong-∙ (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))) _ _))
          ∙ sym (cong-∙ (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n))) ∘ bouquetFunInv (suc n)) _ _)
        pf n x (inr s) =
            refl
          ◁ sqLem _ _ (pfMain n x s)
          ▷ (lUnit _
          ∙ cong₂ _∙_
              (rUnit (λ _ → inl tt)
              ∙ sym (cong-∙ (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))) (λ i → inl (push tt (~ i))) (push tt)))
               ((rUnit _
               ∙ cong₂ _∙_ refl (λ _ _ → inl tt))
               ∙ sym (cong-∙ (λ w → invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
                       (bouquetFunInv (suc n) (inr w))) (merid (cofib→wedgeInrσ (suc n) x s)) (sym (merid (inl tt)))))
          ∙ sym (cong-∙ (λ w → invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
                   (bouquetFunInv (suc n) w)) (push tt)
                     (λ i → inr ((merid (cofib→wedgeInrσ (suc n) x s) ∙ sym (merid (inl tt))) i))))
           where
           open import Cubical.Foundations.Equiv.HalfAdjoint
           sqLem : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) {z : A}
                   {q : y ≡ z} {w : A} {r : z ≡ w} {l : x ≡  w}
                → Square q l (sym p) r → Square (p ∙ q) l refl r
           sqLem = J> λ sq → sym (lUnit _) ◁ sq

           module _ (n : ℕ) where
             woo = Iso.fun (sphereBouquetIso (suc (suc n)) {a = zero} {card D (suc (suc n))} {card B (suc n)})
             waa = sumSphereBouquet→SplitBouquet (suc (suc n)) {a = zero} {card D (suc (suc n))} {card B (suc n)}
             wowa = waa ∘ woo          
             wii = SplitBouquet→sumSphereBouquet (suc (suc n)) {a = zero} {card D (suc (suc n))} {card B (suc n)}
             wiiEq : _ ≃ _
             wiiEq = compEquiv
               (isoToEquiv (sphereBouquetIso (suc (suc n)) {a = zero}
                 {card D (suc (suc n))} {card B (suc n)}))
               (isoToEquiv (Iso-sumSphereBouquet-SplitBouquet (suc (suc n))))

           pfLem : (n : ℕ) (x : _ ) (s : _)
             → Square (λ i₁ → wowa n (inr (invEq (finSplit3≃ zero (card D (suc (suc n))) _) (inr s) , σSn (suc n) x i₁)))
                            (cong (λ r → wowa n
                              (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
                                           (bouquetFunInv (suc n) (inr r))))
                             (merid (cofib→wedgeInrσ (suc n) x s)))
                             (cong (wowa n) (leftSquareComm-inr-inr n (inr s)))
                             (cong (wowa n) (leftSquareComm-inr-inr n (inr s)))
           pfLem n x s i j =
             hcomp (λ k → λ {(i = i0) → waa n (inr (secEq (finSplit3≃ zero _ _) (inr s) (~ k) , σSn (suc n) x j))
                            ; (i = i1) → waa n (Iso.rightInv (sphereBouquetIso (suc (suc n)))
                                            (SplitBouquet→sumSphereBouquet (suc (suc n)) (inr
                                              (Bouquet→ΩBouquetSusp (Fin (card B (suc n))) (λ _ → S₊∙ (suc n))
                                               (BouquetFuns.CTB (suc n) (card B (suc n)) (α B (suc n))
                                                (e B (suc n)) (cofib→wedgeInrσ (suc n) x s)) j))) (~ k))
                            ; (j = i0) → waa n (push (secEq (finSplit3≃ zero _ _) (inr s) (~ k)) (~ i))
                            ; (j = i1) → waa n (push (secEq (finSplit3≃ zero _ _) (inr s) (~ k)) (~ i))})
                   (hcomp (λ k → λ {(i = i0) → inr (doubleCompPath-filler (push s)
                                                     (λ i → inr (s , σSn (suc n) x i))
                                                     (sym (push s)) (~ k) j)
                            ; (i = i1) → Iso.rightInv (Iso-sumSphereBouquet-SplitBouquet (suc (suc n))
                                                        {a = zero} {card D (suc (suc n))} {card B (suc n)})
                                                        (inr ((Bouquet→ΩBouquetSusp (Fin (card B (suc n)))
                                                              (λ _ → S₊∙ (suc n))
                                                              (BouquetFuns.CTB (suc n) (card B (suc n)) (α B (suc n))
                                                               (e B (suc n)) (cofib→wedgeInrσ (suc n) x s))) j)) (~ k)
                            ; (j = i0) → compPath-filler'' (push tt) (λ i → inr (push s i)) k (~ i)
                            ; (j = i1) → compPath-filler'' (push tt) (λ i → inr (push s i)) k (~ i)})
                       (inr (Bouquet→ΩBouquetSusp (Fin (card B (suc n)))
                              (λ _ → S₊∙ (suc n))
                                (Iso.rightInv (BouquetIso-gen (suc n)
                                  (card B (suc n)) (α B (suc n)) (e B (suc n))) (inr (s , x)) (~ i)) j)))

           pfMain : (n : ℕ) (x : _ ) (s : _)
             → Square (λ i₁ → inr (invEq (finSplit3≃ zero (card D (suc (suc n))) _) (inr s) , σSn (suc n) x i₁))
                            (cong (λ r → invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
                                           (bouquetFunInv (suc n) (inr r)))
                             (merid (cofib→wedgeInrσ (suc n) x s)))
                             (leftSquareComm-inr-inr n (inr s))
                             (leftSquareComm-inr-inr n (inr s))
           pfMain n x s i j =
             hcomp (λ k → λ {(i = i0) → retEq (wiiEq n) (inr (invEq (finSplit3≃ zero (card D (suc (suc n))) _)
                                                               (inr s) , σSn (suc n) x j)) k
                            ; (i = i1) → retEq (wiiEq n)
                              (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
                                  (bouquetFunInv (suc n) (inr (merid (cofib→wedgeInrσ (suc n) x s) j)))) k
                            ; (j = i0) → retEq (wiiEq n) (push (Iso.fun Iso-Fin⊎Fin-Fin+ (inr s)) (~ i)) k
                            ; (j = i1) → retEq (wiiEq n) (push (Iso.fun Iso-Fin⊎Fin-Fin+ (inr s)) (~ i)) k})
               (invEq (wiiEq n) (pfLem n x s i j))

        main : (n : ℕ) (x : _ ) (w : _)
          → Square (λ i → PB n (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun (push (w , x) i)))
                    (λ i → invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
                                   (bouquetFunInv (suc n) (cofib→wedgeInr n (push (w , x) i))))
                   refl (leftSquareComm-inr-inr n w)
        main n x w = (cong-∙ (PB n) _ _ ∙ (sym (lUnit _)))
                   ◁ pf n x w


    
    leftSquareComm : (n : ℕ) (x : cofibskelQuot n)
      → BouquetFuns.CTB (suc (suc n)) (card cofibCWskel (suc (suc n)))
              (α cofibCWskel (suc (suc n))) (e cofibCWskel (suc (suc n)))
                (cofibskelQuot≃ n .fst x)
      ≡ invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
               (bouquetFunInv (suc n) (cofib→wedge n x))
    leftSquareComm n (inl x) = refl
    leftSquareComm n (inr x) =
      cong (Pushout→Bouquet (suc (suc n)) (card cofibCWskel (suc (suc n)))
           (α cofibCWskel (suc (suc n))) (e cofibCWskel (suc (suc n))))
           (cong (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun)
                 (secEq (eCWPushout terminalCW f (suc n)) x))
      ∙ leftSquareComm-inr n x
    leftSquareComm n (push a i) j =
      hcomp (λ k → λ {(i = i0) → inl tt
                     ; (j = i0) → hh (~ k) i
                     ; (j = i1) → inl tt})
       (W (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun
         ((isEquivPushoutA→PushoutPushoutMapStrict terminalCW f
          (suc n) .fst (inl (PushoutPushoutMap→PushoutA terminalCW f n a))
          (~ i ∨ j)))))
      where

      secCompEquiv : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
        → (e : A ≃ B) (d : B ≃ C) (x : _) → secEq (compEquiv e d) x ≡ cong (fst d) (secEq e (invEq d x)) ∙ secEq d x
      secCompEquiv e d x = refl

      W = Pushout→Bouquet (suc (suc n)) (card cofibCWskel (suc (suc n)))
                       (α cofibCWskel (suc (suc n))) (e cofibCWskel (suc (suc n)))
      L = BouquetFuns.CTB (suc (suc n)) (card cofibCWskel (suc (suc n)))
            (α cofibCWskel (suc (suc n))) (e cofibCWskel (suc (suc n)))
      hh : cong L (push (PushoutPushoutMap→PushoutA terminalCW f n a) ∙ refl)
         ≡ cong W (cong (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun)
                        (sym ((secEq (eCWPushout terminalCW f (suc n)))
                          (inl (PushoutPushoutMap→PushoutA terminalCW f n a)))))
      hh = cong-∙ L _ _ ∙ sym (rUnit _) ∙ cong-∙∙ W _ _ _ ∙ sym (rUnit _)


  ------ STEP 2

    cofibskelQuotSusp : (n : ℕ) → cofibskelQuot n  → Susp (cofibskel' n)
    cofibskelQuotSusp n (inl x) = north
    cofibskelQuotSusp n (inr x) = south
    cofibskelQuotSusp n (push a i) = merid a i

    cofibskelQuot↓ : (n : ℕ) → cofibskelQuot (suc n)  → Susp (cofibskelQuot n)
    cofibskelQuot↓ n x = suspFun inr (cofibskelQuotSusp (suc n) x)

    module _ (n : ℕ) where
      multMap-inr-inl : Susp∙ (QuotCW B (suc (suc n))) →∙ (Susp∙ (QuotCW D (suc (suc n))) ⋁∙ₗ Susp∙ (Susp (QuotCW B (suc n))))
      fst multMap-inr-inl x = inl (suspFun (prefunctoriality.fn+1/fn (suc (suc (suc n)))
                                   (cellMap→finCellMap (suc (suc (suc n))) f ) flast) x)
      snd multMap-inr-inl = refl

      multMap-inr-inr : Susp∙ (QuotCW B (suc (suc n))) →∙ (Susp∙ (QuotCW D (suc (suc n))) ⋁∙ₗ Susp∙ (Susp (QuotCW B (suc n))))
      fst multMap-inr-inr x = inr (suspFun (suspFun inr ∘ δ (suc (suc n)) B) x)
      snd multMap-inr-inr = sym (push tt)

      multMap : (QuotCW∙ D (suc (suc (suc n)))) ⋁ Susp∙ (QuotCW B (suc (suc n)))
                        → (Susp∙ (QuotCW D (suc (suc n))) ⋁ Susp∙ (Susp (QuotCW B (suc n))))
      multMap (inl x) = inl (suspFun inr (δ (suc (suc (suc n))) D x))
      multMap (inr x) = ·Susp (QuotCW∙ B (suc (suc n)))
        multMap-inr-inl multMap-inr-inr .fst x
      multMap (push a i) = inl north


    multMap≡'Inl : (n : ℕ) (x : _)
      →   (suspFun (cofib→wedge n) (cofibskelQuot↓ n (inr (inl x))))
      ≡ Iso.inv (SuspWedgeIso _ _) (multMap n (cofib→wedge (suc n) (inr (inl x))))
    multMap≡'Inl n x = sym (merid (cofib→wedgeInr n (fst (Iso-cofibskel' (suc n)) x)))

    multMap≡'Inr : (n : ℕ) (x : _)
      →   (suspFun (cofib→wedge n) (cofibskelQuot↓ n (inr (inr x))))
      ≡ Iso.inv (SuspWedgeIso _ _) (multMap n (cofib→wedge (suc n) (inr (inr x))))
    multMap≡'Inr n (inl (inr x)) = refl
    multMap≡'Inr n (inr x) = sym (merid (inl (inl tt)))


    

    multMap≡' : (n : ℕ) (x : cofibskelQuot (suc n))
      →   (suspFun (cofib→wedge n) (cofibskelQuot↓ n x))
      ≡ Iso.inv (SuspWedgeIso _ _) (multMap n (cofib→wedge (suc n) x))
    multMap≡' n (inl x) = refl
    multMap≡' n (inr (inl x)) = sym (merid (cofib→wedgeInr n (fst (Iso-cofibskel' (suc n)) x)) )
    multMap≡' n (inr (inr x)) = multMap≡'Inr n x
    multMap≡' n (inr (push (inl (inr x) , b) i)) k = help k i
      where
      cancelLem : (n : ℕ) (x : _) → cofib→wedgeInr n (PushoutA→PushoutPushoutMapR terminalCW f  (suc n) x) ≡ inl (inr x)
      cancelLem n (inl x) i = inl (push x i)
      cancelLem n (inr x) = refl
      cancelLem n (push a i) j =
        compPath-filler' (λ i₂ → inl (push (α D (suc (suc n)) a) i₂))
                         (λ i₂ → inl (inr (push (fst a , snd a) i₂)))
                         (~ j) i

      help : Square refl
        (cong (Iso.inv (SuspWedgeIso _ _))
          (cong (multMap n ∘ cofib→wedge (suc n) ∘ inr) (push (inl (inr x) , b))))
        (sym (merid (cofib→wedgeInr n (fst (Iso-cofibskel' (suc n))
              (inr (α D (suc (suc (suc n))) (x , b)))))))
        refl
      help = (flipSquare (cong (sym ∘ merid) (cancelLem n (α D (suc (suc (suc n))) (x , b)))
           ◁ λ i j → merid (inl (inr (α D (suc (suc (suc n))) (x , b)))) (i ∨ ~ j)))
        ▷ (((λ _ → merid (inl (inr (α D (suc (suc (suc n))) (x , b)))))
        ∙ rUnit _)
        ∙ sym (cong-∙  (Iso.inv (SuspWedgeIso _ _) ∘ multMap n ) _ _))
    multMap≡' n (inr (push (inr x , b) i)) k = {!!} -- help k i
      where
      f1 f2 : (n : ℕ) (x : _) → S₊∙ (suc (suc n)) →∙ (QuotCW∙ D (suc (suc n)) ⋁ Susp∙ (QuotCW B (suc n)) , inr north)
      fst (f1 n x) b = inl (prefunctoriality.fn+1/fn (suc (suc (suc n)))
                             (cellMap→finCellMap (suc (suc (suc n))) f) flast
                               (cofib→wedgeInrσ (suc (suc n)) b x))
      snd (f1 n x) = push tt
      fst (f2 n x) b = inr (suspFun inr (δ (suc (suc n)) B (cofib→wedgeInrσ (suc (suc n)) b x)))
      snd (f2 n x) = refl

      mainSuspLem : (n : ℕ) (x : _) (b : _)
        → cofib→wedgeInr n (fst (Iso-cofibskel' (suc n))
             (pushoutMapₛ terminalCW f (suc (suc n)) (inr x , b)))
        ≡ ·Susp (S₊∙ (suc n)) (f1 n x) (f2 n x) .fst b
      mainSuspLem n x north = push tt
      mainSuspLem n x south = cong (λ w → cofib→wedgeInr n
        (fst (Iso-cofibskel' (suc n))
        (inr
          (∣ f ∣ (suc (suc (suc n))) w)))) (sym (push (x , ptSn (suc n))))
          ∙ cong (cofib→wedgeInr n ∘ fst (Iso-cofibskel' (suc n)) ∘ inr)
                 (sym (comm f (suc (suc n)) (α B (suc (suc n)) (x , ptSn (suc n)))))
         ∙ push tt
      mainSuspLem n x (merid a i) j = {!fst (Iso-cofibskel' (suc n))!}
        where
        rCancelFiller : ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (pr : p ≡ refl)
          → (i j k : _) → A
        rCancelFiller p pf i j k =
          hfill (λ r → λ {(i = i0) → p i0
                         ; (i = i1) → pf (~ r) j
                         ; (j = i0) → pf (~ r) (~ i)
                         ; (j = i1) → pf (~ r) (~ i)})
                 (inS (p i0)) k

        rCancelFiller-coh :  ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (P : p ≡ p) (pr : refl ≡ p)
          → Cube (pr ∙∙ P ∙∙ sym pr) P (λ i j → rCancelFiller p (sym pr) i j i1) pr
               {!!} {!!} --  (λ j i → pr (~ i) (~ j)) λ j i → pr (~ i) (~ j) --  (λ j i → pr i j) λ i j → pr j i --  r i k -- q (pr ∙∙ q ∙∙ sym pr) (λ i j → {!rCancelFiller p (sym pr) i j i1!}) {!!}
        rCancelFiller-coh = {!!}

        F1 : (n : ℕ) (x : _) (i j k : I)
          → QuotCW∙ D (suc (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc (suc n)))
        F1 n x₁ i j k =
          hfill (λ r → λ {(i = i0) → cofib→wedgeInr (suc n)
                                             (doubleCompPath-filler (push (inr x₁ , north))
                                               refl (sym (push (inr x₁ , south))) r (~ j))
                              ; (i = i1) → inr (rCancelFiller _ (rCancel (merid (inl tt))) r j i1)
                              ; (j = i0) → compPath-filler' (push tt)
                                             (λ i → inr (toSusp (_ , inl tt) (inl tt) i)) (~ i) (~ r)
                              ; (j = i1) → compPath-filler' (push tt)
                                             (λ i → inr (toSusp (_ , inl tt) (inl tt) i)) (~ i) (~ r)
                              })
                      (inS (inr north)) k


        LeftInl : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) {q r : y ≡ y}
          (qr : q ≡ r) (qrefl : refl ≡ q) → (i j k : _) → A
        LeftInl p {q = q} {r} qr qrefl i j k =
          hfill (λ k → λ {(i = i0) → p (~ k)
                         ; (i = i1) → qr k j
                         ; (j = i0) → p (i ∨ ~ k)
                         ; (j = i1) → p (i ∨ ~ k)})
                   (inS (qrefl i j)) k


        LEFT : (n : ℕ) (z : _)
          → Square (sym (cong (cofib→wedgeInr n)
                           (PushoutA→PushoutPushoutMapLR terminalCW f (suc n) z ))) -- (λ i j → cofib→wedgeInr n (PushoutA→PushoutPushoutMapLR terminalCW f (suc n) z j i))
                    (λ i → inr (toSusp (QuotCW B (suc n) , inl tt)
                                                (inr z) i))
                    (push tt)
                    (push tt)
        LEFT n (inl x₁) i j =
          LeftInl (push tt)
                  (λ i j → inr (toSusp (QuotCW B (suc n) , inl tt) (push x₁ i) j))
                  (λ j i → inr (rCancel (merid (inl tt)) (~ j) i)) i j i1
        LEFT zero (inr x₁) = {!!}
        LEFT (suc n) (inr x₁) i j =
          hcomp (λ r → λ {(i = i0) → cofib→wedgeInr (suc n)
                                        (doubleCompPath-filler (push (inr x₁ , north))
                                          refl (sym (push (inr x₁ , south))) r (~ j))
                         ; (i = i1) → {!!}
                         {- inr (toSusp (QuotCW B (suc (suc n)) , inl tt)
                                             ((push (α B (suc (suc n)) (x₁ , ptSn (suc n)))
                                             ∙ (λ r → inr (push (x₁ , ptSn (suc n)) r))) r) j)
                                             -}
                         ; (j = i0) → compPath-filler' (push tt) (λ j → inr
                                          (toSusp (Pushout (λ _ → tt) (CW↪ B (suc (suc n))) , inl tt)
                                           (cofib→wedgeInrσ (suc (suc n)) south x₁) j)) (~ i) (~ r)
                         ; (j = i1) → compPath-filler' (push tt) (λ j → inr
                                          (toSusp (Pushout (λ _ → tt) (CW↪ B (suc (suc n))) , inl tt)
                                           (cofib→wedgeInrσ (suc (suc n)) south x₁) j)) (~ i) (~ r) 
                         })
              {!!} -- (F1 n x₁ i j i1)
        LEFT zero (push (a , t) i) = {!a!}
        LEFT (suc n) (push (a , t) i) j k =
          hcomp (λ r → λ { (i = i0) → {!!}
                         ; (i = i1) → {!!}
                         ; (j = i0) → ? -- cofib→wedgeInr (suc n) (PushoutA→PushoutPushoutMapLR-push-filler terminalCW f (suc n) a t i (~ k) r)
                         ; (j = i1) → {!!}
                         ; (k = i0) → {!cofib→wedgeInr (suc n)
                                                 (invSides-filler-filler (push (inr a , north))
                                                   (λ i → inl (inl (∣ f ∣ (suc (suc (suc n))) ( (push (a , t) (~ i)))))) i r (~ j))!}
                         ; (k = i1) → {!cofib→wedgeInr (suc n) (invSides-filler-filler (push (inr a , north))
                                                 (λ i → inl (inl (∣ f ∣ (suc (suc (suc n))) ( (push (a , t) (~ i)))))) r i (~ j))!}})
                {!!}
        {-
          hcomp (λ r → λ { (i = i0) → LeftInl (push tt)
                                           (λ i j → inr (toSusp (QuotCW B (suc (suc n)) , inl tt)
                                                      (push (α B (suc (suc n)) (a , t)) i) j))
                                           (λ j i → inr (rCancel (merid (inl tt)) (~ j) i)) j k r
                         ; (j = i0) → c1 r k i
                         ; (j = i1) → inr (toSusp (QuotCW B (suc (suc n)) , inl tt)
                                           (minilem _ _ (push (a , t)) _ (sym (push (a , ptSn (suc n)))) inr _
                                             (sym (push (α B (suc (suc n)) (a , t))))  _
                                             (sym (push (α B (suc (suc n)) (a , ptSn (suc n))))) r i) k)
                         ; (k = i0) → push tt (j ∨ (~ r ∧ ~ i))
                         ; (k = i1) → push tt (j ∨ (~ r ∧ ~ i))})
            (hcomp (λ r → λ {(i = i0) → inr (rCancelFiller-coh3 _ (sym (rCancel (merid (inl tt)))) r j k)
                         ; (i = i1) → F1 n a j k r
                         ; (j = i0) → SQ k i r -- 
                         ; (j = i1) → inr (rCancelFiller-coh2
                                            _ (sym (rCancel _))
                                            (cong (toSusp (QuotCW B (suc (suc n)) , inl tt))
                                             ((sym (λ i₃ → push (α B (suc (suc n)) (a , t)) (~ i₃)) ∙∙
                                               cong inr* (push (a , t) ∙ (λ i₃ → push (a , ptSn (suc n)) (~ i₃)))
                                               ∙∙ (λ i₃ → push (α B (suc (suc n)) (a , ptSn (suc n))) (~ i₃)))))
                                             r i k)
                         ; (k = i0) → rCancelFiller-coh4 r j i
                         ; (k = i1) → rCancelFiller-coh4 r j i
                         })
                   (SQ k i i0)
                   )
           where --  r k i



           inr* : _ → QuotCW B (suc (suc n))
           inr* = inr

           rCancelFiller-coh2 :  ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (pr : refl ≡ p)  (P : p ≡ p)
             → Cube ((pr ∙∙ P ∙∙ sym pr)) P -- r i k
                     pr (λ r k → rCancelFiller _ (sym pr) r k i1)
                     (λ j i → pr i (~ j)) λ j i → pr i (~ j)
           rCancelFiller-coh2 {x = x} = J> λ P → sym (rUnit P)
             ◁ flipSquare ((λ i _ → P i)
             ▷ λ j i k → rCancelFiller (λ _ → x) refl i k j)

           rCancelFiller-coh3 :  ∀ {ℓ} {A : Type ℓ} {x : A} (p : x ≡ x) (pr : refl ≡ p)
             -- r j k
             → Cube (λ _ _ → x) pr (λ r k → p (~ r)) pr (λ j i → pr (~ i) (~ j)) λ j i → pr (~ i) (~ j) 
           rCancelFiller-coh3 = J> refl


           minilem : ∀ {ℓ} {A B : Type ℓ}
             (x y : A) (ml : x ≡ y) (z : A) (mr : y ≡ z)
             (f : A → B) (b : B) (l : f x ≡ b) (b2 : B) (r : f z ≡ b2)
              → Square (sym l ∙∙ cong f (ml ∙ mr) ∙∙ r) (cong f ml)
                       (sym l) (sym r ∙ sym (cong f mr)) -- Square (l ∙∙ ml ∙ mr ∙∙ r) ml l (sym r ∙ sym mr)
           minilem x = J> (J> λ f → J> (J> ((sym (rUnit _)
             ∙ cong (cong f) (sym (rUnit refl))) ◁ λ j i → rUnit (λ _ → f x) i j)))

           SQ : (i j k : I) → QuotCW∙ D (suc (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc (suc n)))
            
           SQ i j k =
             hfill (λ k → λ {(i = i0) → compPath-filler' (push tt)
                                             (λ i → inr (toSusp (_ , inl tt) (inl tt) i)) j (~ k)
                            ; (i = i1) → compPath-filler' (push tt)
                                             (λ i → inr (toSusp (_ , inl tt) (inl tt) i)) j (~ k)
                            ; (j = i0) → inr (toSusp (Pushout (λ _ → tt) (CW↪ B (suc (suc n))) , inl tt) (inl tt) (~ k))
                            ; (j = i1) → cofib→wedgeInr (suc n)
                                           (doubleCompPath-filler (push (inr a , north)) (λ _ → inr (inr a))
                                            (λ i₃ → push (inr a , south) (~ i₃)) k i)})
             (inS (inr ((sym (rCancel (merid (inl tt)))
                ∙∙ (λ i → toSusp (_ , inl tt)
                            (cofib→wedgeInrσ (suc (suc n)) (merid t i) a))
                ∙∙ rCancel (merid (inl tt))) j i))) k
             -- k


           rCancelFiller-gen : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) {n : A} (finl : B)
             (pushtt⁻¹ : f n ≡ finl) (p : n ≡ n) (q : refl ≡ p)
             → Cube (λ j i → f n) (λ j i → pushtt⁻¹ (~ (j ∨ ~ i)))
                                      (λ r i → compPath-filler' (sym pushtt⁻¹) (cong f p) i (~ r)) -- (λ r i → SQ i0 i r)
                                      (λ r i →  f (q i (~ r)))
                                      (λ r j → f (q (~ j) (~ r)))
                                      λ r i → compPath-filler' (sym pushtt⁻¹) (cong f p) (~ i) (~ r)
           rCancelFiller-gen f {n = n} = J> (J> λ i j k → compPath-filler' (λ _ → f n) refl (~ j ∧ k) (~ i) )

           rCancelFiller-coh4 :  Cube (λ j i → inr north) (λ j i → push tt (j ∨ ~ i))
                                      (λ r i → SQ i0 i r)
                                      (λ r i →  inr (rCancel (merid (inl tt)) (~ i) (~ r)))
                                      (λ r j → inr (rCancel (merid (inl tt)) j (~ r)))
                                      λ r j → F1 n a j i0 r
           rCancelFiller-coh4 =
             rCancelFiller-gen inr _ (sym (push tt)) _ (sym (rCancel (merid (inl tt))))


           c1 : Cube {A = QuotCW∙ D (suc (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc (suc n)))}
                (λ i j → SQ i j i1)
                (λ i j → cofib→wedgeInr (suc n)
                           (PushoutA→PushoutPushoutMapLR-push-filler terminalCW f (suc n) a t j (~ i) i1))
                (λ r i → push tt (~ r ∧ ~ i)) -- (λ r i → push tt (~ r ∧ ~ i))
                (λ r i → push tt (~ r ∧ ~ i)) -- (λ r i → push tt (~ r ∧ ~ i))
                (λ r k → push tt (~ r)) --  (λ r k → push tt (~ r))
                λ r k → cofib→wedgeInr (suc n)
                           (doubleCompPath-filler (push (inr a , north))
                             refl (sym (push (inr a , south))) i1 (~ k))
           c1 r i j =
             hcomp (λ k → λ {(i = i0) → {!cofib→wedgeInr (suc n)
                                             (PushoutA→PushoutPushoutMapLR-push-filler terminalCW f (suc n) a t
                                              r i1 k)!}
                         ; (i = i1) → {!!}
                         ; (j = i0) → push tt (~ r)
                         ; (j = i1) → cofib→wedgeInr (suc n)
                                        (doubleCompPath-filler (push (inr a , north))
                                          refl (sym (push (inr a , south))) k (~ i))
                         ; (r = i0) → {!SQ i j k!} --  -- 
                         ; (r = i1)
                           → cofib→wedgeInr (suc n)
                                (PushoutA→PushoutPushoutMapLR-push-filler terminalCW f (suc n) a t j (~ i) k)
                         })
                   (compPath-filler' (push tt)
                     (λ ii → inr
                        (toSusp (Pushout (λ _ → tt) (CW↪ B (suc (suc n))) , inl tt)
                         (cofib→wedgeInrσ (suc (suc n)) (merid t (~ i)) a) ii)) r j)
                 where
                 big : {!!}
                 big = {!!}

-}

        -- LEFT : (n : ℕ) (z : _)
        --   → Square (cong (cofib→wedgeInr n)
        --              (PushoutA→PushoutPushoutMapLR terminalCW f (suc n) z))
        --             (λ i → inr (toSusp (QuotCW B (suc n) , inl tt)
        --                                         (inr z) i))
        --             (push tt)
        --             (push tt)
        -- LEFT n (inl x₁) i j =
        --   hcomp (λ r → λ {(i = i0) → push tt (~ r)
        --                  ; (i = i1) → inr (toSusp (QuotCW B (suc n) , inl tt) (push x₁ r) j)
        --                  ; (j = i0) → push tt (i ∨ ~ r)
        --                  ; (j = i1) → push tt (i ∨ ~ r)})
        --           (inr (rCancel (merid (inl tt)) (~ i) j))
        -- LEFT zero (inr x₁) = {!!}
        -- LEFT (suc n) (inr x₁) i j =
        --  hcomp (λ r → λ {(i = i0) → cofib→wedgeInr (suc n)
        --                                 (doubleCompPath-filler (push (inr x₁ , north))
        --                                   refl (sym (push (inr x₁ , south))) i1 j)
        --                  ; (i = i1) → inr (toSusp (QuotCW B (suc (suc n)) , inl tt)
        --                                      ((push (α B (suc (suc n)) (x₁ , ptSn (suc n)))
        --                                      ∙ (λ r → inr (push (x₁ , ptSn (suc n)) r))) r) j)
        --                  ; (j = i0) → push tt i
        --                  ; (j = i1) → push tt i
        --                  })
        --  (hcomp (λ r → λ {(i = i0) → cofib→wedgeInr (suc n)
        --                                 (doubleCompPath-filler (push (inr x₁ , north))
        --                                   refl (sym (push (inr x₁ , south))) r j)
        --                  ; (i = i1) → inr (rCancelFiller _ (rCancel (merid (inl tt))) r j)
        --                  ; (j = i0) → compPath-filler' (push tt)
        --                                 (λ i → inr (toSusp (_ , inl tt) (inl tt) i)) (~ i) (~ r)
        --                  ; (j = i1) → compPath-filler' (push tt)
        --                                 (λ i → inr (toSusp (_ , inl tt) (inl tt) i)) (~ i) (~ r)
        --                  })
        --          (inr north))
        -- LEFT zero (push (a , t) i) = {!a!}
        -- LEFT (suc n) (push (a , t) i) j k =
        --   hcomp (λ r → λ {(j = i0) → {!cofib→wedgeInr (suc n) (PushoutA→PushoutPushoutMapLR-push-filler terminalCW f (suc n) a t i k i0)!}
        --                  ; (j = i1) → inr (toSusp (QuotCW B (suc (suc n)) , inl tt)
        --                                    (minilem _ _ (push (a , t)) _ (sym (push (a , ptSn (suc n)))) inr _
        --                                      (sym (push (α B (suc (suc n)) (a , t))))  _
        --                                      (sym (push (α B (suc (suc n)) (a , ptSn (suc n))))) r i) k)
        --                  ; (k = i0) → push tt (j ∨ (~ r ∧ ~ i))
        --                  ; (k = i1) → push tt (j ∨ (~ r ∧ ~ i))})
        --    {!!}
        --    where
        --    minilem : ∀ {ℓ} {A B : Type ℓ}
        --      (x y : A) (ml : x ≡ y) (z : A) (mr : y ≡ z)
        --      (f : A → B) (b : B) (l : f x ≡ b) (b2 : B) (r : f z ≡ b2)
        --       → Square (sym l ∙∙ cong f (ml ∙ mr) ∙∙ r) (cong f ml)
        --                (sym l) (sym r ∙ sym (cong f mr)) -- Square (l ∙∙ ml ∙ mr ∙∙ r) ml l (sym r ∙ sym mr)
        --    minilem x = J> (J> λ f → J> (J> ((sym (rUnit _)
        --      ∙ cong (cong f) (sym (rUnit refl))) ◁ λ j i → rUnit (λ _ → f x) i j)))
        --    SQ : (i j k : I) → QuotCW∙ D (suc (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc (suc n)))
        --    SQ i j k =
        --      hfill (λ k → λ {(i = i0) → {!!}
        --                     ; (i = i1) → cofib→wedgeInr (suc n)
        --                                    (doubleCompPath-filler (push (inr a , north)) (λ _ → inr (inr a))
        --                                     (λ i₃ → push (inr a , south) (~ i₃)) k j)
        --                     ; (j = i0) → {!!}
        --                     ; (j = i1) → {!!}})
        --      (inS (inr (toSusp (_ , inl tt) (push (α B (suc (suc n)) (a , t)) j) i)))
        --      k
        --    c1 : Cube {!!}
        --      (λ i k → cofib→wedgeInr (suc n)
        --                 (PushoutA→PushoutPushoutMapLR-push-filler terminalCW
        --                   f (suc n) a t i k i1))
        --      (λ j _ → push tt (~ j)) -- (\sym (push tt))
        --      (λ i j → cofib→wedgeInr (suc n)
        --                 (doubleCompPath-filler
        --                   (push (inr a , north)) (λ _ → inr (inr a)) (λ i₃ → push (inr a , south) (~ i₃)) i1 j) )
        --      {!!} -- (λ r i → push tt (~ r ∧ ~ i))
        --      {!!} -- (λ r i → push tt (~ r ∧ ~ i)) -- r i k
        --    c1 = {!!}

        F : (n : ℕ) → _
        F n = prefunctoriality.fn+1/fn (suc (suc (suc n))) (cellMap→finCellMap (suc (suc (suc n))) f) flast
        inl' : _ → QuotCW∙ D (suc (suc n)) ⋁ Susp∙ (QuotCW B (suc n))
        inl' = inl

        cong-f1≡ : (a : _) → cong (f1 n x .fst) (σS a)
                           ≡ cong inl' ({!!}
                                       ∙∙ cong (F n ∘ inr) (push (x , a))
                                       ∙∙ {!!})
        cong-f1≡ a =
          cong-∙ (f1 n x .fst) (merid a) (sym (merid (ptSn (suc n))))
                   ∙ cong₂ _∙_ refl
                     (λ j i → inl (F n (cofib→wedgeInrσmerid n x j (~ i))))
                   ∙ sym (rUnit _)
                   ∙ cong (cong inl') ( 
                     cong-∙∙ (F n) _ _ _
                   ∙ cong₃ _∙∙_∙∙_
                           (λ _ → {!(cong (cofib→wedgeInr n)
                       (PushoutA→PushoutPushoutMapLR terminalCW f (suc n) (α B (suc (suc n)) (x , a))))!}
                       ∙ {!λ i → !})
                           (cong-∙ (F n ∘ inr) (push (x , a)) (sym (push (x , (ptSn (suc n)))))
                           ∙ refl)
                           refl
                   ∙ {!α B ?!})
                   ∙ {!cong (cofib→wedgeInr n)
                       (cong (PushoutA→PushoutPushoutMapR terminalCW f (suc n))
                          ((comm f (suc (suc n)) (α B (suc (suc n)) (x , a)))))
                   ∙ cong (cofib→wedgeInr n)
                      (cong (PushoutA→PushoutPushoutMapR terminalCW f (suc n))
                        (cong (∣ f ∣ (suc (suc (suc n)))) (push (x , a))))!}

        cong-f2≡ : (a : _) → cong (f2 n x .fst) (σS a)
                           ≡ λ i → inr (toSusp (QuotCW B (suc n) , inr (α B (suc (suc n)) (x , ptSn (suc n))))
                                                (inr (α B (suc (suc n)) (x , a))) i)
        cong-f2≡ a = cong-∙ (f2 n x .fst) (merid a) (sym (merid (ptSn (suc n))))
                   ∙ cong₂ _∙_ refl
                      (λ j i → inr (suspFun inr (δ (suc (suc n)) B (cofib→wedgeInrσmerid n x j (~ i)))))
                   ∙ sym (rUnit _)
                   ∙ cong-∙∙ (λ x → inr (suspFun inr (δ (suc (suc n)) B x)))
                              (push (α B (suc (suc n)) (x , a)))
                              (λ i → inr ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) i))
                              (sym (push (α B (suc (suc n)) (x , ptSn (suc n))))) -- _ _ _
                   ∙ doubleCompPath≡compPath _ _ _
                   ∙ cong₂ _∙_ refl (sym (lUnit _))
                   ∙ (λ j → (λ i → inr (merid (inr (α B (suc (suc n)) (x , a))) i))
                          ∙ λ i → inr (merid (inr (α B (suc (suc n)) (x , ptSn (suc n)))) (~ i)))
                     ∙ sym (cong-∙ inr (merid (inr (α B (suc (suc n)) (x , a))))
                                    (sym (merid (inr (α B (suc (suc n)) (x , ptSn (suc n)))))))

        lem2 : cong (cofib→wedgeInr n ∘ fst (Iso-cofibskel' (suc n)))
                      (λ i → pushoutMapₛ terminalCW f (suc (suc n)) (inr x , merid a i))
                   ≡ (cong (cofib→wedgeInr n)
                       (PushoutA→PushoutPushoutMapLR terminalCW f (suc n) (α B (suc (suc n)) (x , a)))
                   ∙ cong (cofib→wedgeInr n)
                       (cong (PushoutA→PushoutPushoutMapR terminalCW f (suc n))
                          ((comm f (suc (suc n)) (α B (suc (suc n)) (x , a))))))
                   ∙ cong (cofib→wedgeInr n)
                      (cong (PushoutA→PushoutPushoutMapR terminalCW f (suc n))
                        (cong (∣ f ∣ (suc (suc (suc n)))) (push (x , a))))
        lem2 = cong-∙∙ (cofib→wedgeInr n ∘ fst (Iso-cofibskel' (suc n))) _ _ _
             ∙ cong₃ _∙∙_∙∙_
                     (λ _  _ → inl (inl tt))
                     (cong-∙∙ (cofib→wedgeInr n) _ _ _
                     ∙ cong₃ _∙∙_∙∙_ (cong-∙  (cofib→wedgeInr n) _ _ ∙ sym (rUnit (λ _ → inl (inl tt))))
                                     (cong-∙ (cofib→wedgeInr n) _ _ ∙ sym (rUnit _))
                                     (cong-∙ (cofib→wedgeInr n ∘ PushoutA→PushoutPushoutMapR terminalCW f (suc n)) _ _
                                     ∙ sym (rUnit _)
                                     ∙ refl))
                     refl
             ∙ cong₂ _∙_ (cong₂ _∙_ refl refl) refl
{-
      help : Square refl
        (cong (Iso.inv (SuspWedgeIso _ _))
          (cong (multMap n ∘ cofib→wedge (suc n) ∘ inr) (push (inr x , b))))
        (sym (merid (cofib→wedgeInr n (fst (Iso-cofibskel' (suc n))
              (pushoutMapₛ terminalCW f (suc (suc n)) (inr x , b))))))
         
        (sym (merid (inl (inl tt))))
      help = compPathL→PathP (cong₂ _∙_ refl (sym (lUnit _))
        ∙ (λ i → toSusp (_ , push tt i)
                   (cofib→wedgeInr n (fst (Iso-cofibskel' (suc n))
                     (pushoutMapₛ terminalCW f (suc (suc n)) (inr x , b)))))
        ∙ cong (toSusp (_ , inr north)) (mainSuspLem n x b)
        ∙ (·toSusp (S₊∙ (suc n)) (f1 n x) (f2 n x) b))
        ▷ (refl
        ∙ refl
        ∙ sym (cong-∙ (Susp→⋁ (_ , inl tt) (_ , north)) _ _
              ∙ cong₂ _∙_ (cong-∙ (Susp→⋁ (_ , inl tt) (_ , north)) _ _
                ∙ cong₂ _∙_ (λ _ → merid (inl (prefunctoriality.fn+1/fn (suc (suc (suc n)))
                                                 (cellMap→finCellMap (suc (suc (suc n))) f)
                                                   flast (cofib→wedgeInrσ (suc (suc n)) b x))))
                            λ _ → sym (merid (inl (inl tt))))
                            (cong-∙∙ (Susp→⋁ (_ , inl tt) (_ , north)) (push tt)
                              (cong (fst (multMap-inr-inr n))
                                    (merid (cofib→wedgeInrσ (suc (suc n)) b x))
                                    ∙ sym λ i → inr (merid north i)) (sym (push tt))
                          ∙ sym (rUnit _)
                          ∙ cong-∙ (Susp→⋁ (_ , inl tt) (_ , north))
                               (λ i → inr (merid (suspFun inr (δ (suc (suc n)) B (cofib→wedgeInrσ (suc (suc n)) b x))) i))
                               (λ i → inr (merid north (~ i)))
                          ∙ λ _ → toSusp (_ , inr north) (inr (suspFun inr (δ (suc (suc n))
                                                                 B (cofib→wedgeInrσ (suc (suc n)) b x))))  )
              ∙ cong₂ _∙_ (λ i → toSusp (_ , push tt i) (inl (prefunctoriality.fn+1/fn (suc (suc (suc n)))
                                                 (cellMap→finCellMap (suc (suc (suc n))) f)
                                                   flast (cofib→wedgeInrσ (suc (suc n)) b x))))
                          λ i → toSusp (_ , inr north) (inr (suspFun inr (δ (suc (suc n))
                                                                 B (cofib→wedgeInrσ (suc (suc n)) b x)))))
        ∙ (sym (cong (cong (Susp→⋁ (_ , inl tt) (_ , north)))
             (Susp∙toSusp (_ , inl tt)
               (multMap-inr-inl n) (multMap-inr-inr n) (cofib→wedgeInrσ (suc (suc n)) b x)
             ∙ cong₂ _∙_ (sym (rUnit _)
               ∙ cong-∙ (fst (multMap-inr-inl n)) (merid (cofib→wedgeInrσ (suc (suc n)) b x)) (sym (merid (inl tt)))
               ∙ refl)
                     (cong₃ _∙∙_∙∙_ refl
                       (cong-∙ (fst (multMap-inr-inr n))
                        (merid (cofib→wedgeInrσ (suc (suc n)) b x)) (sym (merid (inl tt))) ∙ refl) refl ∙ refl)
             ∙ refl))
        ∙ lUnit _ -- lUnit _)
        ∙ sym (cong-∙  (Iso.inv (SuspWedgeIso _ _) ∘ multMap n) (push tt)
          λ i → inr (toSusp (_ , inl tt) (cofib→wedgeInrσ (suc (suc n)) b x) i)))
        )
    multMap≡' n (push a i) = {!hcomp
(doubleComp-faces (λ _ → inl (snd (QuotCW∙ D (suc (suc (suc n))))))
 (λ i₁ →
    inr
    (toSusp (Pushout (λ _ → tt) (CW↪ B (suc (suc n))) , inl tt)
     (cofib→wedgeInrσ (suc (suc n)) b x) i₁))
 ?9)
(push tt ?9)!}
-}
    multMap≡ : (n : ℕ) (x : cofibskelQuot (suc n))
      → Iso.fun (SuspWedgeIso _ _)
           (suspFun (cofib→wedge n) (cofibskelQuot↓ n x))
      ≡ multMap n (cofib→wedge (suc n) x)
    multMap≡ n (inl x) = refl
    multMap≡ n (inr (inl x)) i =
      ⋁→Susp (QuotCW∙ D (suc (suc n)))
         (Susp∙ (QuotCW B (suc n)))
           (merid (cofib→wedge n (inr (fst (Iso-cofibskel' (suc n)) x))) (~ i))
    multMap≡ n (inr (inr (inl (inr x)))) = λ i → inl (merid (inl tt) i)
    multMap≡ n (inr (inr (inr x))) = refl
    multMap≡ n (inr (push (inl (inr x) , b) i)) = {!!}
    multMap≡ n (inr (push (inr x , b) i)) =
      {!!}
    multMap≡ n (push a i) j =  ⋁→Susp (QuotCW∙ D (suc (suc n))) (Susp∙ (QuotCW B (suc n))) (h j i)
      where
      h : Square (merid (cofib→wedgeInr n a))
                 refl refl
                 (sym (merid (cofib→wedgeInr n (secEq (Iso-cofibskel' (suc n)) a i0))))
        
      h = (λ i → merid (cofib→wedgeInr n (secEq (Iso-cofibskel' (suc n)) a (~ i))))
         ◁ λ i j → merid (cofib→wedgeInr n (secEq (Iso-cofibskel' (suc n)) a i0)) (~ i ∧ j)
      -- where
      --  ll : ?
      --  ll = ?

-- SuspWedgeIso
