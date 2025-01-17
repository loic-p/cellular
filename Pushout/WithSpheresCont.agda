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

module _ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') where
  SuspWedgeIso : Iso (Susp (A ⋁ B)) (Susp∙ (typ A) ⋁ Susp∙ (typ B))
  Iso.fun SuspWedgeIso north = inl north
  Iso.fun SuspWedgeIso south = inl north
  Iso.fun SuspWedgeIso (merid (inl x) i) = inl (toSusp A x i)
  Iso.fun SuspWedgeIso (merid (inr x) i) = (push tt ∙∙ (λ i → inr (toSusp B x i)) ∙∙ sym (push tt)) i
  Iso.fun SuspWedgeIso (merid (push a i) j) = {!!}
  Iso.inv SuspWedgeIso (inl x) = suspFun inl x
  Iso.inv SuspWedgeIso (inr x) = suspFun inr x
  Iso.inv SuspWedgeIso (push a i) = north
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
  Iso.rightInv SuspWedgeIso (push a i) = {!!}
  Iso.leftInv SuspWedgeIso x = {!!}

-- module _ (isEquivPushoutA→PushoutPushoutMapStrict : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
--   (f : cellMap B C)
--   (g : cellMap B D)
--    → (n : ℕ) → retract (PushoutPushoutMap→PushoutA f g n) (PushoutA→PushoutPushoutMap f g n)
--                × section (PushoutPushoutMap→PushoutA f g n) (PushoutA→PushoutPushoutMap f g n)) where
--   open MOOO isEquivPushoutA→PushoutPushoutMapStrict

--   open CWskel-fields
--   open SequenceMap renaming (map to ∣_∣)
--   open import Cubical.HITs.Wedge
--   open import Cubical.Foundations.Pointed



--   sphereBouquetSuspIso∙ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → Iso.fun (sphereBouquetSuspIso {A = A} {n}) north ≡ inl tt
--   sphereBouquetSuspIso∙ {n = zero} = refl
--   sphereBouquetSuspIso∙ {n = suc n} = refl

--   QuotCW : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Type ℓ 
--   QuotCW C n = cofib (CW↪ C n)

--   QuotCW∙ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Pointed ℓ 
--   QuotCW∙ C n = QuotCW C n , inl tt

--   module _ {B' D' : CWskel ℓ-zero}
--     (f : cellMap (strictCWskel B') (strictCWskel D')) where
--     private
--       B = strictCWskel B'
--       D = strictCWskel D'
--       C = UnitCWskel

--     open MIAU f


--     bouquetFun1 : (n : ℕ) → SphereBouquet n (Fin (card cofibCWskel n)) → QuotCW cofibCWskel n
--     bouquetFun1 n = BouquetFuns.BTC n (card cofibCWskel n) (α cofibCWskel n) (e cofibCWskel n)

--     bouquetFun← : (n : ℕ) → QuotCW cofibCWskel n → SphereBouquet n (Fin (card cofibCWskel n))
--     bouquetFun← n = BouquetFuns.CTB n (card cofibCWskel n) (α cofibCWskel n) (e cofibCWskel n)

--     SphereBouquetCellEquiv : (n m : ℕ)
--       → SphereBouquet n (Fin (card cofibCWskel m)) ≃ (SplitBouquet n (card C m) (card D m) (pushoutMidCells terminalCW f m))
--     SphereBouquetCellEquiv n m = isoToEquiv (compIso (sphereBouquetIso n) (Iso-sumSphereBouquet-SplitBouquet n))

--     bouquetFun1' : (n : ℕ) → SplitBouquet n (card C n) (card D n) (pushoutMidCells terminalCW f n)
--                             → QuotCW cofibCWskel n
--     bouquetFun1' n = bouquetFun1 n ∘ invEq (SphereBouquetCellEquiv n n)

--     -- bottom left fun
--     bouquetFun'-inl : (n : ℕ) → (SphereBouquet∙ (suc n) (Fin zero) ⋁ SphereBouquet∙ (suc n) (Fin (card D (suc n))))
--                                → (QuotCW D (suc n))
--     bouquetFun'-inl n (inl x) = inl tt
--     bouquetFun'-inl n (inr x) = BouquetFuns.BTC (suc n) (card D (suc n)) (α D (suc n)) (e D (suc n)) x
--     bouquetFun'-inl n (push a i) = inl tt

--     bouquetFun' : (n : ℕ) → SplitBouquet (suc n) zero (card D (suc n)) (pushoutMidCells terminalCW f (suc n))
--                             → (QuotCW∙ D (suc n)) ⋁ Susp∙ (QuotCW B n)
--     bouquetFun' n (inl x) = inl (bouquetFun'-inl n x)
--     bouquetFun' n (inr x) = inr (suspFun (BouquetFuns.BTC n (card B n) (α B n) (e B n)) (Iso.inv sphereBouquetSuspIso x))
--     bouquetFun' zero (push a i) = push tt i
--     bouquetFun' (suc n) (push a i) = push tt i

--     -- its inverse
--     -- bouquetFunInv-inl : (n : ℕ) → (SphereBouquet∙ (suc n) (Fin zero) ⋁ SphereBouquet∙ (suc n) (Fin (card D (suc n))))
--     --                            → (QuotCW D (suc n))
--     -- bouquetFunInv-inl n (inl x) = inl tt
--     -- bouquetFunInv-inl n (inr x) = BouquetFuns.BTC (suc n) (card D (suc n)) (α D (suc n)) (e D (suc n)) x
--     -- bouquetFunInv-inl n (push a i) = inl tt

--     bouquetFunInv : (n : ℕ) → (QuotCW∙ D (suc n)) ⋁ Susp∙ (QuotCW B n)
--       → SplitBouquet (suc n) zero (card D (suc n)) (pushoutMidCells terminalCW f (suc n))
--     bouquetFunInv n (inl x) =
--       inl (inr (BouquetFuns.CTB (suc n) (card D (suc n)) (α D (suc n)) (e D (suc n)) x))
--     bouquetFunInv n (inr x) = inr (Iso.fun sphereBouquetSuspIso
--                                     (suspFun (BouquetFuns.CTB n (card B n) (α B n) (e B n)) x))
--     bouquetFunInv zero (push a i) = ((λ i → inl (push tt (~ i))) ∙ push tt) i
--     bouquetFunInv (suc n) (push a i) = ((λ i → inl (push tt (~ i))) ∙ push tt) i

--     SphereBouquetSplit : (n : ℕ) → Type
--     SphereBouquetSplit n = SphereBouquet (suc (suc n)) (Fin (card D (suc (suc n))) ⊎ Fin (card B (suc n)))

--     cofibskel' : (n : ℕ) → Type _
--     cofibskel' n = Pushout (pushoutMapₛ terminalCW f n) fst

--     Iso-cofibskel' : (n : ℕ) → (fst cofibCWskel (suc (suc n))) ≃ (cofibskel' n)
--     Iso-cofibskel' = eCWPushout terminalCW f

--     cofibskel'↑ : (n : ℕ) → cofibskel' n → cofibskel' (suc n)
--     cofibskel'↑ n x = inl (invEq (Iso-cofibskel' n) x)

--     cofibskelQuot : (n : ℕ) → Type _
--     cofibskelQuot n = cofib {A = cofibskel' n} {B = cofibskel' (suc n)} (cofibskel'↑ n)

--     cofibskelQuot≃ : (n : ℕ) → cofibskelQuot n ≃ QuotCW cofibCWskel (suc (suc n))
--     cofibskelQuot≃ n =
--       pushoutEquiv _ _ _ _
--       (invEquiv (Iso-cofibskel' n)) (idEquiv _) (invEquiv (Iso-cofibskel' (suc n)))
--       (λ _ _ → tt) (funExt λ x → refl)

--     cofib→wedgeInrσ : (n : ℕ) (x : S₊ n) (y : A B n) → QuotCW B n
--     cofib→wedgeInrσ n x y = preBTC n (card B n) (α B n) (e B n) y .fst x

--     cofib→wedgeInr : (n : ℕ) → cofibskel' (suc n) → (QuotCW∙ D (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc n))
--     cofib→wedgeInr n (inl x) = inl (inl tt)
--     cofib→wedgeInr n (inr (inl (inr x))) = inl (inr (inr x))
--     cofib→wedgeInr n (inr (inr x)) = inr north
--     cofib→wedgeInr n (push (inl (inr x) , b) i) =
--       ((λ i → inl (push (α D (suc (suc n)) (x , b)) i)) ∙ (λ i → inl (inr (push (x , b) i)))) i
--     cofib→wedgeInr n (push (inr x , b) i) =
--       (push tt ∙ λ i → inr (toSusp (_ , inl tt) (cofib→wedgeInrσ (suc n) b x) i)) i

--     cofib→wedge : (n : ℕ) → cofibskelQuot n → (QuotCW∙ D (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc n))
--     cofib→wedge n (inl x) = inl (inl tt)
--     cofib→wedge n (inr x) = cofib→wedgeInr n x
--     cofib→wedge n (push a i) = inl (inl tt)

--     private
--       leftSquareComm-inr-inr : (n : ℕ) (w : _)
--         → Pushout→Bouquet (suc (suc n))
--         (card cofibCWskel (suc (suc n))) (α cofibCWskel (suc (suc n)))
--         (e cofibCWskel (suc (suc n)))
--         (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun (inr w))
--         ≡
--         invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
--         (bouquetFunInv (suc n) (cofib→wedgeInr n (inr w)))
--       leftSquareComm-inr-inr n (inl (inr x)) = refl
--       leftSquareComm-inr-inr n (inr x) = sym (push (Iso.fun Iso-Fin⊎Fin-Fin+ (inr x)))

--       leftSquareComm-inr : (n : ℕ) (x : cofibskel' (suc n))
--         → Pushout→Bouquet (suc (suc n))
--         (card cofibCWskel (suc (suc n))) (α cofibCWskel (suc (suc n)))
--         (e cofibCWskel (suc (suc n)))
--         (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun x)
--         ≡
--         invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
--         (bouquetFunInv (suc n) (cofib→wedgeInr n x))
--       leftSquareComm-inr n (inl x) = refl
--       leftSquareComm-inr n (inr x) = leftSquareComm-inr-inr n x
--       leftSquareComm-inr n (push (w , x) i) j = main n x w j i
--         where
--         PB : (n : ℕ) → _
--         PB n = Pushout→Bouquet (suc (suc n))
--                       (card cofibCWskel (suc (suc n))) (α cofibCWskel (suc (suc n)))
--                       (e cofibCWskel (suc (suc n)))

--         pf : (n : ℕ) (x : _ ) (w : _)
--           → Square (push (invEq (finSplit3≃ _ _ _) w)
--                          ∙ (λ i → inr ((invEq (finSplit3≃ _ _ _) w , σSn (suc n) x i))))
--                     (λ i → invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
--                                    (bouquetFunInv (suc n) (cofib→wedgeInr n (push (w , x) i))))
--                    refl (leftSquareComm-inr-inr n w)
--         pf n x (inl (inr s)) =
--             lUnit _
--           ∙ cong₂ _∙_ refl (sym (cong-∙ (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))) _ _))
--           ∙ sym (cong-∙ (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n))) ∘ bouquetFunInv (suc n)) _ _)
--         pf n x (inr s) =
--             refl
--           ◁ sqLem _ _ (pfMain n x s)
--           ▷ (lUnit _
--           ∙ cong₂ _∙_
--               (rUnit (λ _ → inl tt)
--               ∙ sym (cong-∙ (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))) (λ i → inl (push tt (~ i))) (push tt)))
--                ((rUnit _
--                ∙ cong₂ _∙_ refl (λ _ _ → inl tt))
--                ∙ sym (cong-∙ (λ w → invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
--                        (bouquetFunInv (suc n) (inr w))) (merid (cofib→wedgeInrσ (suc n) x s)) (sym (merid (inl tt)))))
--           ∙ sym (cong-∙ (λ w → invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
--                    (bouquetFunInv (suc n) w)) (push tt)
--                      (λ i → inr ((merid (cofib→wedgeInrσ (suc n) x s) ∙ sym (merid (inl tt))) i))))
--            where
--            open import Cubical.Foundations.Equiv.HalfAdjoint
--            sqLem : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) {z : A}
--                    {q : y ≡ z} {w : A} {r : z ≡ w} {l : x ≡  w}
--                 → Square q l (sym p) r → Square (p ∙ q) l refl r
--            sqLem = J> λ sq → sym (lUnit _) ◁ sq

--            module _ (n : ℕ) where
--              woo = Iso.fun (sphereBouquetIso (suc (suc n)) {a = zero} {card D (suc (suc n))} {card B (suc n)})
--              waa = sumSphereBouquet→SplitBouquet (suc (suc n)) {a = zero} {card D (suc (suc n))} {card B (suc n)}
--              wowa = waa ∘ woo          
--              wii = SplitBouquet→sumSphereBouquet (suc (suc n)) {a = zero} {card D (suc (suc n))} {card B (suc n)}
--              wiiEq : _ ≃ _
--              wiiEq = compEquiv
--                (isoToEquiv (sphereBouquetIso (suc (suc n)) {a = zero}
--                  {card D (suc (suc n))} {card B (suc n)}))
--                (isoToEquiv (Iso-sumSphereBouquet-SplitBouquet (suc (suc n))))

--            pfLem : (n : ℕ) (x : _ ) (s : _)
--              → Square (λ i₁ → wowa n (inr (invEq (finSplit3≃ zero (card D (suc (suc n))) _) (inr s) , σSn (suc n) x i₁)))
--                             (cong (λ r → wowa n
--                               (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
--                                            (bouquetFunInv (suc n) (inr r))))
--                              (merid (cofib→wedgeInrσ (suc n) x s)))
--                              (cong (wowa n) (leftSquareComm-inr-inr n (inr s)))
--                              (cong (wowa n) (leftSquareComm-inr-inr n (inr s)))
--            pfLem n x s i j =
--              hcomp (λ k → λ {(i = i0) → waa n (inr (secEq (finSplit3≃ zero _ _) (inr s) (~ k) , σSn (suc n) x j))
--                             ; (i = i1) → waa n (Iso.rightInv (sphereBouquetIso (suc (suc n)))
--                                             (SplitBouquet→sumSphereBouquet (suc (suc n)) (inr
--                                               (Bouquet→ΩBouquetSusp (Fin (card B (suc n))) (λ _ → S₊∙ (suc n))
--                                                (BouquetFuns.CTB (suc n) (card B (suc n)) (α B (suc n))
--                                                 (e B (suc n)) (cofib→wedgeInrσ (suc n) x s)) j))) (~ k))
--                             ; (j = i0) → waa n (push (secEq (finSplit3≃ zero _ _) (inr s) (~ k)) (~ i))
--                             ; (j = i1) → waa n (push (secEq (finSplit3≃ zero _ _) (inr s) (~ k)) (~ i))})
--                    (hcomp (λ k → λ {(i = i0) → inr (doubleCompPath-filler (push s)
--                                                      (λ i → inr (s , σSn (suc n) x i))
--                                                      (sym (push s)) (~ k) j)
--                             ; (i = i1) → Iso.rightInv (Iso-sumSphereBouquet-SplitBouquet (suc (suc n))
--                                                         {a = zero} {card D (suc (suc n))} {card B (suc n)})
--                                                         (inr ((Bouquet→ΩBouquetSusp (Fin (card B (suc n)))
--                                                               (λ _ → S₊∙ (suc n))
--                                                               (BouquetFuns.CTB (suc n) (card B (suc n)) (α B (suc n))
--                                                                (e B (suc n)) (cofib→wedgeInrσ (suc n) x s))) j)) (~ k)
--                             ; (j = i0) → compPath-filler'' (push tt) (λ i → inr (push s i)) k (~ i)
--                             ; (j = i1) → compPath-filler'' (push tt) (λ i → inr (push s i)) k (~ i)})
--                        (inr (Bouquet→ΩBouquetSusp (Fin (card B (suc n)))
--                               (λ _ → S₊∙ (suc n))
--                                 (Iso.rightInv (BouquetIso-gen (suc n)
--                                   (card B (suc n)) (α B (suc n)) (e B (suc n))) (inr (s , x)) (~ i)) j)))

--            pfMain : (n : ℕ) (x : _ ) (s : _)
--              → Square (λ i₁ → inr (invEq (finSplit3≃ zero (card D (suc (suc n))) _) (inr s) , σSn (suc n) x i₁))
--                             (cong (λ r → invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
--                                            (bouquetFunInv (suc n) (inr r)))
--                              (merid (cofib→wedgeInrσ (suc n) x s)))
--                              (leftSquareComm-inr-inr n (inr s))
--                              (leftSquareComm-inr-inr n (inr s))
--            pfMain n x s i j =
--              hcomp (λ k → λ {(i = i0) → retEq (wiiEq n) (inr (invEq (finSplit3≃ zero (card D (suc (suc n))) _)
--                                                                (inr s) , σSn (suc n) x j)) k
--                             ; (i = i1) → retEq (wiiEq n)
--                               (invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
--                                   (bouquetFunInv (suc n) (inr (merid (cofib→wedgeInrσ (suc n) x s) j)))) k
--                             ; (j = i0) → retEq (wiiEq n) (push (Iso.fun Iso-Fin⊎Fin-Fin+ (inr s)) (~ i)) k
--                             ; (j = i1) → retEq (wiiEq n) (push (Iso.fun Iso-Fin⊎Fin-Fin+ (inr s)) (~ i)) k})
--                (invEq (wiiEq n) (pfLem n x s i j))

--         main : (n : ℕ) (x : _ ) (w : _)
--           → Square (λ i → PB n (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun (push (w , x) i)))
--                     (λ i → invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
--                                    (bouquetFunInv (suc n) (cofib→wedgeInr n (push (w , x) i))))
--                    refl (leftSquareComm-inr-inr n w)
--         main n x w = (cong-∙ (PB n) _ _ ∙ (sym (lUnit _)))
--                    ◁ pf n x w


    
--     leftSquareComm : (n : ℕ) (x : cofibskelQuot n)
--       → BouquetFuns.CTB (suc (suc n)) (card cofibCWskel (suc (suc n)))
--               (α cofibCWskel (suc (suc n))) (e cofibCWskel (suc (suc n)))
--                 (cofibskelQuot≃ n .fst x)
--       ≡ invEq (SphereBouquetCellEquiv (suc (suc n)) (suc (suc n)))
--                (bouquetFunInv (suc n) (cofib→wedge n x))
--     leftSquareComm n (inl x) = refl
--     leftSquareComm n (inr x) =
--       cong (Pushout→Bouquet (suc (suc n)) (card cofibCWskel (suc (suc n)))
--            (α cofibCWskel (suc (suc n))) (e cofibCWskel (suc (suc n))))
--            (cong (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun)
--                  (secEq (eCWPushout terminalCW f (suc n)) x))
--       ∙ leftSquareComm-inr n x
--     leftSquareComm n (push a i) j =
--       hcomp (λ k → λ {(i = i0) → inl tt
--                      ; (j = i0) → hh (~ k) i
--                      ; (j = i1) → inl tt})
--        (W (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun
--          ((isEquivPushoutA→PushoutPushoutMapStrict terminalCW f
--           (suc n) .fst (inl (PushoutPushoutMap→PushoutA terminalCW f n a))
--           (~ i ∨ j)))))
--       where

--       secCompEquiv : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
--         → (e : A ≃ B) (d : B ≃ C) (x : _) → secEq (compEquiv e d) x ≡ cong (fst d) (secEq e (invEq d x)) ∙ secEq d x
--       secCompEquiv e d x = refl

--       W = Pushout→Bouquet (suc (suc n)) (card cofibCWskel (suc (suc n)))
--                        (α cofibCWskel (suc (suc n))) (e cofibCWskel (suc (suc n)))
--       L = BouquetFuns.CTB (suc (suc n)) (card cofibCWskel (suc (suc n)))
--             (α cofibCWskel (suc (suc n))) (e cofibCWskel (suc (suc n)))
--       hh : cong L (push (PushoutPushoutMap→PushoutA terminalCW f n a) ∙ refl)
--          ≡ cong W (cong (Iso-Pushoutα-PushoutPushoutMapₛ terminalCW f (suc n) .Iso.fun)
--                         (sym ((secEq (eCWPushout terminalCW f (suc n)))
--                           (inl (PushoutPushoutMap→PushoutA terminalCW f n a)))))
--       hh = cong-∙ L _ _ ∙ sym (rUnit _) ∙ cong-∙∙ W _ _ _ ∙ sym (rUnit _)


--   ------ STEP 2

--     cofibskelQuotSusp : (n : ℕ) → cofibskelQuot n  → Susp (cofibskel' n)
--     cofibskelQuotSusp n (inl x) = north
--     cofibskelQuotSusp n (inr x) = south
--     cofibskelQuotSusp n (push a i) = merid a i

--     cofibskelQuot↓ : (n : ℕ) → cofibskelQuot (suc n)  → Susp (cofibskelQuot n)
--     cofibskelQuot↓ n x = suspFun inr (cofibskelQuotSusp (suc n) x)

--     module _ (n : ℕ) where
--       multMap-inr-inl : Susp∙ (QuotCW B (suc (suc n))) →∙ (Susp∙ (QuotCW D (suc (suc n))) ⋁∙ₗ Susp∙ (Susp (QuotCW B (suc n))))
--       fst multMap-inr-inl x = inl (suspFun (prefunctoriality.fn+1/fn (suc (suc (suc n)))
--                                    (cellMap→finCellMap (suc (suc (suc n))) f ) flast) x)
--       snd multMap-inr-inl = refl

--       multMap-inr-inr : Susp∙ (QuotCW B (suc (suc n))) →∙ (Susp∙ (QuotCW D (suc (suc n))) ⋁∙ₗ Susp∙ (Susp (QuotCW B (suc n))))
--       fst multMap-inr-inr x = inr (suspFun (suspFun inr ∘ δ (suc (suc n)) B) x)
--       snd multMap-inr-inr = sym (push tt)

--       multMap : (QuotCW∙ D (suc (suc (suc n)))) ⋁ Susp∙ (QuotCW B (suc (suc n)))
--                         → (Susp∙ (QuotCW D (suc (suc n))) ⋁ Susp∙ (Susp (QuotCW B (suc n))))
--       multMap (inl x) = inl (suspFun inr (δ (suc (suc (suc n))) D x))
--       multMap (inr x) = ·Susp (QuotCW∙ B (suc (suc n)))
--         multMap-inr-inl multMap-inr-inr .fst x
--       multMap (push a i) = inl north

