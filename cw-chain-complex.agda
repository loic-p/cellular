{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup

open import prelude
open import freeabgroup
open import degree
open import spherebouquet hiding (chooseS)
open import cw-complex

module cw-chain-complex (C : CW) where

-- In this file, we associate to every CW complex its cellular chain complex
-- The group in dimension n is Z[A_n] where A_n is the number of n-cells
-- The boundary map is defined through a bit of homotopical manipulation.
-- The definition loosely follows May's Concise Course in Alg. Top.

-- the groups of the chain complex associated to a CW-complex C
ℤ[A_] : (n : ℕ) → AbGroup ℓ-zero
ℤ[A n ] = FreeAbGroup (Fin (snd C .fst n))

-- in this module we define pre∂, a homotopical version of the boundary map
-- it goes from V_(A_n+2) S^(n+2) to V_(A_n+1) S^(n+2)
module preboundary (n : ℕ) where
  Xn+1 = (fst C (suc n))
  An+1 = (snd C .fst (suc n))
  αn+1 = (snd C .snd .fst n)
  An+2 = (snd C .fst (suc (suc n)))
  αn+2 = (snd C .snd .fst (suc n))

  isoSuspBouquet : Susp∙ (fst (SphereBouquet (suc n) (Fin An+1)))
                   →∙ SphereBouquet (suc (suc n)) (Fin An+1)
  isoSuspBouquet = Iso.fun sphereBouquetSuspIso , refl

  isoSuspBouquet↑ : Susp∙ (fst (SphereBouquet (suc (suc n)) (Fin An+1)))
                    →∙ SphereBouquet (suc (suc (suc n))) (Fin An+1)
  isoSuspBouquet↑ = Iso.fun sphereBouquetSuspIso , refl

  isoSuspBouquetInv↑ : SphereBouquet (suc (suc (suc n))) (Fin An+2)
                       →∙ Susp∙ (fst (SphereBouquet (suc (suc n)) (Fin An+2)))
  isoSuspBouquetInv↑ = Iso.inv sphereBouquetSuspIso , refl

  isoCofBouquet : cofiber n C →∙ SphereBouquet (suc n) (Fin An+1)
  isoCofBouquet = Iso.fun (BouquetIso-gen n An+1 αn+1 (snd C .snd .snd .snd n))
                  , refl

  isoCofBouquetInv↑ : SphereBouquet (suc (suc n)) (Fin An+2) →∙ cofiber (suc n) C
  isoCofBouquetInv↑ = (Iso.inv (BouquetIso-gen (suc n) An+2 αn+2 (snd C .snd .snd .snd (suc n))))
                     , refl

  connecting : cofiber (suc n) C →∙ Susp∙ Xn+1
  connecting = δ∙ (suc n) C

  -- our homotopical boundary map
  pre∂ : (SphereBouquet (suc (suc n)) (Fin An+2)
         →∙ SphereBouquet (suc (suc n)) (Fin An+1))
  pre∂ = isoSuspBouquet ∘∙ (suspFun∙ (fst isoCofBouquet)
         ∘∙ ((suspFun∙ (to_cofiber n C) ∘∙ connecting) ∘∙ isoCofBouquetInv↑))

  -- we define a suspended version
  -- we cannot prove that pre∂ ∘ pre∂ ≡ 0, because the dimensions do not match
  -- instead, we will prove susp-pre∂ ∘ pre∂ ≡ 0
  susp-pre∂ = suspFun∙ (fst isoSuspBouquet) ∘∙ (suspFun∙ (suspFun (fst isoCofBouquet))
              ∘∙ ((suspFun∙ (suspFun (to_cofiber n C)) ∘∙ suspFun∙ (fst connecting))
              ∘∙ (suspFun∙ (fst isoCofBouquetInv↑))))

  -- variant of susp-pre∂ where all the suspensions are collected
  pre∂↑ : (SphereBouquet (suc (suc (suc n))) (Fin An+2)
          →∙ SphereBouquet (suc (suc (suc n))) (Fin An+1))
  pre∂↑ = isoSuspBouquet↑ ∘∙ (susp-pre∂ ∘∙ isoSuspBouquetInv↑)

  -- susp is distributive, so susp-pre∂ ≡ pre∂↑
  susp-pre∂-pre∂↑ : fst (bouquetSusp→ pre∂) ≡ fst pre∂↑
  susp-pre∂-pre∂↑ = congS (λ X → (fst isoSuspBouquet↑) ∘ X ∘ (fst isoSuspBouquetInv↑)) susp-distrib
    where
      susp-distrib : fst (suspFun∙ (fst pre∂)) ≡ fst susp-pre∂
      susp-distrib i north = north
      susp-distrib i south = south
      susp-distrib i (merid a i₁) = fst susp-pre∂ (merid a i₁)


-- In this module we prove that (susp pre∂) ∘ pre∂ ≡ 0
-- from that, we will deduce that ∂ ∘ ∂ ≡ 0
module preboundary-cancellation (n : ℕ) where
  open preboundary

  -- the desired equation comes from exactness of the (Baratt-Puppe) long cofiber sequence
  -- we need some choice to prove this lemma -- which is fine, because we use finite sets
  -- this is because the spaces we are dealing with are not pointed
  cofiber-exactness : (connecting n .fst) ∘ (to_cofiber (suc n) C) ≡ λ x → north
  cofiber-exactness i x = merid (choose-point x) (~ i)
    where
      choose-aux : (card : ℕ) (α : Fin card × S₊ (suc n) → Xn+1 n)
                   → Pushout α (λ r → fst r) → Xn+1 n
      choose-aux zero α (inl x) = x
      choose-aux zero α (inr x) with (¬Fin0 x)
      choose-aux zero α (inr x) | ()
      choose-aux zero α (push (x , _) i) with (¬Fin0 x)
      choose-aux zero α (push (x , _) i) | ()
      choose-aux (suc card') α x = α (fzero , ptSn (suc n))

      choose-point : Xn+1 (suc n) → Xn+1 n
      choose-point x = choose-aux (An+2 n) (αn+2 n) (snd C .snd .snd .snd (suc n) .fst x)

  -- combining the previous result with some isomorphism cancellations
  cancellation : suspFun (connecting n .fst) ∘ suspFun (isoCofBouquetInv↑ n .fst)
                 ∘ (isoSuspBouquetInv↑ n .fst) ∘ (isoSuspBouquet (suc n) .fst)
                 ∘ (suspFun (isoCofBouquet (suc n) .fst)) ∘ suspFun (to_cofiber (suc n) C)
                 ≡ λ x → north
  cancellation = congS (λ X → suspFun (connecting n .fst) ∘ suspFun (isoCofBouquetInv↑ n .fst)
                              ∘ X ∘ (suspFun (isoCofBouquet (suc n) .fst))
                              ∘ suspFun (to_cofiber (suc n) C))
                       iso-cancel-2
                 ∙∙ congS (λ X → suspFun (connecting n .fst) ∘ X ∘ suspFun (to_cofiber (suc n) C))
                          iso-cancel-1
                 ∙∙ cofiber-exactness↑
    where
      cofiber-exactness↑ : suspFun (connecting n .fst) ∘ suspFun (to_cofiber (suc n) C)
                           ≡ λ x → north
      cofiber-exactness↑ = sym (suspFun-comp _ _)
                           ∙∙ congS suspFun cofiber-exactness
                           ∙∙ suspFun-const north

      iso-cancel-1 : suspFun (isoCofBouquetInv↑ n .fst) ∘ suspFun (isoCofBouquet (suc n) .fst)
                     ≡ λ x → x
      iso-cancel-1 = sym (suspFun-comp _ _)
                     ∙∙ congS suspFun (λ i x → Iso.leftInv
                          (BouquetIso-gen (suc n) (An+2 n) (αn+2 n)
                                          (snd C .snd .snd .snd (suc n))) x i)
                     ∙∙ suspFun-id

      iso-cancel-2 : (isoSuspBouquetInv↑ n .fst) ∘ (isoSuspBouquet (suc n) .fst) ≡ λ x → x
      iso-cancel-2 i x = Iso.leftInv sphereBouquetSuspIso x i

  left-maps = (isoSuspBouquet↑ n .fst) ∘ (suspFun (isoSuspBouquet n .fst))
              ∘ (suspFun (suspFun (isoCofBouquet n .fst))) ∘ (suspFun (suspFun (to_cofiber n C)))

  right-maps = (connecting (suc n) .fst) ∘ (isoCofBouquetInv↑ (suc n) .fst)

  -- the cancellation result but suspension has been distributed on every map
  pre∂↑pre∂≡0 : fst (pre∂↑ n) ∘ fst (pre∂ (suc n)) ≡ λ _ → inl tt
  pre∂↑pre∂≡0 = congS (λ X → left-maps ∘ X ∘ right-maps) cancellation

  -- we factorise the suspensions
  -- and use the fact that a pointed map is constant iff its nonpointed part is constant
  pre∂pre∂≡0 : (bouquetSusp→ (pre∂ n)) ∘∙ (pre∂ (suc n)) ≡ ((λ _ → inl tt) , refl)
  pre∂pre∂≡0 = constant-pointed ((bouquetSusp→ (pre∂ n)) ∘∙ (pre∂ (suc n)))
                                (congS (λ X → X ∘ (fst (pre∂ (suc n))))
                                       (susp-pre∂-pre∂↑ n) ∙ pre∂↑pre∂≡0)

-- the boundary map of the chain complex associated to C
∂ : (n : ℕ) → AbGroupHom (ℤ[A (suc (suc n)) ]) (ℤ[A (suc n) ])
∂ n = bouquetDegree pre∂
  where
    open preboundary n

-- ∂ ∘ ∂ = 0, the fundamental equation of chain complexes
∂∂≡0 : (n : ℕ) → compGroupHom (∂ (suc n)) (∂ n)
               ≡ constAbGroupHom (ℤ[A (suc (suc (suc n))) ]) (ℤ[A (suc n) ])
∂∂≡0 n = congS (compGroupHom (∂ (suc n))) ∂≡∂↑
           ∙∙ sym (degreeComp (bouquetSusp→ (pre∂ n)) (pre∂ (suc n)))
           ∙∙ (congS bouquetDegree (preboundary-cancellation.pre∂pre∂≡0 n)
           ∙ degreeConst _ _ _)
  where
    open preboundary

    ∂↑ : AbGroupHom (ℤ[A (suc (suc n)) ]) (ℤ[A (suc n) ])
    ∂↑ = bouquetDegree (bouquetSusp→ (pre∂ n))

    ∂≡∂↑ : ∂ n ≡ ∂↑
    ∂≡∂↑ = degreeSusp (pre∂ n)
