{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
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
open import ChainComplex

-- In this file, we associate to every CW complex its cellular chain complex
-- The group in dimension n is Z[A_n] where A_n is the number of n-cells
-- The boundary map is defined through a bit of homotopical manipulation.
-- The definition loosely follows May's Concise Course in Alg. Top.

module cw-chain-complex (C : CW) where

-- the groups of the chain complex associated to a CW-complex C
ℤ[A_] : (n : ℕ) → AbGroup ℓ-zero
ℤ[A n ] = FreeAbGroup (Fin (snd C .fst n))

-- in this module we define pre∂, a homotopical version of the boundary map
-- it goes from V_(A_n+2) S^(n+2) to V_(A_n+1) S^(n+2)
module preboundary (n : ℕ) where
  Xn = (fst C n)
  Xn+1 = (fst C (suc n))
  An = (snd C .fst n)
  An+1 = (snd C .fst (suc n))
  αn = (snd C .snd .fst n)
  αn+1 = (snd C .snd .fst (suc n))

  isoSuspBouquet : Susp (SphereBouquet n (Fin An))
                   → SphereBouquet (suc n) (Fin An)
  isoSuspBouquet = Iso.fun sphereBouquetSuspIso

  isoSuspBouquetInv : SphereBouquet (suc n) (Fin An)
                   → Susp (SphereBouquet n (Fin An))
  isoSuspBouquetInv = Iso.inv sphereBouquetSuspIso

  isoSuspBouquet↑ : Susp (SphereBouquet (suc n) (Fin An))
                    → SphereBouquet (suc (suc n)) (Fin An)
  isoSuspBouquet↑ = Iso.fun sphereBouquetSuspIso

  isoSuspBouquetInv↑ : SphereBouquet (suc (suc n)) (Fin An+1)
                       → Susp (SphereBouquet (suc n) (Fin An+1))
  isoSuspBouquetInv↑ = Iso.inv sphereBouquetSuspIso

  isoCofBouquet : cofiber n C → SphereBouquet n (Fin An)
  isoCofBouquet = Iso.fun (BouquetIso-gen n An αn (snd C .snd .snd .snd n))

  isoCofBouquetInv↑ : SphereBouquet (suc n) (Fin An+1) → cofiber (suc n) C
  isoCofBouquetInv↑ = Iso.inv (BouquetIso-gen (suc n) An+1 αn+1 (snd C .snd .snd .snd (suc n)))

  -- our homotopical boundary map
  pre∂ : SphereBouquet (suc n) (Fin An+1) → SphereBouquet (suc n) (Fin An)
  pre∂ = isoSuspBouquet ∘ (suspFun isoCofBouquet)
         ∘ (suspFun (to_cofiber n C)) ∘ (δ (suc n) C) ∘ isoCofBouquetInv↑

  -- we define a suspended version
  -- we cannot prove that pre∂ ∘ pre∂ ≡ 0, because the dimensions do not match
  -- instead, we will prove susp-pre∂ ∘ pre∂ ≡ 0
  susp-pre∂ = (suspFun isoSuspBouquet) ∘ (suspFun (suspFun isoCofBouquet))
              ∘ (suspFun (suspFun (to_cofiber n C))) ∘ (suspFun (δ (suc n) C))
              ∘ (suspFun isoCofBouquetInv↑)

  -- variant of susp-pre∂ where all the suspensions are collected
  pre∂↑ : (SphereBouquet (suc (suc n)) (Fin An+1)
          → SphereBouquet (suc (suc n)) (Fin An))
  pre∂↑ = isoSuspBouquet↑ ∘ susp-pre∂ ∘ isoSuspBouquetInv↑

  -- susp is distributive, so susp-pre∂ ≡ pre∂↑
  susp-pre∂-pre∂↑ : bouquetSusp→ pre∂ ≡ pre∂↑
  susp-pre∂-pre∂↑ = congS (λ X → isoSuspBouquet↑ ∘ X ∘ isoSuspBouquetInv↑) susp-distrib
    where
      susp-distrib : suspFun pre∂ ≡ susp-pre∂
      susp-distrib i north = north
      susp-distrib i south = south
      susp-distrib i (merid a i₁) = susp-pre∂ (merid a i₁)


-- In this module we prove that (susp pre∂) ∘ pre∂ ≡ 0
-- from that, we will deduce that ∂ ∘ ∂ ≡ 0
module preboundary-cancellation (n : ℕ) where
  open preboundary

  -- the desired equation comes from exactness of the (Baratt-Puppe) long cofiber sequence
  -- we need some choice to prove this lemma -- which is fine, because we use finite sets
  -- this is because the spaces we are dealing with are not pointed
  cofiber-exactness : (δ (suc n) C) ∘ (to_cofiber (suc n) C) ≡ λ x → north
  cofiber-exactness i x = merid (choose-point x) (~ i)
    where
      choose-aux : (card : ℕ) (α : Fin card × S₊ n → Xn+1 n)
                   → Pushout α (λ r → fst r) → Xn+1 n
      choose-aux zero α (inl x) = x
      choose-aux zero α (inr x) with (¬Fin0 x)
      choose-aux zero α (inr x) | ()
      choose-aux zero α (push (x , _) i) with (¬Fin0 x)
      choose-aux zero α (push (x , _) i) | ()
      choose-aux (suc card') α x = α (fzero , ptSn n)

      choose-point : Xn+1 (suc n) → Xn+1 n
      choose-point x = choose-aux (An+1 n) (αn (suc n)) (snd C .snd .snd .snd (suc n) .fst x)

  -- combining the previous result with some isomorphism cancellations
  cancellation : suspFun (δ (suc n) C) ∘ suspFun (isoCofBouquetInv↑ n)
                 ∘ (isoSuspBouquetInv↑ n) ∘ (isoSuspBouquet (suc n))
                 ∘ (suspFun (isoCofBouquet (suc n))) ∘ suspFun (to_cofiber (suc n) C)
                 ≡ λ x → north
  cancellation = congS (λ X → suspFun (δ (suc n) C) ∘ suspFun (isoCofBouquetInv↑ n)
                              ∘ X ∘ (suspFun (isoCofBouquet (suc n)))
                              ∘ suspFun (to_cofiber (suc n) C))
                       iso-cancel-2
                 ∙∙ congS (λ X → suspFun (δ (suc n) C) ∘ X ∘ suspFun (to_cofiber (suc n) C))
                          iso-cancel-1
                 ∙∙ cofiber-exactness↑
    where
      cofiber-exactness↑ : suspFun (δ (suc n) C) ∘ suspFun (to_cofiber (suc n) C)
                           ≡ λ x → north
      cofiber-exactness↑ = sym (suspFun-comp _ _)
                           ∙∙ congS suspFun cofiber-exactness
                           ∙∙ suspFun-const north

      iso-cancel-1 : suspFun (isoCofBouquetInv↑ n) ∘ suspFun (isoCofBouquet (suc n))
                     ≡ λ x → x
      iso-cancel-1 = sym (suspFun-comp _ _)
                     ∙∙ congS suspFun (λ i x → Iso.leftInv
                          (BouquetIso-gen (suc n) (An+1 n) (αn+1 n)
                                          (snd C .snd .snd .snd (suc n))) x i)
                     ∙∙ suspFun-id
      iso-cancel-2 : (isoSuspBouquetInv↑ n) ∘ (isoSuspBouquet (suc n)) ≡ λ x → x
      iso-cancel-2 i x = Iso.leftInv sphereBouquetSuspIso x i

  left-maps = (isoSuspBouquet↑ n) ∘ (suspFun (isoSuspBouquet n))
              ∘ (suspFun (suspFun (isoCofBouquet n))) ∘ (suspFun (suspFun (to_cofiber n C)))

  right-maps = (δ (suc (suc n)) C) ∘ (isoCofBouquetInv↑ (suc n))

  -- the cancellation result but suspension has been distributed on every map
  pre∂↑pre∂≡0 : (pre∂↑ n) ∘ (pre∂ (suc n)) ≡ λ _ → inl tt
  pre∂↑pre∂≡0 = congS (λ X → left-maps ∘ X ∘ right-maps) cancellation

  -- we factorise the suspensions
  -- and use the fact that a pointed map is constant iff its nonpointed part is constant
  pre∂pre∂≡0 : (bouquetSusp→ (pre∂ n)) ∘ (pre∂ (suc n)) ≡ (λ _ → inl tt)
  pre∂pre∂≡0 = (congS (λ X → X ∘ (pre∂ (suc n))) (susp-pre∂-pre∂↑ n) ∙ pre∂↑pre∂≡0)

-- the boundary map of the chain complex associated to C
∂ : (n : ℕ) → AbGroupHom (ℤ[A (suc n) ]) (ℤ[A n ])
∂ n = bouquetDegree (preboundary.pre∂ n)

-- ∂ ∘ ∂ = 0, the fundamental equation of chain complexes
∂∂≡0 : (n : ℕ) → compGroupHom (∂ (suc n)) (∂ n) ≡ 0hom
∂∂≡0 n = congS (compGroupHom (∂ (suc n))) ∂≡∂↑
           ∙∙ sym (degreeComp (bouquetSusp→ (pre∂ n)) (pre∂ (suc n)))
           ∙∙ (congS bouquetDegree (preboundary-cancellation.pre∂pre∂≡0 n)
           ∙ degreeConst _ _ _)
  where
    open preboundary

    ∂↑ : AbGroupHom (ℤ[A (suc n) ]) (ℤ[A n ])
    ∂↑ = bouquetDegree (bouquetSusp→ (pre∂ n))

    ∂≡∂↑ : ∂ n ≡ ∂↑
    ∂≡∂↑ = degreeSusp (pre∂ n)


open ChainComplex.ChainComplex

CW-ChainComplex : ChainComplex ℓ-zero
chain CW-ChainComplex n = ℤ[A n ]
bdry CW-ChainComplex = ∂
bdry²=0 CW-ChainComplex = ∂∂≡0

-- Cellular homology
Hᶜʷ : (n : ℕ) → Group₀
Hᶜʷ n = homology n CW-ChainComplex
