-- Obtaining a chain homotopy from a cellular homotopy

{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool hiding (_≟_ ; isProp≤)

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms

open import prelude
open import freeabgroup
open import spherebouquet
open import degree
open import cw-complex
open import cw-chain-complex
open import cw-map
open import ChainComplex

module CWHomotopy-gen where

-- A cellular homotopy between two cellular maps
-- TODO : use finite approximations instead
record cellHom {C D : CW} (f g : cellMap C D) : Type where
  open cellMap
  field
    hom : (n : ℕ) → (x : C .fst n) → CW↪ D n (f .map n x) ≡ CW↪ D n (g .map n x)
    coh : (n : ℕ) → (c : C .fst n) → Square (cong (CW↪ D (suc n)) (hom n c))
                                            (hom (suc n) (CW↪ C n c))
                                            (cong (CW↪ D (suc n)) (f .comm n c))
                                            (cong (CW↪ D (suc n)) (g .comm n c))

-- Extracting a map between sphere bouquets from a MMmap
cofibIso : (n : ℕ) (C : CW) → Iso (Susp (cofiber n C)) (SphereBouquet (suc n) (CW-fields.A C n))
cofibIso n C =
  compIso (congSuspIso
            (BouquetIso-gen n (CW-fields.card C n) (CW-fields.α C n) (CW-fields.e C n)))
          sphereBouquetSuspIso

-- Building a chain homotopy from a cell homotopy
module preChainHomotopy (C D : CW) (n : ℕ)
  (fₙ : fst C n → fst D n)
  (gₙ : fst C n → fst D n)
  (fₙ₊₁ : fst C (suc n) → fst D (suc n))
  (gₙ₊₁ : fst C (suc n) → fst D (suc n))
  (f-homₙ : (x : fst C n) → CW↪ D n (fₙ x) ≡ fₙ₊₁ (CW↪ C n x))
  (g-homₙ : (x : fst C n) → CW↪ D n (gₙ x) ≡ gₙ₊₁ (CW↪ C n x))
  (Hₙ : (x : C .fst n) → CW↪ D n (fₙ x) ≡ CW↪ D n (gₙ x))
  (Hₙ₊₁ : (x : C .fst (suc n)) →
         CW↪ D (suc n) (fₙ₊₁ x) ≡ CW↪ D (suc n) (gₙ₊₁ x))
  (Hₙ-coh : (c : C .fst n)
    → Square (cong (CW↪ D (suc n)) (Hₙ c))
              (Hₙ₊₁ (CW↪ C n c))
              (cong (CW↪ D (suc n)) (f-homₙ c))
              (cong (CW↪ D (suc n)) (g-homₙ c)))

  where
  open cellMap
  open cellHom

  -- the homotopy expressed as a map Susp (cofiber n C) → cofiber (suc n) D
  Hn+1/Hn : Susp (cofiber n C) → cofiber (suc n) D
  Hn+1/Hn north = inl tt
  Hn+1/Hn south = inl tt
  Hn+1/Hn (merid (inl tt) i) = inl tt
  Hn+1/Hn (merid (inr x) i) = ((push (fₙ₊₁ x)) ∙∙ (cong inr (Hₙ₊₁ x)) ∙∙ (sym (push (gₙ₊₁ x)))) i
  Hn+1/Hn (merid (push x j) i) =
    hcomp (λ k → λ { (i = i0) → push (f-homₙ x j) (~ k)
                   ; (i = i1) → push (g-homₙ x j) (~ k)
                   ; (j = i0) → push (Hₙ x i) (~ k) })
          (inr (Hₙ-coh x j i))

  -- the homotopy expressed as a map of sphere bouquets
  bouquetHomotopy : SphereBouquet (suc n) (CW-fields.A C n) → SphereBouquet (suc n) (CW-fields.A D (suc n))
  bouquetHomotopy = Iso.fun bouquetIso ∘ Hn+1/Hn ∘ Iso.inv (cofibIso n C)
    where
      bouquetIso = BouquetIso-gen (suc n) (CW-fields.card D (suc n)) (CW-fields.α D (suc n)) (CW-fields.e D (suc n))

  -- the homotopy as a map of abelian groups
  chainHomotopy : AbGroupHom (ℤ[A C ] n) (ℤ[A D ] (suc n))
  chainHomotopy = bouquetDegree bouquetHomotopy

-- Now, we would like to prove the chain homotopy equation ∂H + H∂ = f - g
-- MMmaps (Meridian-to-Meridian maps) are a convenient abstraction for the kind of maps
-- that we are going to manipulate
module MMmaps (C D : CW) (n : ℕ)
  where
  MMmap : (m1 m2 : (x : C .fst (suc n)) → cofiber n D) → Type
  MMmap m1 m2 = (x : C .fst n) → m1 (CW↪ C n x) ≡ m2 (CW↪ C n x)

  -- the suspension of a cell map as a MMmap
  MMΣcellMap : (fₙ : fst C n → fst D n) (fₙ₊₁ : fst C (suc n) → fst D (suc n))
               (f-homₙ : (x : fst C n) → CW↪ D n (fₙ x) ≡ fₙ₊₁ (CW↪ C n x))
       → MMmap (λ x → (inr (fₙ₊₁ x))) (λ x → inl tt)
  MMΣcellMap fₙ fₙ₊₁ f-homₙ x = sym (push (fₙ x) ∙ (cong inr (f-homₙ x)))

  -- Addition of MMmaps
  MMmap-add : (m1 m2 m3 : (x : C .fst (suc n)) → cofiber n D)
            → MMmap m1 m2 → MMmap m2 m3 → MMmap m1 m3
  MMmap-add m1 m2 m3 e1 e2 x = (e1 x) ∙ (e2 x)

  -- Extracting a map between suspensions of cofibers from a MMmap
  realiseMMmap : (m1 m2 : (x : C .fst (suc n)) → cofiber n D)
                 → MMmap m1 m2 → Susp (cofiber n C) → Susp (cofiber n D)
  realiseMMmap m1 m2 e north = north
  realiseMMmap m1 m2 e south = north
  realiseMMmap m1 m2 e (merid (inl tt) i) = north
  realiseMMmap m1 m2 e (merid (inr x) i) = (merid (m1 x) ∙∙ refl ∙∙ (sym (merid (m2 x)))) i
  realiseMMmap m1 m2 e (merid (push x j) i) =
    hcomp (λ k → λ { (i = i0) → merid (m1 (CW↪ C n x)) (~ k)
                   ; (i = i1) → merid (m2 (CW↪ C n x)) (~ k)
                   ; (j = i0) → merid (e x i) (~ k) })
          (south)

  -- Extracting a map between sphere bouquets from a MMmap
  bouquetMMmap : (m1 m2 : (x : C .fst (suc n)) → cofiber n D)
                 → MMmap m1 m2
                 → SphereBouquet (suc n) (CW-fields.A C n)
                 → SphereBouquet (suc n) (CW-fields.A D n)
  bouquetMMmap m1 m2 f =
      Iso.fun (cofibIso n D)
    ∘ realiseMMmap m1 m2 f
    ∘ Iso.inv (cofibIso n C)


-- Expressing the chain homotopy at the level of MMmaps
-- There, it is easy to prove the chain homotopy equation
module MMchainHomotopy (C D : CW) (n : ℕ) 
  (fₙ : fst C n → fst D n)
  (gₙ : fst C n → fst D n)
  (fₙ₊₁ : fst C (suc n) → fst D (suc n))
  (gₙ₊₁ : fst C (suc n) → fst D (suc n))
  (f-homₙ : (x : fst C n) → CW↪ D n (fₙ x) ≡ fₙ₊₁ (CW↪ C n x))
  (g-homₙ : (x : fst C n) → CW↪ D n (gₙ x) ≡ gₙ₊₁ (CW↪ C n x))
  (Hₙ : (x : C .fst n) → CW↪ D n (fₙ x) ≡ CW↪ D n (gₙ x))
  where
  open cellMap
  open cellHom
  open MMmaps C D n

  merid-f merid-g merid-tt : (x : C .fst (suc n)) → cofiber n D
  merid-f = λ x → inr (fₙ₊₁ x)
  merid-g = λ x → inr (gₙ₊₁ x)
  merid-tt = λ x → inl tt

  MM∂H : MMmap merid-f merid-g
  MM∂H x = (sym (cong inr (f-homₙ x))) ∙∙ (cong inr (Hₙ x)) ∙∙ (cong inr (g-homₙ x))

  -- the suspension of f as a MMmap
  MMΣf : MMmap merid-f merid-tt
  MMΣf = MMΣcellMap fₙ fₙ₊₁ f-homₙ

  -- the suspension of g as a MMmap
  MMΣg : MMmap merid-g merid-tt
  MMΣg = MMΣcellMap gₙ gₙ₊₁ g-homₙ

  -- the suspension of H∂ as a MMmap
  MMΣH∂ : MMmap merid-tt merid-tt
  MMΣH∂ x = sym ((push (fₙ x)) ∙∙ (cong inr (Hₙ x)) ∙∙ (sym (push (gₙ x))))

  -- the chain homotopy equation at the level of MMmaps
  MMchainHomotopy : ∀ x →
    MMmap-add merid-f merid-tt merid-tt (MMmap-add merid-f merid-g merid-tt MM∂H MMΣg) MMΣH∂ x
    ≡ MMΣf x
  MMchainHomotopy x = sym (doubleCompPath-elim (MM∂H x) (MMΣg x) (MMΣH∂ x)) ∙ aux2
    where
      aux : Square (MMΣf x) (MMΣg x) (MM∂H x) (sym (MMΣH∂ x))
      aux i j =
         hcomp (λ k → λ {(i = i0) → compPath-filler (push (fₙ x)) (λ i₁ → inr (f-homₙ x i₁)) k (~ j)
                       ; (i = i1) → compPath-filler (push (gₙ x)) (λ i₁ → inr (g-homₙ x i₁)) k (~ j)
                       ; (j = i1) → (push (fₙ x) ∙∙ (λ i → inr (Hₙ x i)) ∙∙ (λ i₁ → push (gₙ x) (~ i₁))) i})
                (doubleCompPath-filler  (push (fₙ x)) (λ i → (inr (Hₙ x i))) (λ i₁ → push (gₙ x) (~ i₁)) j i)

      aux2 : (MM∂H x ∙∙ MMΣg x ∙∙ MMΣH∂ x) ≡ MMΣf x
      aux2 i j =
        hcomp (λ k → λ { (j = i0) → MM∂H x ((~ i) ∧ (~ k))
                       ; (j = i1) → MMΣH∂ x (i ∨ k)
                       ; (i = i1) → MMΣf x j })
              (aux (~ i) j)

-- Now we want to transform our MMmap equation to the actual equation
-- First, we connect the involved MMmaps to cofiber maps
module realiseMMmap (C D : CW) (n : ℕ)
  (fₙ : fst C n → fst D n)
  (gₙ : fst C n → fst D n)
  (fₙ₊₁ : fst C (suc n) → fst D (suc n))
  (gₙ₊₁ : fst C (suc n) → fst D (suc n))
  (f-homₙ : (x : fst C n) → CW↪ D n (fₙ x) ≡ fₙ₊₁ (CW↪ C n x))
  (g-homₙ : (x : fst C n) → CW↪ D n (gₙ x) ≡ gₙ₊₁ (CW↪ C n x))
  (Hₙ : (x : C .fst n) → CW↪ D n (fₙ x) ≡ CW↪ D n (gₙ x))
  (Hₙ₊₁ : (x : C .fst (suc n)) →
         CW↪ D (suc n) (fₙ₊₁ x) ≡ CW↪ D (suc n) (gₙ₊₁ x))
  (Hₙ-coh : (c : C .fst n)
    → Square (cong (CW↪ D (suc n)) (Hₙ c))
              (Hₙ₊₁ (CW↪ C n c))
              (cong (CW↪ D (suc n)) (f-homₙ c))
              (cong (CW↪ D (suc n)) (g-homₙ c)))
     where
  open cellMap
  open cellHom
  open MMmaps C D
  open MMchainHomotopy C D n fₙ gₙ fₙ₊₁ gₙ₊₁ {!!} -- fₙ gₙ fₙ₊₁ gₙ₊₁ f-homₙ g-homₙ ? ? ?
  -- open preChainHomotopy C D f g H

--   -- an alternative extraction function, that will be useful in some computations
--   realiseMMmap2 : (n : ℕ) → (m1 m2 : (x : C .fst (suc n)) → cofiber n D)
--                  → MMmap n m1 m2 → Susp (cofiber n C) → Susp (cofiber n D)
--   realiseMMmap2 n m1 m2 e north = north
--   realiseMMmap2 n m1 m2 e south = north
--   realiseMMmap2 n m1 m2 e (merid (inl tt) i) = north
--   realiseMMmap2 n m1 m2 e (merid (inr x) i) = (merid (m1 x) ∙∙ refl ∙∙ (sym (merid (m2 x)))) i
--   realiseMMmap2 n m1 m2 e (merid (push x j) i) =
--     hcomp (λ k → λ { (i = i0) → merid (e x (~ j)) (~ k)
--                    ; (i = i1) → merid (m2 (CW↪ C n x)) (~ k)
--                    ; (j = i0) → merid (m2 (CW↪ C n x)) (~ k) })
--           (south)

--   -- auxiliary lemma which says the two realisation functions are equal
--   realiseMMmap1≡2 : (n : ℕ) → (m1 m2 : (x : C .fst (suc n)) → cofiber n D) (e : MMmap n m1 m2)
--     (x : Susp (cofiber n C)) → realiseMMmap n m1 m2 e x ≡ realiseMMmap2 n m1 m2 e x
--   realiseMMmap1≡2 n m1 m2 e north = refl
--   realiseMMmap1≡2 n m1 m2 e south = refl
--   realiseMMmap1≡2 n m1 m2 e (merid (inl tt) i) = refl
--   realiseMMmap1≡2 n m1 m2 e (merid (inr x) i) = refl
--   realiseMMmap1≡2 n m1 m2 e (merid (push x j) i) l =
--     hcomp (λ k → λ { (i = i0) → merid (e x ((~ j) ∧ l)) (~ k)
--                    ; (i = i1) → merid (m2 (CW↪ C n x)) (~ k)
--                    ; (j = i0) → merid (e x (i ∨ l)) (~ k) })
--           south

--   -- realisation of MMΣf is equal to Susp f
--   realiseMMΣcellMap : (f : cellMap C D) (x : Susp (cofiber n C)) →
--         realiseMMmap n (λ x → (inr (fₙ₊₁ x))) (λ x → inl tt) (MMΣcellMap n f) x
--         ≡ suspFun (prefunctoriality.fn+1/fn f n) x
--   realiseMMΣcellMap f x = realiseMMmap1≡2 n (λ x → (inr (fₙ₊₁ x))) (λ x → inl tt) (MMΣcellMap n f) x ∙ aux x
--     where
--       aux : (x : Susp (cofiber n C)) →
--         realiseMMmap2 n (λ x → (inr (fₙ₊₁ x))) (λ x → inl tt) (MMΣcellMap n f) x
--         ≡ suspFun (prefunctoriality.fn+1/fn f n) x
--       aux north = refl
--       aux south l = merid (inl tt) l
--       aux (merid (inl tt) i) l = merid (inl tt) (i ∧ l)
--       aux (merid (inr x) i) l =
--         hcomp (λ k → λ { (i = i0) → merid (inr (fₙ₊₁ x)) (~ k)
--                        ; (i = i1) → merid (inl tt) (l ∨ (~ k))
--                        ; (l = i1) → merid (inr (fₙ₊₁ x)) (~ k ∨ i) })
--               south
--       aux (merid (push x j) i) l =
--         hcomp (λ k → λ { (i = i0) → merid ((push (fₙ x) ∙ (cong inr (f .comm n x))) j) (~ k)
--                        ; (i = i1) → merid (inl tt) (l ∨ (~ k))
--                        ; (j = i0) → merid (inl tt) ((i ∧ l) ∨ (~ k))
--                        ; (l = i1) → merid ((push (fₙ x) ∙ (cong inr (f .comm n x))) j) (i ∨ (~ k)) })
--               south

--   -- realisation of MMΣf is equal to Susp f
--   realiseMMΣf : (x : Susp (cofiber n C)) →
--         realiseMMmap n (merid-f n) (merid-tt n) (MMΣf n) x
--         ≡ suspFun (prefunctoriality.fn+1/fn f n) x
--   realiseMMΣf = realiseMMΣcellMap f

--   -- realisation of MMΣg is equal to Susp g
--   realiseMMΣg : (x : Susp (cofiber n C)) →
--         realiseMMmap n (merid-g n) (merid-tt n) (MMΣg n) x
--         ≡ suspFun (prefunctoriality.fn+1/fn g n) x
--   realiseMMΣg = realiseMMΣcellMap g

--   -- a compact version of ∂ ∘ H
--   cof∂H : Susp (cofiber n C) → Susp (cofiber n D)
--   cof∂H north = north
--   cof∂H south = north
--   cof∂H (merid (inl tt) i) = north
--   cof∂H (merid (inr x) i) = ((merid (inr (fₙ₊₁ x))) ∙∙ refl ∙∙ (sym (merid (inr (gₙ₊₁ x))))) i
--   cof∂H (merid (push x j) i) =
--     hcomp (λ k → λ { (i = i0) → merid (inr (f .comm n x j)) (~ k)
--                    ; (i = i1) → merid (inr (g .comm n x j)) (~ k)
--                    ; (j = i0) → merid (inr (hom H n x i)) (~ k) })
--           (south)

--   -- realisation of MM∂H is equal to cof∂H
--   realiseMM∂H : (x : Susp (cofiber n C)) →
--     realiseMMmap n (merid-f n) (merid-g n) (MM∂H n) x
--     ≡ suspFun (to_cofiber n D) (δ (suc n) D (Hn+1/Hn n x))
--   realiseMM∂H x = aux2 x ∙ aux x
--     where
--       aux : (x : Susp (cofiber n C)) → cof∂H x ≡ suspFun (to_cofiber n D) (δ (suc n) D (Hn+1/Hn n x))
--       aux north = refl
--       aux south = refl
--       aux (merid (inl tt) i) = refl
--       aux (merid (inr x) i) j =
--         hcomp (λ k → λ { (i = i0) → merid (inr (fₙ₊₁ x)) (~ k)
--                        ; (i = i1) → merid (inr (gₙ₊₁ x)) (~ k)
--                        ; (j = i1) → suspFun (to_cofiber n D) (δ (suc n) D
--                             (doubleCompPath-filler (push (fₙ₊₁ x))
--                                                    (cong inr (H .hom (suc n) x))
--                                                    (sym (push (gₙ₊₁ x))) k i)) })
--               south
--       aux (merid (push x j) i) k =
--         hcomp (λ l → λ { (i = i0) → merid (inr (f .comm n x j)) (~ l)
--                        ; (i = i1) → merid (inr (g .comm n x j)) (~ l)
--                        ; (j = i0) → merid (inr (hom H n x i)) (~ l)
--                        ; (k = i1) → suspFun (to_cofiber n D) (δ (suc n) D
--                             (hfill (λ k → λ { (i = i0) → push (f .comm n x j) (~ k)
--                                           ; (i = i1) → push (g .comm n x j) (~ k)
--                                           ; (j = i0) → push (hom H n x i) (~ k) })
--                                    (inS (inr (H .coh n x j i))) l))})
--               south

--       aux2 : (x : Susp (cofiber n C)) →
--         realiseMMmap n (λ x → (inr (fₙ₊₁ x))) (λ x → (inr (gₙ₊₁ x))) (MM∂H n) x
--         ≡ cof∂H x
--       aux2 north = refl
--       aux2 south = refl
--       aux2 (merid (inl tt) i) = refl
--       aux2 (merid (inr x) i) = refl
--       aux2 (merid (push x j) i) l =
--         hcomp (λ k → λ { (i = i0) → merid (inr (f .comm n x (j ∨ (~ l)))) (~ k)
--                        ; (i = i1) → merid (inr (g .comm n x (j ∨ (~ l)))) (~ k)
--                        ; (j = i0) → merid (doubleCompPath-filler (sym (cong inr (f .comm n x)))
--                                                                  (cong inr (hom H n x))
--                                                                  (cong inr (g .comm n x)) (~ l) i) (~ k) })
--               south

--   -- realisation of MMΣH∂ is equal to Susp H∂
--   -- TODO: it is the same code as before. factorise!
--   realiseMMΣH∂ : (x : Susp (cofiber (suc n) C)) →
--         realiseMMmap (suc n) (λ x → inl tt) (λ x → inl tt) (MMΣH∂ (suc n)) x
--         ≡ suspFun ((Hn+1/Hn n) ∘ (suspFun (to_cofiber n C)) ∘ (δ (suc n) C)) x
--   realiseMMΣH∂ x = realiseMMmap1≡2 (suc n) (λ x → inl tt) (λ x → inl tt) (MMΣH∂ (suc n)) x ∙ aux x
--     where
--       aux : (x : Susp (cofiber (suc n) C)) →
--         realiseMMmap2 (suc n) (λ x → inl tt) (λ x → inl tt) (MMΣH∂ (suc n)) x
--         ≡ suspFun ((Hn+1/Hn n) ∘ (suspFun (to_cofiber n C)) ∘ (δ (suc n) C)) x
--       aux north = refl
--       aux south l = merid (inl tt) l
--       aux (merid (inl tt) i) l = merid (inl tt) (i ∧ l)
--       aux (merid (inr x) i) l =
--         hcomp (λ k → λ { (i = i0) → merid (inl tt) (~ k)
--                        ; (i = i1) → merid (inl tt) (l ∨ (~ k))
--                        ; (l = i1) → merid (inl tt) (~ k ∨ i) })
--               south
--       aux (merid (push x j) i) l =
--         hcomp (λ k → λ { (i = i0) → merid (((push (fₙ₊₁ x)) ∙∙ (cong inr (H .hom (suc n) x))
--                                           ∙∙ (sym (push (gₙ₊₁ x)))) j) (~ k)
--                        ; (i = i1) → merid (inl tt) (l ∨ (~ k))
--                        ; (j = i0) → merid (inl tt) ((i ∧ l) ∨ (~ k))
--                        ; (l = i1) → merid (((push (fₙ₊₁ x)) ∙∙ (cong inr (H .hom (suc n) x))
--                                           ∙∙ (sym (push (gₙ₊₁ x)))) j) (i ∨ (~ k)) })
--               south

-- -- Then, we connect the addition of MMmaps to the addition of abelian maps
-- module bouquetAdd where
--   -- keeping imports here for now
--   open import Cubical.ZCohomology.Base
--   open import Cubical.ZCohomology.Properties
--   open import Cubical.ZCohomology.GroupStructure
--   open import Cubical.HITs.Truncation as TR hiding (map)
--   open import Cubical.HITs.Sn
--   open import Cubical.HITs.S1
--   open import Cubical.Foundations.Path
--   open import Cubical.ZCohomology.Groups.Sn
--   open import Cubical.HITs.SetTruncation as ST hiding (map)

--   open MMmaps

--   module _ (C D : CW) (n : ℕ) (m1 m2 : (x : C .fst (suc n)) → cofiber n D)
--             (f : MMmap C D n m1 m2)
--             (a : CW-fields.A D n) where

--     bouquetMMmap∈cohom-raw : (t : CW-fields.A C n) → S₊ (suc n) → S₊ (suc n)
--     bouquetMMmap∈cohom-raw t x = chooseS a (bouquetMMmap C D n m1 m2 f (inr (t , x)))

--     bouquetMMmap∈cohom : (t : CW-fields.A C n)  → S₊ (suc n) → coHomK (suc n)
--     bouquetMMmap∈cohom t x = ∣ bouquetMMmap∈cohom-raw t x ∣ₕ

--     bouquetMMmap∈cohom' : (x : Susp (cofiber n C)) → coHomK (suc n)
--     bouquetMMmap∈cohom' x = ∣ chooseS a (Iso.fun (cofibIso n D) (realiseMMmap C D n m1 m2 f x)) ∣ₕ

--   --
--   realiseAdd-merid : (C D : CW) (n : ℕ) (m1 m2 m3 : (x : C .fst (suc n)) → cofiber n D)
--             (f : MMmap C D n m1 m2)
--             (g : MMmap C D n m2 m3)
--      → (b : _)
--      → Square (λ j → (realiseMMmap C D n m1 m2 f (merid b j)))
--                (λ j →  (realiseMMmap C D n m1 m3
--                          (MMmap-add C D n m1 m2 m3 f g) (merid b j)))
--                (λ _ → north)
--                (λ i →  realiseMMmap C D n m2 m3 g (merid b i))
--   realiseAdd-merid C D n m1 m2 m3 f g (inl tt) i j = north
--   realiseAdd-merid C D n m1 m2 m3 f g (inr x) i j =
--     hcomp (λ k → λ { (i ∨ j = i0) → merid (m1 x) (~ k)
--                    ; (i ∨ (~ j) = i0) → merid (m2 x) (~ k)
--                    ; (i ∧ (~ j) = i1) → merid (m1 x) (~ k)
--                    ; (i ∧ j = i1) → merid (m3 x) (~ k)
--                    ; (j = i0) → merid (m1 x) (~ k) })
--           south
--   realiseAdd-merid C D n m1 m2 m3 f g (push a l) i j =
--     hcomp (λ k → λ { (i ∨ j = i0) → merid (m1 (CW↪ C n a)) (~ k)
--                    ; (i ∨ (~ j) = i0) → merid (m2 (CW↪ C n a)) (~ k)
--                    ; (i ∨ l = i0) → merid (f a j) (~ k)
--                    ; (i ∧ (~ j) = i1) → merid (m1 (CW↪ C n a)) (~ k)
--                    ; (i ∧ j = i1) → merid (m3 (CW↪ C n a)) (~ k)
--                    ; (i ∧ (~ l) = i1) → merid (MMmap-add C D n m1 m2 m3 f g a j) (~ k)
--                    ; (j = i0) → merid (m1 (CW↪ C n a)) (~ k)
--                    ; (j ∧ (~ l) = i1) → merid (g a i) (~ k)
--                    ; (l = i0) → merid (doubleCompPath-filler (refl) (f a) (g a) i j) (~ k) })
--           south

--   bouquetMMmap∈cohom'+ : (C D : CW) (n : ℕ) (m1 m2 m3 : (x : C .fst (suc n)) → cofiber n D)
--             (f : MMmap C D n m1 m2)
--             (g : MMmap C D n m2 m3)
--             (a : CW-fields.A D n)
--             (x : _)
--          → bouquetMMmap∈cohom' C D n m1 m3 (MMmap-add C D n m1 m2 m3 f g) a x
--          ≡ bouquetMMmap∈cohom' C D n m1 m2 f a x
--         +ₖ bouquetMMmap∈cohom' C D n m2 m3 g a x
--   bouquetMMmap∈cohom'+ C D zero m1 m2 m3 f g a north = refl
--   bouquetMMmap∈cohom'+ C D zero m1 m2 m3 f g a south = refl
--   bouquetMMmap∈cohom'+ C D zero m1 m2 m3 f g a (merid b i) j =
--     ((sym (PathP→compPathL (help b))
--       ∙ sym (lUnit _))
--     ∙ ∙≡+₁ (λ i → bouquetMMmap∈cohom' C D zero m1 m2 f a (merid b i))
--            (λ i → bouquetMMmap∈cohom' C D zero m2 m3 g a (merid b i))) j i
--     where
--     help : (b : _)
--       → PathP (λ i → ∣ base ∣ₕ ≡ cong (bouquetMMmap∈cohom' C D zero m2 m3 g a) (merid b) i)
--            (cong (bouquetMMmap∈cohom' C D zero m1 m2 f a) (merid b))
--            (cong (bouquetMMmap∈cohom' C D zero m1 m3 (MMmap-add C D zero m1 m2 m3 f g) a) (merid b))
--     help b i j = ∣ chooseS a (Iso.fun (cofibIso zero D) (realiseAdd-merid C D zero m1 m2 m3 f g b i j)) ∣ₕ
--   bouquetMMmap∈cohom'+ C D (suc n) m1 m2 m3 f g a north = refl
--   bouquetMMmap∈cohom'+ C D (suc n) m1 m2 m3 f g a south = refl
--   bouquetMMmap∈cohom'+ C D (suc n) m1 m2 m3 f g a (merid b i) j =
--     ((sym (PathP→compPathL (help b))
--       ∙ sym (lUnit _))
--     ∙ ∙≡+₂ n (λ i → bouquetMMmap∈cohom' C D (suc n) m1 m2 f a (merid b i))
--            (λ i → bouquetMMmap∈cohom' C D (suc n) m2 m3 g a (merid b i))) j i
--     where
--     help : (b : _)
--       → PathP (λ i → ∣ north ∣ₕ ≡ cong (bouquetMMmap∈cohom' C D (suc n) m2 m3 g a) (merid b) i)
--            (cong (bouquetMMmap∈cohom' C D (suc n) m1 m2 f a) (merid b))
--            (cong (bouquetMMmap∈cohom' C D (suc n) m1 m3 (MMmap-add C D (suc n) m1 m2 m3 f g) a) (merid b))
--     help b i j = ∣ chooseS a (Iso.fun (cofibIso (suc n) D) (realiseAdd-merid C D (suc n) m1 m2 m3 f g b i j)) ∣ₕ

--   bouquetMMmap∈cohom+ : (C D : CW) (n : ℕ) (m1 m2 m3 : (x : C .fst (suc n)) → cofiber n D)
--             (f : MMmap C D n m1 m2)
--             (g : MMmap C D n m2 m3)
--             (t : CW-fields.A C n)
--             (a : CW-fields.A D n)
--             (x : S₊ (suc n))
--          → bouquetMMmap∈cohom C D n m1 m3 (MMmap-add C D n m1 m2 m3 f g) a t x
--          ≡ bouquetMMmap∈cohom C D n m1 m2 f a t x
--         +ₖ bouquetMMmap∈cohom C D n m2 m3 g a t x
--   bouquetMMmap∈cohom+ C D n m1 m2 m3 f g t a x =
--     bouquetMMmap∈cohom'+ C D n m1 m2 m3 f g a (Iso.inv (cofibIso n C) (inr (t , x)))

--   module _  (C D : CW) (n : ℕ) (m1 m2 m3 : (x : C .fst (suc n)) → cofiber n D)
--             (f : MMmap C D n m1 m2) (g : MMmap C D n m2 m3) where
--     realiseMMmap-hom : bouquetDegree (bouquetMMmap C D n m1 m3 (MMmap-add C D n m1 m2 m3 f g))
--                      ≡ addGroupHom _ _ (bouquetDegree (bouquetMMmap C D n m1 m2 f))
--                                        (bouquetDegree (bouquetMMmap C D n m2 m3 g))
--     realiseMMmap-hom =
--       EqHoms λ t → funExt λ a
--         → sym (generator-is-generator'
--                 (λ a₁ → degree (suc n)
--                   λ x → chooseS a (bouquetMMmap C D n m1 m3 (MMmap-add C D n m1 m2 m3 f g)
--                            (inr (a₁ , x)))) t)
--          ∙ cong (fst (Hⁿ-Sⁿ≅ℤ n) .Iso.fun ∘ ∣_∣₂)
--                 (funExt (bouquetMMmap∈cohom+ C D n m1 m2 m3 f g t a))
--         ∙∙ IsGroupHom.pres· (snd (Hⁿ-Sⁿ≅ℤ n))
--              (∣ (λ x → ∣ chooseS a (bouquetMMmap C D n m1 m2 f (inr (t , x))) ∣ₕ) ∣₂)
--              (∣ (λ x → ∣ chooseS a (bouquetMMmap C D n m2 m3 g (inr (t , x))) ∣ₕ) ∣₂)
--         ∙∙ cong₂ _+_ (generator-is-generator'
--                 (λ a₁ → degree (suc n)
--                   λ x → chooseS a (bouquetMMmap C D n m1 m2 f
--                            (inr (a₁ , x)))) t)
--                       (generator-is-generator'
--                 (λ a₁ → degree (suc n)
--                   λ x → chooseS a (bouquetMMmap C D n m2 m3 g
--                            (inr (a₁ , x)))) t)

-- -- Now we have all the ingredients, we can get the chain homotopy equation
-- module chainHomEquation (C D : CW) (f g : cellMap C D) (H : cellHom f g) (n : ℕ) where
--   open cellMap
--   open MMmaps C D (suc n)
--   open MMchainHomotopy C D f g H (suc n)
--   open preChainHomotopy C D f g H
--   open realiseMMmap C D f g H

--   -- The four abelian group maps that are involved in the equation
--   ∂H H∂ fn+1 gn+1 : AbGroupHom (ℤ[A C ] (suc n)) (ℤ[A D ] (suc n))

--   ∂H = compGroupHom (chainHomotopy (suc n)) (∂ D (suc n))
--   H∂ = compGroupHom (∂ C n) (chainHomotopy n)
--   fn+1 = prefunctoriality.chainFunct f (suc n)
--   gn+1 = prefunctoriality.chainFunct g (suc n)

--   -- Technical lemma regarding suspensions of Iso's
--   suspIso-suspFun : {A B C D : Type} (e1 : Iso A B) (e2 : Iso C D) (f : C → A)
--     → Iso.fun (congSuspIso e1) ∘ (suspFun f) ∘ Iso.inv (congSuspIso e2) ≡ suspFun (Iso.fun e1 ∘ f ∘ Iso.inv e2)
--   suspIso-suspFun e1 e2 f i north = north
--   suspIso-suspFun e1 e2 f i south = south
--   suspIso-suspFun e1 e2 f i (merid a j) = merid ((Iso.fun e1 ∘ f ∘ Iso.inv e2) a) j

--   BouquetIso : ∀ C n → Iso (cofiber n C) (SphereBouquet n (Fin (CW-fields.card C n)))
--   BouquetIso C n = BouquetIso-gen n (CW-fields.card C n) (CW-fields.α C n) (CW-fields.e C n)

--   -- Technical lemma to pull bouquetSusp out of a suspended cofiber map
--   cofibIso-suspFun : (n : ℕ) (C D : CW) (f : cofiber n C → cofiber n D) →
--     Iso.fun (cofibIso n D) ∘ (suspFun f) ∘ Iso.inv (cofibIso n C)
--     ≡ bouquetSusp→ ((Iso.fun (BouquetIso D n)) ∘ f ∘ Iso.inv (BouquetIso C n))
--   cofibIso-suspFun n C D f = cong (λ X → Iso.fun sphereBouquetSuspIso ∘ X ∘ Iso.inv sphereBouquetSuspIso)
--                                   (suspIso-suspFun (BouquetIso D n) (BouquetIso C n) f)

--   -- connecting MM∂H to ∂H
--   bouquet∂H : bouquetDegree (bouquetMMmap merid-f merid-g MM∂H) ≡ ∂H
--   bouquet∂H =
--     cong (λ X → bouquetDegree ((Iso.fun (cofibIso (suc n) D)) ∘ X ∘ (Iso.inv (cofibIso (suc n) C))))
--          (funExt (realiseMM∂H (suc n)))
--       ∙ cong bouquetDegree ιδH≡pre∂∘H
--       ∙ degreeComp (preboundary.pre∂ D (suc n)) (bouquetHomotopy (suc n))
--     where
--       ιδH : SphereBouquet (suc (suc n)) (Fin (CW-fields.card C (suc n)))
--           → SphereBouquet (suc (suc n)) (Fin (CW-fields.card D (suc n)))
--       ιδH = Iso.fun (cofibIso (suc n) D) ∘ suspFun (to_cofiber (suc n) D) ∘ δ (suc (suc n)) D
--             ∘ Hn+1/Hn (suc n) ∘ Iso.inv (cofibIso (suc n) C)

--       ιδH≡pre∂∘H : ιδH ≡ (preboundary.pre∂ D (suc n)) ∘ bouquetHomotopy (suc n)
--       ιδH≡pre∂∘H = cong (λ X → Iso.fun (cofibIso (suc n) D) ∘ suspFun (to_cofiber (suc n) D)
--                                ∘ δ (suc (suc n)) D ∘ X ∘ Hn+1/Hn (suc n)
--                                ∘ Iso.inv (cofibIso (suc n) C))
--                         (sym (funExt (Iso.leftInv (BouquetIso D (suc (suc n))))))

--   -- connecting MMΣH∂ to H∂
--   bouquetΣH∂ : bouquetDegree (bouquetMMmap merid-tt merid-tt MMΣH∂) ≡ H∂
--   bouquetΣH∂ =
--     cong (λ X → bouquetDegree ((Iso.fun (cofibIso (suc n) D)) ∘ X ∘ (Iso.inv (cofibIso (suc n) C))))
--          (funExt (realiseMMΣH∂ n))
--       ∙ cong bouquetDegree
--              (cofibIso-suspFun (suc n) C D (Hn+1/Hn n ∘ suspFun (to_cofiber n C) ∘ δ (suc n) C))
--       ∙ sym (degreeSusp Hιδ)
--       ∙ cong bouquetDegree Hιδ≡H∘pre∂
--       ∙ degreeComp (bouquetHomotopy n) (preboundary.pre∂ C n)
--     where
--       Hιδ : SphereBouquet (suc n) (Fin (CW-fields.card C (suc n)))
--           → SphereBouquet (suc n) (Fin (CW-fields.card D (suc n)))
--       Hιδ = Iso.fun (BouquetIso D (suc n)) ∘ (Hn+1/Hn n) ∘ suspFun (to_cofiber n C)
--             ∘ δ (suc n) C ∘ Iso.inv (BouquetIso C (suc n))

--       Hιδ≡H∘pre∂ : Hιδ ≡ bouquetHomotopy n ∘ (preboundary.pre∂ C n)
--       Hιδ≡H∘pre∂ = cong (λ X → Iso.fun (BouquetIso D (suc n)) ∘ (Hn+1/Hn n) ∘ X
--                                ∘ suspFun (to_cofiber n C) ∘ δ (suc n) C
--                                ∘ Iso.inv (BouquetIso C (suc n)))
--                         (sym (funExt (Iso.leftInv (cofibIso n C))))

--   -- connecting MMΣf to fn+1
--   bouquetΣf : bouquetDegree (bouquetMMmap merid-f merid-tt MMΣf) ≡ fn+1
--   bouquetΣf =
--     cong (λ X → bouquetDegree ((Iso.fun (cofibIso (suc n) D)) ∘ X ∘ (Iso.inv (cofibIso (suc n) C))))
--          (funExt (realiseMMΣf (suc n)))
--     ∙ (cong bouquetDegree (cofibIso-suspFun (suc n) C D (prefunctoriality.fn+1/fn f (suc n))))
--     ∙ sym (degreeSusp (prefunctoriality.bouquetFunct f (suc n)))

--   -- connecting MMΣg to gn+1
--   bouquetΣg : bouquetDegree (bouquetMMmap merid-g merid-tt MMΣg) ≡ gn+1
--   bouquetΣg =
--     cong (λ X → bouquetDegree ((Iso.fun (cofibIso (suc n) D)) ∘ X ∘ (Iso.inv (cofibIso (suc n) C))))
--          (funExt (realiseMMΣg (suc n)))
--     ∙ (cong bouquetDegree (cofibIso-suspFun (suc n) C D (prefunctoriality.fn+1/fn g (suc n))))
--     ∙ sym (degreeSusp (prefunctoriality.bouquetFunct g (suc n)))

--   -- Alternative formulation of the chain homotopy equation
--   chainHomotopy1 : addGroupHom _ _ (addGroupHom _ _ ∂H gn+1) H∂ ≡ fn+1
--   chainHomotopy1 = cong (λ X → addGroupHom _ _ X H∂) aux
--                    ∙ aux2
--                    ∙ cong (λ X → bouquetDegree (bouquetMMmap merid-f merid-tt X)) (funExt MMchainHomotopy)
--                    ∙ bouquetΣf
--     where
--       MM∂H+MMΣg = MMmap-add merid-f merid-g merid-tt MM∂H MMΣg
--       MM∂H+MMΣg+MMΣH∂ = MMmap-add merid-f merid-tt merid-tt MM∂H+MMΣg MMΣH∂

--       aux : addGroupHom _ _ ∂H gn+1
--         ≡ bouquetDegree (bouquetMMmap merid-f merid-tt MM∂H+MMΣg)
--       aux = cong₂ (λ X Y → addGroupHom _ _ X Y) (sym bouquet∂H) (sym bouquetΣg)
--             ∙ sym (bouquetAdd.realiseMMmap-hom C D (suc n) merid-f merid-g merid-tt MM∂H MMΣg)

--       aux2 : addGroupHom _ _ (bouquetDegree (bouquetMMmap merid-f merid-tt MM∂H+MMΣg)) H∂
--         ≡ bouquetDegree (bouquetMMmap merid-f merid-tt MM∂H+MMΣg+MMΣH∂)
--       aux2 = cong (addGroupHom _ _ (bouquetDegree (bouquetMMmap merid-f merid-tt MM∂H+MMΣg)))
--                   (sym bouquetΣH∂)
--              ∙ sym (bouquetAdd.realiseMMmap-hom C D (suc n) merid-f merid-tt merid-tt MM∂H+MMΣg MMΣH∂)

--   -- Standard formulation of the chain homotopy equation
--   chainHomotopy2 : subtrGroupHom _ _ fn+1 gn+1 ≡ addGroupHom _ _ ∂H H∂
--   chainHomotopy2 = GroupHom≡ (funExt λ x → aux (fn+1 .fst x) (∂H .fst x) (gn+1 .fst x)
--                      (H∂ .fst x) (cong (λ X → X .fst x) chainHomotopy1))
--     where
--       open AbGroupStr (snd (ℤ[A D ] (suc n))) renaming (_+_ to _+G_ ; -_ to -G_ ; +Assoc to +AssocG ; +Comm to +CommG)
--       aux : ∀ w x y z → (x +G y) +G z ≡ w → w +G (-G y) ≡ x +G z
--       aux w x y z H = cong (λ X → X +G (-G y)) (sym H)
--         ∙ sym (+AssocG (x +G y) z (-G y))
--         ∙ cong (λ X → (x +G y) +G X) (+CommG z (-G y))
--         ∙ +AssocG (x +G y) (-G y) z
--         ∙ cong (λ X → X +G z) (sym (+AssocG x y (-G y))
--                               ∙ cong (λ X → x +G X) (+InvR y)
--                               ∙ +IdR x)

-- -- Going from a cell homotopy to a chain homotopy
-- cellHom-to-ChainHomotopy : {C D : CW} {f g : cellMap C D} (H : cellHom f g)
--                          → ChainHomotopy (cellMap-to-ChainComplexMap f) (cellMap-to-ChainComplexMap g)
-- cellHom-to-ChainHomotopy {C} {D} {f} {g} H .ChainHomotopy.htpy n = preChainHomotopy.chainHomotopy C D f g H n
-- cellHom-to-ChainHomotopy {C} {D} {f} {g} H .ChainHomotopy.bdryhtpy n = chainHomEquation.chainHomotopy2 C D f g H n
