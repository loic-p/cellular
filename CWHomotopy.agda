{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

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

module CWHomotopy where

record cellHom {C D : CW} (f g : cellMap C D) : Type where
  open cellMap
  field
    hom : (n : ℕ) → (x : C .fst n) → CW↪ D n (f .map n x) ≡ CW↪ D n (g .map n x)
    coh : (n : ℕ) → (c : C .fst n) → Square (cong (CW↪ D (suc n)) (hom n c))
                                            (hom (suc n) (CW↪ C n c))
                                            (cong (CW↪ D (suc n)) (f .comm n c))
                                            (cong (CW↪ D (suc n)) (g .comm n c))

-- MMmaps (Meridian-to-Meridian maps) are a convenient abstraction for the kind of maps
-- Susp (cofiber n C) → Susp (cofiber n D) that we are going to manipulate
MMmap : (C D : CW) (n : ℕ) (m1 m2 : (x : C .fst (suc n)) → cofiber n D) → Type
MMmap C D n m1 m2 = (x : C .fst n) → m1 (CW↪ C n x) ≡ m2 (CW↪ C n x)

-- Addition of MMmaps
MMmap-add : (C D : CW) (n : ℕ) (m1 m2 m3 : (x : C .fst (suc n)) → cofiber n D)
          → MMmap C D n m1 m2 → MMmap C D n m2 m3 → MMmap C D n m1 m3
MMmap-add C D n m1 m2 m3 e1 e2 x = (e1 x) ∙ (e2 x)

-- Extracting a map between suspensions of cofibers from a MMmap
realiseMMmap : (C D : CW) (n : ℕ) (m1 m2 : (x : C .fst (suc n)) → cofiber n D)
               → MMmap C D n m1 m2 → Susp (cofiber n C) → Susp (cofiber n D)
realiseMMmap C D n m1 m2 e north = north
realiseMMmap C D n m1 m2 e south = north
realiseMMmap C D n m1 m2 e (merid (inl tt) i) = north
realiseMMmap C D n m1 m2 e (merid (inr x) i) = (merid (m1 x) ∙∙ refl ∙∙ (sym (merid (m2 x)))) i
realiseMMmap C D n m1 m2 e (merid (push x j) i) =
  hcomp (λ k → λ { (i = i0) → merid (m1 (CW↪ C n x)) (~ k)
                 ; (i = i1) → merid (m2 (CW↪ C n x)) (~ k)
                 ; (j = i0) → merid (e x i) (~ k) })
        (south)

-- an alternative extraction function, that will be useful in some computations
realiseMMmap2 : (C D : CW) (n : ℕ) (m1 m2 : (x : C .fst (suc n)) → cofiber n D)
               → MMmap C D n m1 m2 → Susp (cofiber n C) → Susp (cofiber n D)
realiseMMmap2 C D n m1 m2 e north = north
realiseMMmap2 C D n m1 m2 e south = north
realiseMMmap2 C D n m1 m2 e (merid (inl tt) i) = north
realiseMMmap2 C D n m1 m2 e (merid (inr x) i) = (merid (m1 x) ∙∙ refl ∙∙ (sym (merid (m2 x)))) i
realiseMMmap2 C D n m1 m2 e (merid (push x j) i) =
  hcomp (λ k → λ { (i = i0) → merid (e x (~ j)) (~ k)
                 ; (i = i1) → merid (m2 (CW↪ C n x)) (~ k)
                 ; (j = i0) → merid (m2 (CW↪ C n x)) (~ k) })
        (south)

-- the suspension of a cell map as a MMmap
MMΣcellMap : {C D : CW} (f : cellMap C D) (n : ℕ)
     → MMmap C D n (λ x → (inr (f .cellMap.map (suc n) x))) (λ x → inl tt)
MMΣcellMap f n x = sym (push (f .cellMap.map n x) ∙ (cong inr (f .cellMap.comm n x)))

-- Now let's extract a chain homotopy from a cellular homotopy
module _ (C D : CW) (f g : cellMap C D) (H : cellHom f g) where
  open cellMap
  open cellHom

  module _ (n : ℕ) where
    -- here is the homotopy H
    -- H is expressed as a map Susp (cofiber n C) → cofiber (suc n) D
    -- since cofibers are isomorphique to sphere bouquets, H represents a map between free groups
    Hn+1/Hn : Susp (cofiber n C) → cofiber (suc n) D
    Hn+1/Hn north = inl tt
    Hn+1/Hn south = inl tt
    Hn+1/Hn (merid (inl tt) i) = inl tt
    Hn+1/Hn (merid (inr x) i) = ((push (f .map (suc n) x)) ∙∙ (cong inr (H .hom (suc n) x)) ∙∙ (sym (push (g .map (suc n) x)))) i
    Hn+1/Hn (merid (push x j) i) =
      hcomp (λ k → λ { (i = i0) → push (f .comm n x j) (~ k)
                     ; (i = i1) → push (g .comm n x j) (~ k)
                     ; (j = i0) → push (hom H n x i) (~ k) })
            (inr (H .coh n x j i))

    -- Now, we want to prove that H is a chain homotopy, ie that ∂H + H∂ = f - g
    -- we start by defining a compact version of ∂H
    ∂H : Susp (cofiber n C) → Susp (cofiber n D)
    ∂H north = north
    ∂H south = north
    ∂H (merid (inl tt) i) = north
    ∂H (merid (inr x) i) = ((merid (inr (f .map (suc n) x))) ∙∙ refl ∙∙ (sym (merid (inr (g .map (suc n) x))))) i
    ∂H (merid (push x j) i) =
      hcomp (λ k → λ { (i = i0) → merid (inr (f .comm n x j)) (~ k)
                     ; (i = i1) → merid (inr (g .comm n x j)) (~ k)
                     ; (j = i0) → merid (inr (hom H n x i)) (~ k) })
            (south)

    -- and then, here is ∂H as a MMmap
    merid-f merid-g merid-tt : (x : C .fst (suc n)) → cofiber n D
    merid-f = λ x → inr (f .map (suc n) x)
    merid-g = λ x → inr (g .map (suc n) x)
    merid-tt = λ x → inl tt

    MM∂H : MMmap C D n merid-f merid-g
    MM∂H x = (sym (cong inr (f .comm n x))) ∙∙ (cong inr (hom H n x)) ∙∙ (cong inr (g .comm n x))

    -- the suspension of f as a MMmap
    MMΣf : MMmap C D n merid-f merid-tt
    MMΣf = MMΣcellMap f n

    -- the suspension of g as a MMmap
    MMΣg : MMmap C D n merid-g merid-tt
    MMΣg = MMΣcellMap g n -- sym (push (f .cellMap.map n x) ∙ (cong inr (f .cellMap.comm n x)))

    -- the suspension of H∂ as a MMmap
    MMΣH∂ : MMmap C D n merid-tt merid-tt
    MMΣH∂ x = sym ((push (f .map n x)) ∙∙ (cong inr (H .hom n x)) ∙∙ (sym (push (g .map n x))))

    -- the chain homotopy equation at the level of MMmaps
    MMchainHomotopy : ∀ x →
      MMmap-add C D n merid-f merid-g merid-tt MM∂H MMΣg x
      ≡ MMmap-add C D n merid-f merid-tt merid-tt MMΣf MMΣH∂ x
    MMchainHomotopy x = {!!} -- Square→compPath help
      where
      open import Cubical.Foundations.GroupoidLaws
      open import Cubical.Foundations.Path
      
      help : Square (MMΣf x) (MMΣg x) (MM∂H x) (sym (MMΣH∂ x))
      help i j =
         hcomp (λ k → λ {(i = i0) → compPath-filler (push (f .map n x)) (λ i₁ → inr (f .comm n x i₁)) k (~ j)
                       ; (i = i1) → compPath-filler (push (g .map n x)) (λ i₁ → inr (g .comm n x i₁)) k (~ j)
                       ; (j = i1) → (push (f .map n x) ∙∙ (λ i → inr (H .hom n x i)) ∙∙ (λ i₁ → push (g .map n x) (~ i₁))) i})
                (doubleCompPath-filler  (push (f .map n x)) (λ i → (inr (H .hom n x i))) (λ i₁ → push (g .map n x) (~ i₁)) j i)

  -- in this module, we prove that decoding the MMmaps results in the intended functions
  module _ (n : ℕ) where

    -- realisation of MM∂H is equal to ∂H
    realiseMM∂H : (x : Susp (cofiber n C)) →
      realiseMMmap C D n (λ x → (inr (f .map (suc n) x))) (λ x → (inr (g .map (suc n) x))) (MM∂H n) x
      ≡ suspFun (to_cofiber n D) (δ (suc n) D (Hn+1/Hn n x))
    realiseMM∂H x = aux2 x ∙ aux x
      where
        aux : (x : Susp (cofiber n C)) → ∂H n x ≡ suspFun (to_cofiber n D) (δ (suc n) D (Hn+1/Hn n x))
        aux north = refl
        aux south = refl
        aux (merid (inl tt) i) = refl
        aux (merid (inr x) i) j =
          hcomp (λ k → λ { (i = i0) → merid (inr (f .map (suc n) x)) (~ k)
                         ; (i = i1) → merid (inr (g .map (suc n) x)) (~ k)
                         ; (j = i1) → suspFun (to_cofiber n D) (δ (suc n) D
                              (doubleCompPath-filler (push (f .map (suc n) x))
                                                     (cong inr (H .hom (suc n) x))
                                                     (sym (push (g .map (suc n) x))) k i)) })
                south
        aux (merid (push x j) i) k =
          hcomp (λ l → λ { (i = i0) → merid (inr (f .comm n x j)) (~ l)
                         ; (i = i1) → merid (inr (g .comm n x j)) (~ l)
                         ; (j = i0) → merid (inr (hom H n x i)) (~ l)
                         ; (k = i1) → suspFun (to_cofiber n D) (δ (suc n) D
                              (hfill (λ k → λ { (i = i0) → push (f .comm n x j) (~ k)
                                            ; (i = i1) → push (g .comm n x j) (~ k)
                                            ; (j = i0) → push (hom H n x i) (~ k) })
                                     (inS (inr (H .coh n x j i))) l))})
                south

        aux2 : (x : Susp (cofiber n C)) →
          realiseMMmap C D n (λ x → (inr (f .map (suc n) x))) (λ x → (inr (g .map (suc n) x))) (MM∂H n) x
          ≡ ∂H n x
        aux2 north = refl
        aux2 south = refl
        aux2 (merid (inl tt) i) = refl
        aux2 (merid (inr x) i) = refl
        aux2 (merid (push x j) i) l =
          hcomp (λ k → λ { (i = i0) → merid (inr (f .comm n x (j ∨ (~ l)))) (~ k)
                         ; (i = i1) → merid (inr (g .comm n x (j ∨ (~ l)))) (~ k)
                         ; (j = i0) → merid (doubleCompPath-filler (sym (cong inr (f .comm n x)))
                                                                   (cong inr (hom H n x))
                                                                   (cong inr (g .comm n x)) (~ l) i) (~ k) })
                south

    -- auxiliary lemma which says the two realisation functions are equal
    realiseMMmap1≡2 : (C D : CW) (n : ℕ) (m1 m2 : (x : C .fst (suc n)) → cofiber n D) (e : MMmap C D n m1 m2)
      (x : Susp (cofiber n C)) → realiseMMmap C D n m1 m2 e x ≡ realiseMMmap2 C D n m1 m2 e x
    realiseMMmap1≡2 C D n m1 m2 e north = refl
    realiseMMmap1≡2 C D n m1 m2 e south = refl
    realiseMMmap1≡2 C D n m1 m2 e (merid (inl tt) i) = refl
    realiseMMmap1≡2 C D n m1 m2 e (merid (inr x) i) = refl
    realiseMMmap1≡2 C D n m1 m2 e (merid (push x j) i) l =
      hcomp (λ k → λ { (i = i0) → merid (e x ((~ j) ∧ l)) (~ k)
                     ; (i = i1) → merid (m2 (CW↪ C n x)) (~ k)
                     ; (j = i0) → merid (e x (i ∨ l)) (~ k) })
            south

    -- realisation of MMΣf is equal to Susp f
    realiseMMΣcellMap : (f : cellMap C D) (x : Susp (cofiber n C)) →
          realiseMMmap C D n (λ x → (inr (f .map (suc n) x))) (λ x → inl tt) (MMΣcellMap f n) x
          ≡ suspFun (prefunctoriality.fn+1/fn f n) x
    realiseMMΣcellMap f x = realiseMMmap1≡2 C D n (λ x → (inr (f .map (suc n) x))) (λ x → inl tt) (MMΣcellMap f n) x ∙ aux x
      where
        aux : (x : Susp (cofiber n C)) →
          realiseMMmap2 C D n (λ x → (inr (f .map (suc n) x))) (λ x → inl tt) (MMΣcellMap f n) x
          ≡ suspFun (prefunctoriality.fn+1/fn f n) x
        aux north = refl
        aux south l = merid (inl tt) l
        aux (merid (inl tt) i) l = merid (inl tt) (i ∧ l)
        aux (merid (inr x) i) l =
          hcomp (λ k → λ { (i = i0) → merid (inr (f .map (suc n) x)) (~ k)
                         ; (i = i1) → merid (inl tt) (l ∨ (~ k))
                         ; (l = i1) → merid (inr (f .map (suc n) x)) (~ k ∨ i) })
                south
        aux (merid (push x j) i) l =
          hcomp (λ k → λ { (i = i0) → merid ((push (f .map n x) ∙ (cong inr (f .comm n x))) j) (~ k)
                         ; (i = i1) → merid (inl tt) (l ∨ (~ k))
                         ; (j = i0) → merid (inl tt) ((i ∧ l) ∨ (~ k))
                         ; (l = i1) → merid ((push (f .map n x) ∙ (cong inr (f .comm n x))) j) (i ∨ (~ k)) })
                south

    -- realisation of MMΣf is equal to Susp f
    realiseMMΣf : (x : Susp (cofiber n C)) →
          realiseMMmap C D n (λ x → (inr (f .map (suc n) x))) (λ x → inl tt) (MMΣf n) x
          ≡ suspFun (prefunctoriality.fn+1/fn f n) x
    realiseMMΣf = realiseMMΣcellMap f

    -- realisation of MMΣg is equal to Susp g
    realiseMMΣg : (x : Susp (cofiber n C)) →
          realiseMMmap C D n (λ x → (inr (g .map (suc n) x))) (λ x → inl tt) (MMΣg n) x
          ≡ suspFun (prefunctoriality.fn+1/fn g n) x
    realiseMMΣg = realiseMMΣcellMap g

    -- realisation of MMΣH∂ is equal to Susp H∂
    -- TODO: it is the same code as before. factorise!
    realiseMMΣH∂ : (x : Susp (cofiber (suc n) C)) →
          realiseMMmap C D (suc n) (λ x → inl tt) (λ x → inl tt) (MMΣH∂ (suc n)) x
          ≡ suspFun ((Hn+1/Hn n) ∘ (suspFun (to_cofiber n C)) ∘ (δ (suc n) C)) x
    realiseMMΣH∂ x = realiseMMmap1≡2 C D (suc n) (λ x → inl tt) (λ x → inl tt) (MMΣH∂ (suc n)) x ∙ aux x
      where
        aux : (x : Susp (cofiber (suc n) C)) →
          realiseMMmap2 C D (suc n) (λ x → inl tt) (λ x → inl tt) (MMΣH∂ (suc n)) x
          ≡ suspFun ((Hn+1/Hn n) ∘ (suspFun (to_cofiber n C)) ∘ (δ (suc n) C)) x
        aux north = refl
        aux south l = merid (inl tt) l
        aux (merid (inl tt) i) l = merid (inl tt) (i ∧ l)
        aux (merid (inr x) i) l =
          hcomp (λ k → λ { (i = i0) → merid (inl tt) (~ k)
                         ; (i = i1) → merid (inl tt) (l ∨ (~ k))
                         ; (l = i1) → merid (inl tt) (~ k ∨ i) })
                south
        aux (merid (push x j) i) l =
          hcomp (λ k → λ { (i = i0) → merid (((push (f .map (suc n) x)) ∙∙ (cong inr (H .hom (suc n) x))
                                            ∙∙ (sym (push (g .map (suc n) x)))) j) (~ k)
                         ; (i = i1) → merid (inl tt) (l ∨ (~ k))
                         ; (j = i0) → merid (inl tt) ((i ∧ l) ∨ (~ k))
                         ; (l = i1) → merid (((push (f .map (suc n) x)) ∙∙ (cong inr (H .hom (suc n) x))
                                            ∙∙ (sym (push (g .map (suc n) x)))) j) (i ∨ (~ k)) })
                south
