{-# OPTIONS --cubical #-}
module Hurewicz.Connected where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat.Order.Inductive

open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.Connected
open import Cubical.CW.Homology



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

open import Cubical.Data.Unit

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Wedge


open import Cubical.Homotopy.Group.Base
-- open import Cubical.Homotopy.Group.Properties

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Algebra.AbGroup

-- yieldsConnectedCWskel : (A : ℕ → Type ℓ) (n : ℕ) → Type _
-- yieldsConnectedCWskel A k =
--   Σ[ sk ∈ yieldsCWskel A ] ((sk .fst 0 ≡ 1) × ((n : ℕ) → n <ᵗ k → sk .fst (suc n) ≡ 0))

yieldsConnectedCWskelBottomSkel : ∀ {ℓ} (A : ℕ → Type ℓ) (n : ℕ)
  → (sk : yieldsConnectedCWskel A n)
  → A (suc (suc n)) ≃ SphereBouquet (suc n) (Fin (sk .fst .fst (suc n)))
yieldsConnectedCWskelBottomSkel A n sk =
  compEquiv (sk .fst .snd .snd .snd (suc n))
             (compEquiv (isoToEquiv (⋁-cofib-Iso ((A (suc n)) ,  cont .fst) α'))
             (compEquiv
               (compEquiv
                 (pushoutEquiv _ _ _ _
                   (idEquiv _) (idEquiv _)
                   (isContr→≃Unit cont)
                   refl
                   refl)
                 PushoutSusp≃Susp)
               (isoToEquiv sphereBouquetSuspIso)))
  where
  cont : isContr (A (suc n))
  cont = isConnectedCW→Contr n (A , sk) (n , <ᵗsucm {m = n})

  α' : SphereBouquet∙ n (Fin (fst (sk .fst) (suc n))) →∙ (A (suc n) , cont .fst)
  fst α' (inl x) = cont .fst
  fst α' (inr x) = fst (sk .fst .snd) (suc n) x
  fst α' (push a i) =
    isContr→isProp cont
      (isConnectedCW→Contr n (A , sk) (n , <ᵗsucm {n}) .fst)
      (fst (sk .fst .snd) (suc n) (a , snd (S₊∙ n))) i
  snd α' = refl




  -- → ∃[ F1 ∈ ℕ ] Σ[ F2 ∈ ℕ ] (α : SphereBouquet∙ (suc n) (Fin F1) →∙ SphereBouquet (suc n) (Fin F1))
  --     ((A (suc n) ≃ SphereBouquet (suc n) (Fin F1))
  --    × (A (suc (suc n)) ≃ {!!}))
