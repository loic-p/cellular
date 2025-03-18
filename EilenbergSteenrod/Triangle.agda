{-# OPTIONS --cubical #-}
module EilenbergSteenrod.Triangle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.CW.Map

open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive
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

open import EilenbergSteenrod.StrictifyCW renaming (strictCWskel to str)
open import EilenbergSteenrod.CWPushout
open import Cubical.Foundations.Pointed

open SequenceMap renaming (map to seqMap)

module Bob (ℓ : Level) (Bʷ Cʷ Dʷ : CWskel ℓ) where



QuotCW : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Type ℓ 
QuotCW C n = cofib (CW↪ C n)

QuotCW∙ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Pointed ℓ 
QuotCW∙ C n = QuotCW C n , inl tt

data 3⋁ {ℓ ℓ' ℓ''} (A : Pointed ℓ) (B : Pointed ℓ') (C : Pointed ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  inl : fst A → 3⋁ A B C 
  inm : fst B → 3⋁ A B C
  inr : fst C → 3⋁ A B C

  pushₗ : inl (pt A) ≡ inm (pt B)
  pushᵣ : inr (pt C) ≡ inm (pt B)

module _ (ℓ : Level) (Bʷ Cʷ Dʷ : CWskel ℓ)
  (fʷ : cellMap (str Bʷ) (str Cʷ))
  (gʷ : cellMap (str Bʷ) (str Dʷ)) where
  open Pushoutz ℓ Bʷ Cʷ Dʷ fʷ gʷ

  Bob : (n : ℕ) → Type ℓ
  Bob n = 3⋁ (QuotCW∙ C (suc n)) (Susp∙ (QuotCW B n)) (QuotCW∙ D (suc n))

  pushoutA→Bob : (n : ℕ) → pushoutA (suc (suc n)) → Bob n
  pushoutA→Bob n (inl x) = inl (inr x)
  pushoutA→Bob n (inr x) = inr (inr x)
  pushoutA→Bob n (push a i) =
    ((λ i → inl (push (seqMap f (suc n) a) (~ i)))
      ∙∙ (pushₗ ∙∙ (λ i → inm (toSusp (QuotCW∙ B n) (inr a) i)) ∙∙ sym pushᵣ)
    ∙∙ λ i → inr (push (seqMap g (suc n) a) i)) i

  open CWskel-fields
  open import Cubical.HITs.Wedge.Properties

  Strict→BobCell : (n : ℕ) (a : (Fin (card C (suc n)) ⊎ Fin (card B n)) ⊎ Fin (card D (suc n)))
              → Bob n
  Strict→BobCell n (inl (inl x)) = inl (inr (inr x))
  Strict→BobCell n (inl (inr x)) = inr {!!}
  Strict→BobCell n (inr x) = inm {!seqMap f (suc n) !}

  Strict→BobΩinm : (n : ℕ) (w : Fin (card B (suc n))) (s : S₊ (suc n))
    → Path (Susp (QuotCW B (suc n))) north north
  Strict→BobΩinm zero w base i = north
  Strict→BobΩinm zero w (loop i₁) i = {!!}
  Strict→BobΩinm (suc n) w north i = north
  Strict→BobΩinm (suc n) w south i = north
  Strict→BobΩinm (suc n) w (merid a i) j =
    hcomp {!!}
          (toSusp (QuotCW∙ B (suc (suc n)))
                   ((push (α B (suc (suc n)) (w , a))
                    ∙∙ (λ i → inr (push (w , a) i))
                    ∙∙ {!!}) i) j)


  makeLoop : ∀ {ℓ} (D : CWskel ℓ) (n : ℕ) (s : S₊ n) (s : Fin (card (str D) (suc n)))
    → Path (QuotCW (str D) (suc n)) (inl tt) (inl tt)
  makeLoop D n s w = ((push (α (str D) (suc n) (w , s)) ∙ λ i → inr (push (w , s) i))
                    ∙ sym ((push (α (str D) (suc n) (w , ptSn n)) ∙ λ i → inr (push (w , ptSn n) i))))

  Strict→BobΩ : (n : ℕ) (a : (Fin (card C (suc n)) ⊎ Fin (card B n)) ⊎ Fin (card D (suc n)))
              → S₊ n → Path (Bob n) (inm north) (inm north)
  Strict→BobΩ n (inl (inl s)) x = sym pushₗ
            ∙∙ (λ i → inl (makeLoop Cʷ n x s i))
            ∙∙ pushₗ
  Strict→BobΩ zero (inl (inr s)) x = {!!}
  Strict→BobΩ (suc n) (inl (inr s)) x = cong inm (Strict→BobΩinm n s x)
  -- (λ i → inm (toSusp (QuotCW∙ B n) (inr (α B (suc n) ({!s!} , x))) i)) 
  Strict→BobΩ n (inr s) x =
    sym pushᵣ
    ∙∙ (λ i → inr {!makeLoop Bʷ n s i i!})
    ∙∙ pushᵣ
  -- {!!} ∙∙ (λ i → inm (toSusp (QuotCW∙ B n) (inr (α B (suc n) ({!x₁!} , x))) i)) ∙∙ {!!}

  Strict→Bob : (n : ℕ) → Pushout (pushoutMap (suc n)) fst → Bob n
  Strict→Bob n (inl x) = inm north
  Strict→Bob n (inr x) = inm north
  Strict→Bob n (push (a , b) i) =
    Strict→BobΩ n (Iso.fun (IsoFinSplit3 (card C (suc n)) (card B n) (card D (suc n))) a) b i
