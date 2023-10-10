{-# OPTIONS --cubical --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.Relation.Nullary
open import Cubical.Homotopy.Loopspace
open import Cubical.Foundations.Pointed

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.HITs.FreeAbGroup.Base

σ : (n : ℕ) → S₊ n → typ (Ω (S₊∙ (suc n)))
σ zero false = loop
σ zero true = refl
σ (suc n) x = toSusp (S₊∙ (suc n)) x

σ∙ : (n : ℕ) → S₊∙ n →∙ (Ω (S₊∙ (suc n)))
fst (σ∙ n) = σ n
snd (σ∙ zero) = refl
snd (σ∙ (suc n)) = rCancel (merid (ptSn (suc n)))

module _ {ℓ : Level} (A : Type ℓ) where
  ℤ[_] : AbGroup ℓ
  ℤ[_] = FAGAbGroup {A = A}
