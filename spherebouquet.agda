{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetTruncation as ST

open import Cubical.Relation.Nullary
open import Cubical.Homotopy.Loopspace
open import Cubical.ZCohomology.Groups.Sn


open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.QuotientGroup renaming (_/_ to _//_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.AbGroup

open import prelude
open import freeabgroup

module spherebouquet where

--terminal map from any type to Unit
terminal : (A : Type) → A → Unit
terminal A x = tt

--a sphere bouquet is the wedge sum of A n-dimensional spheres
SphereBouquet : (n : ℕ) (A : Type) → Pointed₀
SphereBouquet n A = Pushout (terminal A) ((λ a → (a , ptSn n))) , inl tt

--the suspension of a n-dimensional bouquet is a (n+1)-dimensional bouquet
--here is the action of suspension on morphisms
bouquetSusp→ : {n : ℕ} {A B : Type} → (SphereBouquet n A →∙ SphereBouquet n B)
                                    → (SphereBouquet (suc n) A →∙ SphereBouquet (suc n) B)
bouquetSusp→ {n} {A} {B} f = {!!} , {!!}

--a morphisms between bouquets gives a morphisms of free abelian groups by taking degrees
bouquetDegree : {n : ℕ} {A B : Type} → (SphereBouquet n A →∙ SphereBouquet n B)
                                     → (AbGroupHom ℤ[ A ] ℤ[ B ])
bouquetDegree f = {!!}

--degree is compatible with composition
degreeComp : {n : ℕ} {A B C : Type} → (f : SphereBouquet n B →∙ SphereBouquet n C)
                                    → (g : SphereBouquet n A →∙ SphereBouquet n B)
                                    → bouquetDegree (f ∘∙ g) ≡ compGroupHom (bouquetDegree g) (bouquetDegree f)
degreeComp f g = {!!}

--the degree of a suspension is the same as the original degree
--in fact, ℤ[ A ] is basically the infinite suspension of a bouquet
degreeSusp : {n : ℕ} {A B : Type} → (f : SphereBouquet n A →∙ SphereBouquet n B)
                                  → bouquetDegree f ≡ bouquetDegree (bouquetSusp→ f)
degreeSusp f = {!!}
