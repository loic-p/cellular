{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.AbPath where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed


open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.Connected
open import Cubical.CW.Homology
open import Cubical.CW.Subcomplex


open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
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
open import Cubical.HITs.SetTruncation as ST


open import Cubical.Homotopy.Group.Base
open import Cubical.Algebra.Group.Properties

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Foundations.HLevels

open import Cubical.Algebra.AbGroup

open import Cubical.CW.Approximation

open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.CW.ChainComplex
open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties as SQ
open import Cubical.Data.Int
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Abelianization.Properties as Abi

open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Unit
open import Cubical.HITs.Wedge


open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup as FAB 

open import Hurewicz.random


open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Pushout as PO

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Semigroup.Base


·GroupAutomorphism : ∀ {ℓ} (G : Group ℓ) (g : fst G) → Iso (fst G) (fst G)
Iso.fun (·GroupAutomorphism G g) = GroupStr._·_ (snd G) g
Iso.inv (·GroupAutomorphism G g) = GroupStr._·_ (snd G) (GroupStr.inv (snd G) g)
Iso.rightInv (·GroupAutomorphism G g) h =
  GroupStr.·Assoc (snd G) _ _ _
  ∙ cong₂ (GroupStr._·_ (snd G)) (GroupStr.·InvR (snd G) g) refl
  ∙ GroupStr.·IdL (snd G) h
Iso.leftInv (·GroupAutomorphism G g) h =
  GroupStr.·Assoc (snd G) _ _ _
  ∙ cong₂ (GroupStr._·_ (snd G)) (GroupStr.·InvL (snd G) g) refl
  ∙ GroupStr.·IdL (snd G) h

·GroupAutomorphismR : ∀ {ℓ} (G : Group ℓ) (g : fst G) → Iso (fst G) (fst G)
Iso.fun (·GroupAutomorphismR G g) x = GroupStr._·_ (snd G) x g
Iso.inv (·GroupAutomorphismR G g) x = GroupStr._·_ (snd G) x (GroupStr.inv (snd G) g)
Iso.rightInv (·GroupAutomorphismR G g) h =
  sym (GroupStr.·Assoc (snd G) _ _ _)
  ∙ cong₂ (GroupStr._·_ (snd G)) refl (GroupStr.·InvL (snd G) g) -- 
  ∙ GroupStr.·IdR (snd G) h
Iso.leftInv (·GroupAutomorphismR G g) h =
    sym (GroupStr.·Assoc (snd G) _ _ _)
  ∙ cong₂ (GroupStr._·_ (snd G)) refl (GroupStr.·InvR (snd G) g) -- 
  ∙ GroupStr.·IdR (snd G) h

open import Cubical.Algebra.Group.Subgroup
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.S1
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.HITs.FreeAbGroup.Base

open import Cubical.Algebra.Group.Free
open import Cubical.Data.List renaming ([_] to [_]L)



open import Cubical.HITs.Bouquet as Bouq
open import Cubical.HITs.Bouquet.Discrete



open import Cubical.HITs.FreeGroup as FG
open import Cubical.HITs.FreeGroup.NormalForm
open import Cubical.HITs.FreeGroupoid.Properties
open import Cubical.Algebra.Group.Free

data _≡ᵃᵇ_ {ℓ} {A : Type ℓ} (x y : A) : Type ℓ
  where
  paths : x ≡ y → x ≡ᵃᵇ y
  com : (p q r : x ≡ y) → paths (p ∙ sym q ∙ r) ≡ paths (r ∙ sym q ∙ p)

Ωᵃᵇ : ∀ {ℓ} (A : Pointed ℓ) → Type ℓ
Ωᵃᵇ (A , a) = a ≡ᵃᵇ a

Pathᵃᵇ : ∀ {ℓ} (A : Type ℓ) (x y : A) → Type ℓ
Pathᵃᵇ A = _≡ᵃᵇ_

elimProp≡ᵃᵇ : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} {B : x ≡ᵃᵇ y → Type ℓ'}
  → ((s : _) → isProp (B s))
  → ((p : x ≡ y) → B (paths p))
  → (x : _) → B x
elimProp≡ᵃᵇ pr path* (paths x) = path* x
elimProp≡ᵃᵇ {B = B} pr path* (com p q r i) = help i
  where
  help : PathP (λ i → B (com p q r i)) (path* (p ∙ sym q ∙ r)) (path* (r ∙ sym q ∙ p))
  help = isProp→PathP (λ _ → pr _) _ _


congPathsLemmaL : ∀ {ℓ} {A : Type ℓ} {x y : A} (z : _) (p : x ≡ z)  (q : x ≡ y)(r : x ≡ y) (s : x ≡ y)
  → Path (z ≡ᵃᵇ y) (paths (sym p ∙ q ∙ sym r ∙ s)) (paths (sym p ∙ s ∙ sym r ∙ q))
congPathsLemmaL = J> λ q r s → cong paths (sym (lUnit _)) ∙ com q r s ∙ cong paths (lUnit _)

congPathsLemmaR : ∀ {ℓ} {A : Type ℓ} {x y : A} (z : _) (p : y ≡ z)  (q : x ≡ y)(r : x ≡ y) (s : x ≡ y)
  → Path (x ≡ᵃᵇ z) (paths ((q ∙ sym r ∙ s) ∙ p)) (paths ((s ∙ sym r ∙ q) ∙ p))
congPathsLemmaR = J> λ q r s → cong paths (sym (rUnit _)) ∙ com q r s ∙ cong paths (rUnit _)

act≡ᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ x) → x ≡ᵃᵇ y → x ≡ᵃᵇ y
act≡ᵃᵇ p (paths x₁) = paths (p ∙ x₁)
act≡ᵃᵇ {y = y} p (com q r s i) = congPathsLemmaL _ (sym p) q r s i

actL·πᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) → y ≡ᵃᵇ z → x ≡ᵃᵇ z
actL·πᵃᵇ p (paths q) = paths (p ∙ q)
actL·πᵃᵇ p (com q r s i) = congPathsLemmaL _ (sym p) q r s i

·πᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → ∥ x ≡ᵃᵇ y ∥₂ → ∥ y ≡ᵃᵇ z ∥₂ → ∥ x ≡ᵃᵇ z ∥₂
·πᵃᵇ {x = x} {y} {z} = ST.rec2 squash₂ preMult
  where
  preMult : x ≡ᵃᵇ y → y ≡ᵃᵇ z → ∥ x ≡ᵃᵇ z ∥₂
  preMult (paths p) q = ∣ actL·πᵃᵇ p q ∣₂
  preMult (com p q r i) s = lem s i
    where
    lem : (s : y ≡ᵃᵇ z) → ∣ actL·πᵃᵇ (p ∙ sym q ∙ r) s ∣₂ ≡ ∣ actL·πᵃᵇ (r ∙ sym q ∙ p) s ∣₂
    lem = elimProp≡ᵃᵇ (λ _ → squash₂ _ _) λ s i → ∣ congPathsLemmaR _ s p q r i ∣₂

symᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ᵃᵇ y → y ≡ᵃᵇ x
symᵃᵇ (paths x) = paths (sym x)
symᵃᵇ {A = A} {x} {y} (com p q r i) = lem i
  where
  lem : Path (y ≡ᵃᵇ x) (paths (sym (p ∙ sym q ∙ r))) (paths (sym (r ∙ sym q ∙ p)))
  lem = cong paths (symDistr _ _ ∙ cong₂ _∙_ (symDistr _ _) refl
                  ∙ sym (GLaws.assoc _ _ _))
     ∙∙ com _ _ _
     ∙∙ sym (cong paths (symDistr _ _ ∙ cong₂ _∙_ (symDistr _ _) refl
                  ∙ sym (GLaws.assoc _ _ _)))

-πᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x y : A} → ∥ x ≡ᵃᵇ y ∥₂ → ∥ y ≡ᵃᵇ x ∥₂
-πᵃᵇ = ST.map symᵃᵇ

reflᵃᵇ : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ᵃᵇ x
reflᵃᵇ = paths refl

-- Groupoid laws

·πᵃᵇrUnit : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ᵃᵇ y ∥₂) → ·πᵃᵇ p ∣ reflᵃᵇ ∣₂ ≡ p
·πᵃᵇrUnit = ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
  λ p → cong ∣_∣₂ (cong paths (sym (rUnit _))))

·πᵃᵇlUnit : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ᵃᵇ y ∥₂) → ·πᵃᵇ ∣ reflᵃᵇ ∣₂ p ≡ p
·πᵃᵇlUnit = ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
  λ p → cong ∣_∣₂ (cong paths (sym (lUnit _))))

·πᵃᵇrCancel : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ᵃᵇ y ∥₂) → ·πᵃᵇ p (-πᵃᵇ p) ≡ ∣ reflᵃᵇ ∣₂
·πᵃᵇrCancel = ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
  λ p → cong ∣_∣₂ (cong paths (rCancel _)))

·πᵃᵇlCancel : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : ∥ x ≡ᵃᵇ y ∥₂) → ·πᵃᵇ (-πᵃᵇ p) p ≡ ∣ reflᵃᵇ ∣₂
·πᵃᵇlCancel = ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
  λ p → cong ∣_∣₂ (cong paths (lCancel _)))

·πᵃᵇassoc : ∀ {ℓ} {A : Type ℓ} {x : A} (p q r : ∥ x ≡ᵃᵇ x ∥₂) → ·πᵃᵇ p (·πᵃᵇ q r)  ≡ ·πᵃᵇ (·πᵃᵇ p q) r
·πᵃᵇassoc = ST.elim3 (λ _ _ _ → isSetPathImplicit)
  (elimProp≡ᵃᵇ (λ _ → isPropΠ2 λ _ _ → squash₂ _ _)
   λ p → elimProp≡ᵃᵇ (λ _ → isPropΠ λ _ → squash₂ _ _)
     λ q → elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
       λ r → cong ∣_∣₂ (cong paths (GLaws.assoc p q r)))

·πᵃᵇcomm : ∀ {ℓ} {A : Type ℓ} {x : A} (p q : ∥ x ≡ᵃᵇ x ∥₂) → ·πᵃᵇ p q ≡ ·πᵃᵇ q p
·πᵃᵇcomm = ST.elim2 (λ _ _ → isSetPathImplicit)
  (elimProp≡ᵃᵇ (λ _ → isPropΠ (λ _ → squash₂ _ _))
    λ p → elimProp≡ᵃᵇ (λ _ → squash₂ _ _) λ q
      → cong ∣_∣₂ (cong paths (cong₂ _∙_ refl (lUnit q))
                 ∙ com p refl q
                 ∙ cong paths (cong₂ _∙_ refl (sym (lUnit p)))))

open IsAbGroup
open IsGroup
open IsMonoid

open IsSemigroup
π₁ᵃᵇAbGroup : ∀ {ℓ} (A : Pointed ℓ) → AbGroup ℓ
fst (π₁ᵃᵇAbGroup (A , a)) = ∥ a ≡ᵃᵇ a ∥₂
AbGroupStr.0g (snd (π₁ᵃᵇAbGroup A)) = ∣ reflᵃᵇ ∣₂
AbGroupStr._+_ (snd (π₁ᵃᵇAbGroup A)) = ·πᵃᵇ
AbGroupStr.- snd (π₁ᵃᵇAbGroup A) = -πᵃᵇ
is-set (isSemigroup (isMonoid (isGroup (AbGroupStr.isAbGroup (snd (π₁ᵃᵇAbGroup A)))))) = squash₂
IsSemigroup.·Assoc (isSemigroup (isMonoid (isGroup (AbGroupStr.isAbGroup (snd (π₁ᵃᵇAbGroup A)))))) = ·πᵃᵇassoc
IsMonoid.·IdR (isMonoid (isGroup (AbGroupStr.isAbGroup (snd (π₁ᵃᵇAbGroup A))))) = ·πᵃᵇrUnit
IsMonoid.·IdL (isMonoid (isGroup (AbGroupStr.isAbGroup (snd (π₁ᵃᵇAbGroup A))))) = ·πᵃᵇlUnit
·InvR (isGroup (AbGroupStr.isAbGroup (snd (π₁ᵃᵇAbGroup A)))) = ·πᵃᵇrCancel
·InvL (isGroup (AbGroupStr.isAbGroup (snd (π₁ᵃᵇAbGroup A)))) = ·πᵃᵇlCancel
IsAbGroup.+Comm (AbGroupStr.isAbGroup (snd (π₁ᵃᵇAbGroup A))) = ·πᵃᵇcomm

module _ {ℓ} {G : Group ℓ} (H : AbGroup ℓ) (ϕ : GroupHom G (AbGroup→Group H)) where
  fromAbelianization : AbGroupHom (AbelianizationAbGroup G) H
  fst fromAbelianization = Abi.rec G (AbGroupStr.is-set (snd H)) (fst ϕ)
    λ x y z → IsGroupHom.pres· (snd ϕ) _ _
            ∙ cong₂ (AbGroupStr._+_ (snd H)) refl
                (IsGroupHom.pres· (snd ϕ) _ _
                ∙ AbGroupStr.+Comm (snd H) _ _
                ∙ sym (IsGroupHom.pres· (snd ϕ) _ _))
            ∙ sym (IsGroupHom.pres· (snd ϕ) _ _)
  snd fromAbelianization =
    makeIsGroupHom (Abi.elimProp2 _
      (λ _ _ → AbGroupStr.is-set (snd H) _ _)
      λ x y → IsGroupHom.pres· (snd ϕ) x y)


Ωᵃᵇ→Abelianizeπ₁ : ∀ {ℓ} {A : Pointed ℓ} →  Ωᵃᵇ A → Abelianization (πGr 0 A)
Ωᵃᵇ→Abelianizeπ₁ (paths x) = η ∣ x ∣₂
Ωᵃᵇ→Abelianizeπ₁ {A = A} (com p q r i) = help i
  where
  open AbelianizationGroupStructure (πGr 0 A)
  help : Path (Abelianization (πGr 0 A))
              (η (·π 0 ∣ p ∣₂ (·π 0 ∣ sym q ∣₂ ∣ r ∣₂)))
              (η (·π 0 ∣ r ∣₂ (·π 0 ∣ sym q ∣₂ ∣ p ∣₂)))
  help = commAb (η ∣ p ∣₂) (η (·π 0 ∣ sym q ∣₂ ∣ r ∣₂))
       ∙ cong₂ _·Ab_ (commAb (η ∣ sym q ∣₂) (η ∣ r ∣₂)) refl
       ∙ sym (assocAb (η ∣ r ∣₂) (η ∣ sym q ∣₂) (η ∣ p ∣₂))

π₁ᵃᵇ→Abelianizeπ₁ : ∀ {ℓ} {A : Pointed ℓ} → ∥ Ωᵃᵇ A ∥₂ → Abelianization (πGr 0 A)
π₁ᵃᵇ→Abelianizeπ₁ = ST.rec isset Ωᵃᵇ→Abelianizeπ₁

π₁→π₁ᵃᵇHom : ∀ {ℓ} {A : Pointed ℓ} → GroupHom (πGr 0 A) (AbGroup→Group (π₁ᵃᵇAbGroup A))
fst π₁→π₁ᵃᵇHom = ST.map paths
snd π₁→π₁ᵃᵇHom =
  makeIsGroupHom (ST.elim2 (λ _ _ → isSetPathImplicit) λ p q → refl)

Abelianizeπ₁→π₁ᵃᵇ : ∀ {ℓ} {A : Pointed ℓ} → AbGroupHom (AbelianizationAbGroup (πGr 0 A)) (π₁ᵃᵇAbGroup A)
Abelianizeπ₁→π₁ᵃᵇ = fromAbelianization (π₁ᵃᵇAbGroup _) π₁→π₁ᵃᵇHom

Abelianizeπ₁≅π₁ᵃᵇ : ∀ {ℓ} (A : Pointed ℓ) → AbGroupIso (AbelianizationAbGroup (πGr 0 A)) (π₁ᵃᵇAbGroup A)
Iso.fun (fst (Abelianizeπ₁≅π₁ᵃᵇ A)) = fst Abelianizeπ₁→π₁ᵃᵇ
Iso.inv (fst (Abelianizeπ₁≅π₁ᵃᵇ A)) = π₁ᵃᵇ→Abelianizeπ₁
Iso.rightInv (fst (Abelianizeπ₁≅π₁ᵃᵇ A)) =
  ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _) λ p → refl)
Iso.leftInv (fst (Abelianizeπ₁≅π₁ᵃᵇ A)) = Abi.elimProp _ (λ _ → isset _ _)
  (ST.elim (λ _ → isOfHLevelPath 2 isset _ _) λ p → refl)
snd (Abelianizeπ₁≅π₁ᵃᵇ A) = snd Abelianizeπ₁→π₁ᵃᵇ


-πᵃᵇinvDistr : ∀ {ℓ} {A : Pointed ℓ} (p q : ∥ Ωᵃᵇ A ∥₂) → -πᵃᵇ {x = pt A} (·πᵃᵇ p q) ≡ ·πᵃᵇ (-πᵃᵇ p) (-πᵃᵇ q)
-πᵃᵇinvDistr {A = A} p q =
  GroupTheory.invDistr (AbGroup→Group (π₁ᵃᵇAbGroup A)) p q
  ∙ ·πᵃᵇcomm _ _

·πᵃᵇinvInv : ∀ {ℓ} {A : Pointed ℓ} (p : ∥ Ωᵃᵇ A ∥₂) → -πᵃᵇ (-πᵃᵇ p) ≡ p
·πᵃᵇinvInv = GroupTheory.invInv (AbGroup→Group (π₁ᵃᵇAbGroup _))
