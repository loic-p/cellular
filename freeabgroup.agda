{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Instances.Int

open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Foundations.Function

open import prelude

module freeabgroup where

open IsGroup
open GroupStr
open IsMonoid
open IsSemigroup

module _ {ℓ ℓ' : Level} {X : Type ℓ} (G : X → Group ℓ') where

  ΠGroup : Group (ℓ-max ℓ ℓ')
  fst ΠGroup = (x : X) → fst (G x)
  1g (snd ΠGroup) x = 1g (G x .snd)
  GroupStr._·_ (snd ΠGroup) f g x = GroupStr._·_ (G x .snd) (f x) (g x)
  inv (snd ΠGroup) f x = inv (G x .snd) (f x)
  is-set (isSemigroup (isMonoid (isGroup (snd ΠGroup)))) =
    isSetΠ λ x → is-set (G x .snd) 
  IsSemigroup.·Assoc (isSemigroup (isMonoid (isGroup (snd ΠGroup)))) f g h =
    funExt λ x → IsSemigroup.·Assoc (isSemigroup (isMonoid (G x .snd))) (f x) (g x) (h x)
  ·IdR (isMonoid (isGroup (snd ΠGroup))) f =
    funExt λ x → ·IdR (isMonoid (isGroup (snd (G x)))) (f x)
  ·IdL (isMonoid (isGroup (snd ΠGroup))) f =
    funExt λ x → ·IdL (isMonoid (isGroup (snd (G x)))) (f x)
  ·InvR (isGroup (snd ΠGroup)) f =
    funExt λ x → ·InvR (isGroup (snd (G x))) (f x)
  ·InvL (isGroup (snd ΠGroup)) f =
    funExt λ x → ·InvL (isGroup (snd (G x))) (f x)

module _ {ℓ ℓ' : Level} {X : Type ℓ} (G : X → AbGroup ℓ') where
  ΠAbGroup : AbGroup (ℓ-max ℓ ℓ')
  ΠAbGroup = Group→AbGroup (ΠGroup (λ x → AbGroup→Group (G x)))
              λ f g i x → IsAbGroup.+Comm (AbGroupStr.isAbGroup (G x .snd)) (f x) (g x) i

ℤAbGroup : AbGroup ℓ-zero
ℤAbGroup = Group→AbGroup ℤGroup +Comm

-- Ok yes this is a lie but it happens to be FreeAbGroup for A = Fin n...
FreeAbGroup : ∀ {ℓ} (A : Type ℓ) → AbGroup ℓ
FreeAbGroup A = ΠAbGroup {X = A} λ _ → ℤAbGroup

ℤ[A_] : (n : ℕ) → AbGroup ℓ-zero
ℤ[A n ] = FreeAbGroup (Fin n)

Fin↑ : {n : ℕ} → Fin n → Fin (suc n)
Fin↑ {n = n} p = fst p , <-trans (snd p) (0 , refl)

sumFin : {n : ℕ} (f : Fin n → ℤ) → ℤ
sumFin {n = zero} f = 0
sumFin {n = suc n} f = f flast + sumFin {n = n} λ x → f (Fin↑ x)

sumFin-hom : {n : ℕ} (f g : Fin n → ℤ)
  → sumFin (λ x → f x + g x) ≡ sumFin f + sumFin g
sumFin-hom {n = zero} f g = refl
sumFin-hom {n = suc n} f g =
    cong ((f flast + g flast) +_) (sumFin-hom {n = n} (f ∘ Fin↑) (g ∘ Fin↑))
  ∙ move4 (f flast) (g flast) (sumFin {n = n} (f ∘ Fin↑)) (sumFin {n = n} (g ∘ Fin↑))
          _+_ +Assoc +Comm

generator : {n : ℕ} (k : Fin n) → ℤ[A n ] .fst
generator {n = n} k s with (Cubical.Data.Nat.Order._≟_ (fst k) (fst s))
... | lt x = 0
... | eq x = 1
... | gt x = 0

generator-is-generator : {n : ℕ} (f : ℤ[A n ] .fst) (a : _)
  → f a ≡ sumFin {n = n} λ s → f s ·ℤ (generator s a)
generator-is-generator {n = zero} f a = ⊥.rec (¬Fin0 a)
generator-is-generator {n = suc n} f (a , zero , p) = {!!}
generator-is-generator {n = suc n} f (a , suc diff , p) =
     cong f (Σ≡Prop (λ _ → Cubical.Data.Nat.Order.isProp≤) refl)
  ∙∙ generator-is-generator {n = n} (f ∘ Fin↑) (a , diff , cong predℕ p)
  ∙∙ (λ i → sumFin (λ x → f (Fin↑ x) ·ℤ help x a diff p i))
  ∙∙ +Comm F 0
  ∙∙ λ i → (sym (·Comm (f flast) 0) 
           ∙ (cong (f flast ·ℤ_) (sym (help₂ flast refl)))) i + F
  where
  F = sumFin (λ x → f (Fin↑ x) ·ℤ generator (Fin↑ x) (a , suc diff , p))

  help : (x : _) (a : _) (diff : _) (p : _)
    → generator {n = n} x (a , diff , cong predℕ p)
     ≡ generator {n = suc n} (Fin↑ x) (a , suc diff , p)
  help x a diff p with (Cubical.Data.Nat.Order._≟_ (fst x) a)
  ... | lt _ = refl
  ... | eq _ = refl
  ... | gt _ = refl

  help₂ : (k : Fin (suc n)) → fst k ≡ n → generator {n = suc n} k (a , suc diff , p) ≡ 0
  help₂ k q with (Cubical.Data.Nat.Order._≟_ (fst k) a)
  ... | lt _ = refl
  ... | eq x = ⊥.rec
    (snotz (sym (+∸ (suc diff) a)
           ∙ cong (_∸ a) (sym (+-suc diff a))
           ∙ (cong (_∸ suc a) (p ∙ cong suc (sym q ∙ x)))
           ∙ n∸n a))
  ... | gt _ = refl


elimFreeAbGroup : ∀ {ℓ} {n : ℕ}
  → (P : ℤ[A (suc n) ] .fst → Type ℓ)
  → ((x : _) → P (generator x))
  → ((f : _) → P f → P (λ x → -ℤ (f x)))
  → ((f g : _) → P f → P g → P (λ x → f x + g x))
  → (x : _) → P x
elimFreeAbGroup {n = zero} P gen d ind f =
  subst P (sym (funExt (generator-is-generator f)))
    {!!}
elimFreeAbGroup {n = suc n} P gen d ind f =
  subst P (sym (funExt (generator-is-generator f)))
    (ind (λ x → f flast ·ℤ generator flast x) (λ x → (f (Fin↑ flast) ·ℤ generator (Fin↑ flast) x +
          sumFin
          (λ x₁ → f (Fin↑ (Fin↑ x₁)) ·ℤ generator (Fin↑ (Fin↑ x₁)) x)))
            {!!}
            {!!})
    where
    ct : {!!}
    ct = {!!}

    c : (y : ℤ) → P (λ x → y ·ℤ generator flast x)
    c (pos zero) = {!!}
    c (pos (suc n)) =
      ind (generator flast) (λ x → pos n ·ℤ generator flast x) (gen flast) (c (pos n)) 
    c (negsuc n) = {!!}
