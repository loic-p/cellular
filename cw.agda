{-# OPTIONS --cubical --safe #-}

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
open import Cubical.Data.Int
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetTruncation as ST

open import Cubical.Relation.Nullary
open import Cubical.Homotopy.Loopspace
open import Cubical.ZCohomology.Groups.Sn

open import Cubical.Algebra.AbGroup

open import prelude

module cw where

mutual
  -- description of n-dimensional finite cell complex
  CW : ℕ → Type
  CW zero = ℕ
  CW (suc n) = Σ[ C ∈ CW n ] Σ[ m ∈ ℕ ] (Fin m × (S₊ n) → real n C)

  -- realization of a n-dimensional finite cell complex
  real : (n : ℕ) → CW n → Type
  real zero m = Fin m
  real (suc n) (C , m , bndry) = Pushout bndry fst

-- number of cells of max dimension
cells : (n : ℕ) → CW n → ℕ
cells zero m = m
cells (suc n) (C , m , bndry) = m

-- number of cells of max dimension minus one
prev-cells : (n : ℕ) → CW (suc n) → ℕ
prev-cells zero (m , _ , _) = m
prev-cells (suc n) ((C , m , bndry) , _ , _) = m

-- lower-cells
lower-cell : {n : ℕ} → CW n → (m : ℕ) → m ≤ n → ℕ
lower-cell {n = n} C m (zero , p) = cells n C
lower-cell {n = zero} C m (suc diff , p) = ⊥.rec (snotz p)
lower-cell {n = (suc n)} C m (suc diff , p) =
  lower-cell (fst C) m (diff , cong predℕ p)

-- subcomplexes
subcomplex : (n m : ℕ) → m ≤ n → CW n → CW m
subcomplex n m (zero , p) C = subst CW (sym p) C
subcomplex zero m (suc diff , p) C = ⊥.rec (snotz p)
subcomplex (suc n) m (suc diff , p) C = subcomplex n m (diff , cong predℕ p) (fst C)

-- realisation of subcomplexes
sub-real : {n : ℕ} (m : ℕ) (p : m ≤ n) (C : CW n) → Type
sub-real {n = n} m p C = real m (subcomplex n m p C)

getCell : {n : ℕ} → CW n → (m : ℕ) → ℕ
getCell {n = n} C m with (n Cubical.Data.Nat.Order.≟ m)
... | lt x = 0
... | eq x = cells _ C
... | gt x = lower-cell C m (<-weaken x)

chooseS : (n : ℕ) (a b : ℕ) → S₊ n → S₊ n
chooseS n a b x with (discreteℕ a b)
... | yes p = x
... | no ¬p = ptSn n

∂-aux : (n : ℕ) → (C : CW (suc n)) → real (suc n) C → ℕ → S₊ (suc n)
∂-aux n C (inl _) _ = ptSn (suc n)
∂-aux n C (inr _) _ = ptSn (suc n)
∂-aux n C (push (a , s) i) b = σ n (chooseS n (fst a) b s) i

degree : (n : ℕ) → (S₊ (suc n) → S₊ (suc n)) → ℤ
degree n f = Iso.fun ((Hⁿ-Sⁿ≅ℤ n) .fst) ∣ (λ x → ∣ f x ∣) ∣₂

∂ : (n : ℕ) → (C : CW (suc n)) → Fin (cells (suc n) C) → Fin (prev-cells n C) → ℤ
∂ zero C x y = pos (C .snd .snd (x , true) .fst) - pos (C .snd .snd (x , false) .fst)
∂ (suc n) C x y = degree n λ z → ∂-aux n (fst C) (snd C .snd (x , z)) (y .fst)


--- The above definitions seem to lead to transport hell. Would this work instead?
yieldsCW' : (ℕ → Type) → Type
yieldsCW' X =
  Σ[ f ∈ (ℕ → ℕ) ]
        (Σ[ α ∈ ((n : ℕ) → (Fin (f (suc n)) × (S₊ n)) → X n) ]
         ((X zero ≃ Fin (f 0))
        × ((n : ℕ) → X (suc n) ≃ Pushout (α n) fst)))

CW' : Type₁
CW' = Σ[ X ∈ (ℕ → Type) ] (yieldsCW' X)

CW↪ : (T : CW') → (n : ℕ) → fst T n → fst T (suc n)
CW↪ (X , α , e₀ , e₊) n x = invEq (e₊ .snd n) (inl x)

yieldsFinCW' : (n : ℕ) (X : ℕ → Type) → Type
yieldsFinCW' n X =
  Σ[ CW ∈ yieldsCW' X ] ((k : ℕ) → isEquiv (CW↪ (X , CW) (k +ℕ n)))

finCW : (n : ℕ) → Type₁
finCW n = Σ[ C ∈ (ℕ → Type) ] (yieldsFinCW' n C)

∂-aux** : (n : ℕ) (C : CW')
  → Pushout (fst (C .snd .snd) n) fst
  → ℕ → S₊ (suc n)
∂-aux** n C (inl x) _ = ptSn (suc n)
∂-aux** n C (inr x) _ = ptSn (suc n)
∂-aux** n C (push (a , s) i) m = σ n (chooseS n (a .fst) m s) i

∂-aux* : (n : ℕ) → (C : CW') → C .fst (suc n) → ℕ → S₊ (suc n)
∂-aux* n C x m = ∂-aux** n C (fst (C .snd .snd .snd .snd n) x) m

pre∂ : (n : ℕ) (C : CW') → Fin (C .snd .fst (suc n)) → Fin (C .snd .fst n) → ℤ
pre∂ zero C x y = pos (snd C .snd .snd .fst .fst (C .snd .snd .fst zero (x , true)) .fst)
                - pos (snd C .snd .snd .fst .fst (C .snd .snd .fst zero (x , false)) .fst)
pre∂ (suc n) C x y = degree n λ z → ∂-aux* n C (snd C .snd .fst (suc n) (x , z)) (y .fst)

open import freeabgroup
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function

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

open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup renaming (_/_ to _//_)

open import Cubical.Algebra.Group.Base

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

elimFreeGroup : ∀ {ℓ} {n : ℕ}
  → (P : ℤ[A (suc n) ] .fst → Type ℓ)
  → ((x : _) → P (generator x))
  → ((f : _) → P f → P (λ x → -ℤ (f x)))
  → ((f g : _) → P f → P g → P (λ x → f x + g x))
  → (x : _) → P x
elimFreeGroup {n = zero} P gen d ind f =
  subst P (sym (funExt (generator-is-generator f)))
    {!!}
elimFreeGroup {n = suc n} P gen d ind f =
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
elimFreeGroup {n = suc n} P gen d ind = {!!}


module _ (C : CW') where
  ∂-alt : (n : ℕ) → ℤ[A snd C .fst (suc n) ] .fst → ℤ[A snd C .fst n ] .fst
  ∂-alt n f a = sumFin λ b → f b ·ℤ (pre∂ n C b a)

  ∂² : (n : ℕ) (f : _) (a : _) → ∂-alt n (∂-alt (suc n) f) a ≡ 0
  ∂² n f a =
     cong (sumFin {n = snd C .fst (suc n)})
       (funExt (λ g → cong (_·ℤ pre∂ n C g a) (refl {x = sumFin (λ b → f b ·ℤ (pre∂ (suc n) C b g))}) ∙ refl))
    ∙ {!!}
    ∙ {!!}

  ∂-hom : (n : ℕ) → AbGroupHom ℤ[A snd C .fst (suc n) ] ℤ[A snd C .fst n ]
  fst (∂-hom n) = ∂-alt n
  snd (∂-hom n) =
    makeIsGroupHom λ f g → funExt λ x →
      cong (sumFin {n = snd C .fst (suc n)})
        (funExt (λ y → ·DistL+ (f y) (g y) (pre∂ n C y x)))
    ∙ sumFin-hom (λ b → f b ·ℤ pre∂ n C b x) (λ b → g b ·ℤ pre∂ n C b x)
  

  ∂* : ∀ {ℓ} (n : ℕ) (G : AbGroup ℓ)
    → HomGroup (AbGroup→Group (ℤ[A snd C .fst n ])) G .fst
    → HomGroup (AbGroup→Group (ℤ[A snd C .fst (suc n) ])) G .fst
  ∂* n G f = compGroupHom (∂-hom n) f

  ∂*-hom : ∀ {ℓ} (n : ℕ) (G : AbGroup ℓ)
    → AbGroupHom (HomGroup (AbGroup→Group (ℤ[A snd C .fst n ])) G)
                  (HomGroup (AbGroup→Group (ℤ[A snd C .fst (suc n) ])) G)
  fst (∂*-hom n G) = ∂* n G
  snd (∂*-hom n G) =
    makeIsGroupHom λ f g → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    refl

open import Cubical.Algebra.Group.Subgroup

H^_[_,_]gr : ∀ {ℓ} (n : ℕ) (C : CW') (G : AbGroup ℓ) → Group ℓ
H^ n [ C , G ]gr = {!kerSubgroup (∂*-hom C n G)!} // {!!}

H^_[_,_] : ∀ {ℓ} (n : ℕ) (C : CW') (G : AbGroup ℓ) → AbGroup ℓ
H^ n [ C , G ] = {!!}
