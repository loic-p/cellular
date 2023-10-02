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


open import freeabgroup

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



open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Foundations.Function
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup renaming (_/_ to _//_)

open import Cubical.Algebra.Group.Base

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
