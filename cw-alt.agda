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
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT

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

module cw-alt where

-- defn of the degree map
chooseS : (n : ℕ) (a b : ℕ) → S₊ n → S₊ n
chooseS n a b x with (discreteℕ a b)
... | yes p = x
... | no ¬p = ptSn n

degree : (n : ℕ) → (S₊ (suc n) → S₊ (suc n)) → ℤ
degree n f = Iso.fun ((Hⁿ-Sⁿ≅ℤ n) .fst) ∣ (λ x → ∣ f x ∣) ∣₂

open import Cubical.HITs.S1
open import Cubical.Foundations.Function

open import Cubical.HITs.Susp
open import Cubical.Homotopy.Connected
open import Cubical.Foundations.HLevels


AC-Fin : ∀ {ℓ} {n : ℕ} {A : Fin n → Type ℓ} (m : ℕ)
  → ((x : Fin n) → hLevelTrunc m (A x))
  → hLevelTrunc m ((x : Fin n) → A x)
AC-Fin = {!!}

data bigWedge {ℓ} (n : ℕ) (A : Fin n → Pointed ℓ) : Type ℓ where
  incl : (m : Fin n) → A m .fst → bigWedge n A
  ⋆wedge : bigWedge n A
  glu : (m : Fin n) → incl m (pt (A m)) ≡ ⋆wedge

bigWedge≡ : ∀ {ℓ ℓ'} (n : ℕ) {A : Fin n → Pointed ℓ} {C : Type ℓ'}
  → (isConnected 3 C)
  → (f g : bigWedge n A → C)
  → ((x : _) (y : _) → f (incl x y) ≡ g (incl x y))
  → ∥ ((x : _) → f x ≡ g x) ∥₁
bigWedge≡ zero co f g ind = TR.rec (isOfHLevelSuc 1 squash₁) (λ p → ∣ (λ { (incl m x) → ⊥.rec (¬Fin0 m) ; ⋆wedge → p ; (glu m i) j → ⊥.rec {A = Square (λ i → f (glu m i)) (cong g (glu m)) (⊥.rec (¬Fin0 m)) p} (⊥.rec (¬Fin0 m)) j i}) ∣₁) (Iso.fun (PathIdTruncIso 2) (isContr→isProp co ∣ f ⋆wedge ∣ₕ ∣ g ⋆wedge ∣ₕ))
bigWedge≡ (suc n) co f g ind =
  TR.rec (isOfHLevelSuc 1 squash₁)
    (λ p → {!!})
    (Iso.fun (PathIdTruncIso 2) (isContr→isProp co ∣ f ⋆wedge ∣ₕ ∣ g ⋆wedge ∣ₕ))

-- bigWedge∙ : ∀ {ℓ} (n : ℕ) (A : Fin n → Pointed ℓ) → Pointed ℓ
-- bigWedge∙ n A = bigWedge n A , ⋆wedge

-- wedge-deg : ∀ (n m : ℕ) → (bigWedge n (λ _ → S₊∙ (suc m)) → S₊ (suc m)) → ℤ
-- wedge-deg n m f = sumFin λ x → degree m λ y → f (incl x y)

-- induce-big-wedge : (n m : ℕ) (f : Fin n → (S₊∙ (suc m) →∙ S₊∙ (suc m))) → bigWedge n (λ _ → S₊∙ (suc m)) → S₊ (suc m)
-- induce-big-wedge n m f (incl m₁ x) = f m₁ .fst x
-- induce-big-wedge n m f ⋆wedge = ptSn (suc m)
-- induce-big-wedge n m f (glu m₁ i) = f m₁ .snd i

-- induce-big-wedge' : (n m : ℕ) (f : Fin n → (S₊∙ (suc m) →∙ S₊∙ (suc m))) → sumFin (λ x → degree m (f x .fst)) ≡ wedge-deg n m (induce-big-wedge n m f)
-- induce-big-wedge' n m f = refl

-- degree-mult : (n : ℕ) (f g : S₊ (suc n) → S₊ (suc n)) → degree n f ·ℤ degree n g ≡ degree n (f ∘ g)
-- degree-mult = {!!}

-- degree-susp : (n : ℕ) (f : S₊ (suc n) → S₊ (suc n)) → degree n f ≡ degree (suc n) (suspFun f)  
-- degree-susp = {!!}


-- degree⋁ : {!!}
-- degree⋁ = {!!}

-- --- CW complexes ---

-- -- Definition of (the skeleton) of an arbitrary CW complex
-- yieldsCW : (ℕ → Type) → Type
-- yieldsCW X =
--   Σ[ f ∈ (ℕ → ℕ) ]
--         (Σ[ α ∈ ((n : ℕ) → (Fin (f (suc n)) × (S₊ n)) → X n) ]
--          ((X zero ≃ Fin (f 0))
--         × ((n : ℕ) → X (suc n) ≃ Pushout (α n) fst)))

-- CW : Type₁
-- CW = Σ[ X ∈ (ℕ → Type) ] (yieldsCW X)

-- -- Technically, a CW complex should be the sequential colimit over the following maps
-- CW↪ : (T : CW) → (n : ℕ) → fst T n → fst T (suc n)
-- CW↪ (X , α , e₀ , e₊) n x = invEq (e₊ .snd n) (inl x)

-- -- But if it stabilises, no need for colimits.
-- yieldsFinCW : (n : ℕ) (X : ℕ → Type) → Type
-- yieldsFinCW n X =
--   Σ[ CW ∈ yieldsCW X ] ((k : ℕ) → isEquiv (CW↪ (X , CW) (k +ℕ n)))

-- -- ... which should give us finite CW complexes.
-- finCW : (n : ℕ) → Type₁
-- finCW n = Σ[ C ∈ (ℕ → Type) ] (yieldsFinCW n C)


-- -- This def makes ∂ easy to define.
-- ∂-aux-gen : (n : ℕ) (C : CW) → ℕ
--   → Pushout (fst (C .snd .snd) n) fst
--   → S₊ (suc n)
-- ∂-aux-gen n C m (inl x) = ptSn (suc n)
-- ∂-aux-gen n C m (inr x) = ptSn (suc n)
-- ∂-aux-gen n C m (push (a , s) i) = σ n (chooseS n (a .fst) m s) i





-- X→Susp : (n : ℕ) (C : CW)
--   → Pushout (fst (C .snd .snd) n) fst
--   → Susp (Fin (fst (C .snd) (suc n)) × S₊ n)
-- X→Susp n C (inl x) = north
-- X→Susp n C (inr x) = south
-- X→Susp n C (push a i) = merid a i

-- ∂-aux-gen-Susp : (n : ℕ) (C : CW) (m : ℕ) → Susp (Fin (fst (C .snd) (suc n)) × S₊ n) → S₊ (suc n)
-- ∂-aux-gen-Susp zero C m north = base
-- ∂-aux-gen-Susp zero C m south = base
-- ∂-aux-gen-Susp zero C m (merid (a , s) i) = σ zero (chooseS zero (a .fst) m s) i
-- ∂-aux-gen-Susp (suc n) C m = suspFun λ as → chooseS (suc n) (as .fst .fst) m (as .snd)

-- ∂-aux-gen≡ : (n : ℕ) (C : CW) (m : ℕ) → ∂-aux-gen n C m ≡ ∂-aux-gen-Susp n C m ∘ X→Susp n C
-- ∂-aux-gen≡ zero C m = funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl}
-- ∂-aux-gen≡ (suc n) C m =
--   funExt λ { (inl x) → refl
--            ; (inr x) → merid (ptSn (suc n))
--            ; (push a i) j → compPath-filler
--              (merid (chooseS (suc n) (a .fst .fst) m (a .snd))) (sym (merid (ptSn (suc n)))) (~ j) i }

-- ∂-aux : (n : ℕ) → (C : CW) → ℕ → C .fst (suc n) → S₊ (suc n)
-- ∂-aux n C m x = ∂-aux-gen n C m (fst (C .snd .snd .snd .snd n) x)

-- -- Please check my indices...
-- pre∂ : (n : ℕ) (C : CW) → Fin (C .snd .fst (suc n)) → Fin (C .snd .fst n) → ℤ
-- pre∂ zero (C , f , α , e₀ , e₊) x y = pos (e₀ .fst (α zero (x , true)) .fst) - pos (e₀ .fst (α zero (x , false)) .fst)
-- pre∂ (suc n) C x y = degree n λ z → ∂-aux n C (y .fst) (α (x , z))
--   where
--   Aₙ₊₂ : Type
--   Aₙ₊₂ = Fin (fst (snd C) (suc (suc n)))

--   α : Aₙ₊₂ × S₊ (suc n) → fst C (suc n)
--   α = snd C .snd .fst (suc n)

-- module _ (C : CW) where
--   ∂ : (n : ℕ) → ℤ[A snd C .fst (suc n) ] .fst → ℤ[A snd C .fst n ] .fst
--   ∂ n f a = sumFin λ b → f b ·ℤ (pre∂ n C b a)

--   ∂-hom : (n : ℕ) → AbGroupHom ℤ[A snd C .fst (suc n) ] ℤ[A snd C .fst n ]
--   fst (∂-hom n) = ∂ n
--   snd (∂-hom n) =
--     makeIsGroupHom λ f g → funExt λ x →
--       cong (sumFin {n = snd C .fst (suc n)})
--         (funExt (λ y → ·DistL+ (f y) (g y) (pre∂ n C y x)))
--     ∙ sumFin-hom (λ b → f b ·ℤ pre∂ n C b x) (λ b → g b ·ℤ pre∂ n C b x)

--   ∂* : ∀ {ℓ} (n : ℕ) (G : AbGroup ℓ)
--     → HomGroup (AbGroup→Group (ℤ[A snd C .fst n ])) G .fst
--     → HomGroup (AbGroup→Group (ℤ[A snd C .fst (suc n) ])) G .fst
--   ∂* n G f = compGroupHom (∂-hom n) f

--   ∂*-hom : ∀ {ℓ} (n : ℕ) (G : AbGroup ℓ)
--     → AbGroupHom (HomGroup (AbGroup→Group (ℤ[A snd C .fst n ])) G)
--                   (HomGroup (AbGroup→Group (ℤ[A snd C .fst (suc n) ])) G)
--   fst (∂*-hom n G) = ∂* n G
--   snd (∂*-hom n G) =
--     makeIsGroupHom λ f g → Σ≡Prop (λ _ → isPropIsGroupHom _ _)
--     refl

--   deg1 : {!degree ?!}
--   deg1 = {!!}



--   -- Need elimination principle for FreeAbGroup I think

--   ∂² : (n : ℕ) (f : _) (a : _) → ∂ n (∂ (suc n) f) a ≡ 0
--   ∂² n f a =
--      cong (sumFin {n = snd C .fst (suc n)})
--        (funExt (λ g → cong (_·ℤ pre∂ n C g a) (refl {x = sumFin (λ b → f b ·ℤ (pre∂ (suc n) C b g))}) ∙ refl))
--     ∙ (λ _ → sumFin (λ (x : Fin (C .snd .fst (suc n))) → sumFin (λ (b : Fin (snd C .fst (suc (suc n)))) → f b ·ℤ pre∂ (suc n) C b x) ·ℤ pre∂ n C x a))
--     ∙ {!a!}


-- ∂²* : (C : CW) (n : ℕ) (s : _) (a : _) → ∂ C n (∂ C (suc n) (generator s)) a ≡ pos zero
-- ∂²* (C , s , e₀ , e₊) zero (zero , t) a = {!!} -- f b₀ = 1,
-- ∂²* (C , s , e₀ , e₊) zero (suc s' , t) a = {!!}
-- ∂²* C (suc n) b₀ a = PT.rec {!!} (λ Fpt → ((λ _ → sumFin (λ (x : Fin (C .snd .fst (suc (suc n))))
--   → sumFin (λ (b : Fin (snd C .fst (suc (suc (suc n))))) → generator b₀ b ·ℤ pre∂ (suc (suc n)) C b x) ·ℤ pre∂ (suc n) C x a)))
--   ∙ help
--   ∙ (λ j → sumFin (λ x →  help₁ a x j))
--   ∙ (λ _ → wedge-deg _ (suc n) (induce-big-wedge _ _ (F∙ a Fpt)))
--   ∙ {!!})
--   ∥F∙∥
--   module _ where
--   α = C .snd .snd .fst

--   help : (sumFin (λ (x : Fin (C .snd .fst (suc (suc n))))
--     → sumFin (λ (b : Fin (snd C .fst (suc (suc (suc n))))) → generator b₀ b ·ℤ pre∂ (suc (suc n)) C b x) ·ℤ pre∂ (suc n) C x a))
--      ≡ sumFin (λ (x : Fin (C .snd .fst (suc (suc n)))) → pre∂ (suc (suc n)) C b₀ x ·ℤ pre∂ (suc n) C x a)
--   help = {!!}

--   F : (a : Fin ((snd C .fst (suc n)))) (x : _) → S₊ (suc (suc n)) → S₊ (suc (suc n))
--   F a x = ((λ z → ∂-aux (suc n) C (x .fst) (α (suc (suc n)) (b₀ , z))) ∘ suspFun (λ w → ∂-aux n C (fst a) (α (suc n) (x , w))))

--   ∥F∙∥ : ∥ ((x : _) → F a x north ≡ north) ∥₁
--   ∥F∙∥ = {!!}

--   help₁ : (a : _) (x : _) → pre∂ (suc (suc n)) C b₀ x ·ℤ pre∂ (suc n) C x a
--                            ≡ degree (suc n) (F a x)
--   help₁ a x = cong (pre∂ (suc (suc n)) C b₀ x ·ℤ_) (degree-susp n (λ z → ∂-aux n C (a .fst) (α (suc n) (x , z))))
--               ∙ degree-mult (suc n) ((λ z → ∂-aux (suc n) C (x .fst) (α (suc (suc n)) (b₀ , z))))
--                 (suspFun λ w → ∂-aux n C (fst a) (α (suc n) (x , w)))

--   module _ (a : _) (p : (x : _) → F a x north ≡ north) where
--     F∙ : (x : _) → S₊∙ (suc (suc n)) →∙ S₊∙ (suc (suc n))
--     fst (F∙ x) = F a x
--     snd (F∙ x) = p x

--     F∙≡0 : {!!}
--     F∙≡0 = {!!}
    




-- H^_[_,_]gr : ∀ {ℓ} (n : ℕ) (C : CW) (G : AbGroup ℓ) → Group ℓ
-- H^ n [ C , G ]gr = {!kerSubgroup (∂*-hom C n G)!} // {!!}

-- H^_[_,_] : ∀ {ℓ} (n : ℕ) (C : CW) (G : AbGroup ℓ) → AbGroup ℓ
-- H^ n [ C , G ] = {!!}
