{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin as FN
open import Cubical.Data.Nat.Order

open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT

open import prelude

-- This should probably end up in the lib

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Stuff about choice:
choice-map : {A : Type ℓ} {B : A → Type ℓ'} (n : ℕ)
  → hLevelTrunc n ((a : A) → B a)
  → (a : A) → hLevelTrunc n (B a)
choice-map n =
  TR.rec (isOfHLevelΠ n (λ _ → isOfHLevelTrunc n))
         λ f a → ∣ f a ∣ₕ

satAC : (ℓ' : Level) (n : ℕ) (A : Type ℓ)  → Type (ℓ-max ℓ (ℓ-suc ℓ'))
satAC ℓ' n A = (B : A → Type ℓ') → isEquiv (choice-map {A = A} {B} n)

satAC₀ : {A : Type ℓ} → satAC ℓ' 0 A
satAC₀ B = isoToIsEquiv (iso (λ _ _ → tt*) (λ _ → tt*) (λ _ → refl) λ _ → refl)

-- Characterisation of Π over (Fin (suc n))
FinΠ-divide : ∀ {ℓ} (n : ℕ) {B : Fin (suc n) → Type ℓ}
  → Iso ((x : _) → B x) (B fzero × ((x : _) → B (fsuc x)))
Iso.fun (FinΠ-divide n {B = B}) f = f fzero , f ∘ fsuc
Iso.inv (FinΠ-divide n {B = B}) (x , f) (zero , p) =
  subst B (Fin-fst-≡ {i = fzero} {j = zero , p} refl) x
Iso.inv (FinΠ-divide n {B = B}) (x , f) (suc y , p) =
  subst B (Fin-fst-≡ refl) (f (y , pred-≤-pred p))
Iso.rightInv (FinΠ-divide n {B = B}) (x , f) =
  ΣPathP ((λ j → transp (λ i → B (isSetFin fzero fzero (Fin-fst-≡ (λ _ → zero)) refl j i)) j x)
  , funExt λ x → (λ j → subst B (P-id x j) (f (fst x , pred-≤-pred (suc-≤-suc (snd x)))))
                ∙ (λ i → transp (λ j → B (P' x (i ∨ j))) i (f (P↓ x i))))
  where
  P : (x : Fin n) → _
  P x = Fin-fst-≡ {i = (fsuc (fst x , pred-≤-pred (snd (fsuc x))))} {j = fsuc x} refl

  P↓ : (x : _) → _ ≡ _
  P↓ x = Fin-fst-≡ refl

  P' : (x : Fin n) → _
  P' x = cong fsuc (P↓ x)

  P-id : (x : Fin n) → P x ≡ P' x
  P-id x = isSetFin _ _ _ _

Iso.leftInv (FinΠ-divide n {B = B}) f =
  funExt λ { (zero , p) j → transp (λ i → B (Fin-fst-≡ {i = fzero} {j = zero , p} refl (i ∨ j)))
                                    j (f (Fin-fst-≡ {i = fzero} {j = zero , p} refl j))
           ; (suc x , p) j → transp (λ i → B (q x p (i ∨ j))) j (f (q x p j))}
  where
  q : (x : _) (p : _) → _
  q x p = Fin-fst-≡ {i = (fsuc (x , pred-≤-pred p))} {j = suc x , p} refl

-- Main theorem Fin m satisfies AC for any level n.
FinSatAC : (n m : ℕ) → ∀ {ℓ} → satAC ℓ n (Fin m)
FinSatAC n zero B =
  isoToIsEquiv (iso _
    (λ f → ∣ (λ x → ⊥.rec (¬Fin0 x)) ∣ₕ)
    (λ f → funExt λ x → ⊥.rec (¬Fin0 x))
    (TR.elim (λ _ → isOfHLevelPath n (isOfHLevelTrunc n) _ _)
      λ a → cong  ∣_∣ₕ (funExt λ x → ⊥.rec (¬Fin0 x))))
FinSatAC n (suc m) B =
  subst isEquiv (ac-eq n m {B} (FinSatAC n m))
    (isoToIsEquiv (ac-map' n m B (FinSatAC n m)))
  where
  ac-map' : ∀ {ℓ} (n m : ℕ) (B : Fin (suc m) → Type ℓ) → (satAC ℓ n (Fin m))
    → Iso (hLevelTrunc n ((x : _) → B x)) ((x : _) → hLevelTrunc n (B x))
  ac-map' n m B ise =
    compIso (mapCompIso (FinΠ-divide m))
            (compIso (truncOfProdIso n)
              (compIso (Σ-cong-iso-snd λ _ → equivToIso (_ , ise (λ x → B (fsuc x))))
                (invIso (FinΠ-divide m))))

  ac-eq : (n m : ℕ) {B : _} → (eq : satAC ℓ n (Fin m))
       → Iso.fun (ac-map' n m B eq) ≡ choice-map {B = B} n
  ac-eq zero m {B = B} x = refl
  ac-eq (suc n) m {B = B} x =
    funExt (TR.elim (λ _ → isOfHLevelPath (suc n)
                             (isOfHLevelΠ (suc n)
                              (λ _ → isOfHLevelTrunc (suc n))) _ _)
      λ F → funExt
      λ { (zero , p) j → ∣ transp (λ i → B (p1 p (j ∨ i))) j (F (p1 p j)) ∣ₕ
        ; (suc x , p) j → ∣ transp (λ i → B (p2 x p (j ∨ i))) j (F (p2 x p j)) ∣ₕ})
    where
    p1 : (p : _ ) → fzero ≡ (zero , p)
    p1 p = Fin-fst-≡ refl

    p2 : (x : _) (p : suc x < suc m)
      → Path (Fin _) (fsuc (x , pred-≤-pred p)) (suc x , p)
    p2 x p = Fin-fst-≡ refl


-- Version of (propositional) AC with ∃
AC∃-map : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  → ∃[ f ∈ ((a : A) → B a) ] ((a : _) → C a (f a))
  → ((a : A) → ∃ (B a) (C a))
AC∃-map =
  PT.rec (isPropΠ (λ _ → squash₁))
    λ f → λ a → ∣ f .fst a , f .snd a ∣₁

satAC∃ : ∀ {ℓ} (ℓ' ℓ'' : Level) (A : Type ℓ) → Type _
satAC∃ ℓ' ℓ'' A = (B : A → Type ℓ') (C : (a : A) → B a → Type ℓ'')
  → isEquiv (AC∃-map {B = B} {C = C})

satAC→satAC∃ : {A : Type ℓ}
  → satAC (ℓ-max ℓ' ℓ'') (suc zero) A → satAC∃ ℓ' ℓ'' A
satAC→satAC∃ F B C = propBiimpl→Equiv squash₁ (isPropΠ (λ _ → squash₁))
  _
  (λ f → invEq propTrunc≃Trunc1 (TR.map (λ f → fst ∘ f , λ a → f a .snd )
          (invEq (_ , F (λ x → Σ (B x) (C x))) λ a → fst propTrunc≃Trunc1 (f a)))) .snd

-- Key result for construction of cw-approx at lvl 0
satAC∃Fin : (n : ℕ) → satAC∃ ℓ ℓ' (Fin n)
satAC∃Fin n = satAC→satAC∃ (FinSatAC 1 n)
