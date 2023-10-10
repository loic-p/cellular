{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.FreeAbGroup as FG renaming (FreeAbGroup to Free ; _·_ to _⋄_)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

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

sumFin0 : (n : ℕ) → sumFin (λ (x : Fin n) → 0) ≡ 0
sumFin0 zero = refl
sumFin0 (suc n) = cong (pos 0 +_) (sumFin0 n)

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
generator-is-generator {n = suc n} f (a , zero , p) with (n ≟ a)
... | lt x = ⊥.rec (¬m<m (subst (n <_) (cong predℕ p) x))
... | eq x = λ i → (·Comm (f (help (~ i))) (pos 1) (~ i)) + l2 (~ i)
  where
  help : Path (Fin (suc n)) flast (a , 0 , p)
  help = Σ≡Prop (λ _ → isProp≤) x
  l1 : (s : _) → generator (Fin↑ s) (a , zero , p) ≡ 0
  l1 s with (fst s ≟ a)
  ... | lt x = refl
  ... | eq w = ⊥.rec (¬m<m {n}
    (snd s .fst , cong (fst (snd s) +ℕ_)
      (cong suc (sym (w ∙ cong predℕ p))) ∙ snd s .snd))
  ... | gt x = refl

  l2 : sumFin (λ s → f (Fin↑ s) ·ℤ generator (Fin↑ s) (a , zero , p)) ≡ 0
  l2 = (λ i → sumFin λ s → (cong (f (Fin↑ s) ·ℤ_) (l1 s) ∙ ·Comm (f (Fin↑ s)) 0) i)
     ∙ (sumFin0 n)

... | gt x = ⊥.rec (¬m<m (subst (_< n) (cong predℕ p) x))
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


module _ {ℓ} (n : ℕ) (P : ℤ[A (suc n) ] .fst → Type ℓ)
         (gens : (x : _) → P (generator x))
         (ind- : ((f : _) → P f → P (λ x → -ℤ (f x))))
         (ind+ : (f g : _) → P f → P g → P (λ x → f x + g x)) where

  private
    P-resp·pos : (x : ℕ) (f : ℤ[A (suc n) ] .fst) → P f → P (λ x₁ → pos x ·ℤ f x₁)
    P-resp·pos zero f d =
      subst P  (funExt (λ x → -Cancel (generator fzero x)))
      (ind+ (generator fzero)
        (λ x → -ℤ (generator fzero x))
          (gens fzero) (ind- _ (gens fzero)))
    P-resp·pos (suc zero) f d = d
    P-resp·pos (suc (suc x)) f d =
      ind+ f (λ a → pos (suc x) ·ℤ f a) d (P-resp·pos (suc x) f d)

  P-resp· : (x : _) (f : ℤ[A (suc n) ] .fst) → P f → P (λ x₁ → x ·ℤ f x₁)
  P-resp· (pos n) f d = P-resp·pos n f d
  P-resp· (negsuc n) f d =
    subst P (funExt (λ r → -DistL· (pos (suc n)) (f r)))
     (ind- (λ x → pos (suc n) ·ℤ f x) (P-resp·pos (suc n) _ d))

  P-resp-sumFin : (m : ℕ) (f : Fin (suc n) → Fin m → ℤ)
                → ((t : _) → P (λ x → f x t))
                → P (λ t → sumFin {n = m} (f t))
  P-resp-sumFin zero f r = P-resp·pos zero (generator fzero) (gens fzero)
  P-resp-sumFin (suc m) f r =
    ind+ (λ t → f t flast) (λ t → sumFin (λ x → f t (Fin↑ x)))
      (r flast)
      (P-resp-sumFin m (λ x y → f x (Fin↑ y)) (r ∘ Fin↑))

private
  preElimFreeAbGroup : ∀ {ℓ} {n : ℕ}
    → (P : ℤ[A (suc n) ] .fst → Type ℓ)
    → ((x : _) → P (generator x))
    → ((f : _) → P f → P (λ x → -ℤ (f x)))
    → ((f g : _) → P f → P g → P (λ x → f x + g x))
    → (x : _) → P x
  preElimFreeAbGroup {n = n} P gen d ind f =
    subst P (sym (funExt (generator-is-generator f)))
      (P-resp-sumFin n P gen d ind (suc n) (λ x y → f y ·ℤ generator y x)
        λ t → P-resp· n P gen d ind (f t) (generator t) (gen t))
-- Calling this one preElim because I dunno how to prove the obvious computation rules


sumFin' : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → (0A : A)
  → (Fin n → A)
  → (compA : A → A → A)
  → A
sumFin' zero {A = A} 0A _ _ = 0A
sumFin' (suc n) {A = A} a f comp = comp (f flast) (sumFin' n a (f ∘ Fin↑) comp)

sumFin'0 : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → (0A : A)
  → (compA : A → A → A)
  → (compA 0A 0A ≡ 0A)
  → sumFin' n 0A (λ _ → 0A) compA ≡ 0A
sumFin'0 zero 0A compA idr = refl
sumFin'0 (suc n) 0A compA idr = cong (compA 0A) (sumFin'0 n 0A compA idr) ∙ idr

sumFin'-neg : ∀ {ℓ} (n : ℕ) {A : AbGroup ℓ}
  → (f : Fin n → fst A)
  → sumFin' n (AbGroupStr.0g (snd A)) (λ x → AbGroupStr.-_ (snd A) (f x)) (AbGroupStr._+_ (snd A))
   ≡ AbGroupStr.-_ (snd A) (sumFin' n (AbGroupStr.0g (snd A)) f (AbGroupStr._+_ (snd A)))
sumFin'-neg zero {A = A} f = sym (GroupTheory.inv1g (AbGroup→Group A))
sumFin'-neg (suc n) {A = A} f =
  cong₂ compA refl (sumFin'-neg n {A = A} (f ∘ Fin↑))
  ∙∙ AbGroupStr.+Comm (snd A) _ _
  ∙∙ sym (GroupTheory.invDistr (AbGroup→Group A) _ _)
  where
  -A = AbGroupStr.-_ (snd A)
  0A = AbGroupStr.0g (snd A)
  compA = AbGroupStr._+_ (snd A)

sumFin'+ : ∀ {ℓ} (n : ℕ) {A : Type ℓ}
  → (0A : A)
  → (compA : A → A → A)
  → (f g : Fin n → A)
  → (compA 0A 0A ≡ 0A)
  → (comm : (x y : A) → compA x y ≡ compA y x)
  → (assocA : (x y z : A) → compA x (compA y z) ≡ compA (compA x y) z)
  → sumFin' n 0A (λ x → compA (f x) (g x)) compA ≡ compA (sumFin' n 0A f compA) (sumFin' n 0A g compA)
sumFin'+ zero 0A compA f g idr com as = sym idr
sumFin'+ (suc n) 0A compA f g idr com as =
     cong (compA (compA (f flast) (g flast)))
          (sumFin'+ n 0A compA (f ∘ Fin↑) (g ∘ Fin↑) idr com as)
   ∙ move4 (f flast) (g flast)
           (sumFin' n 0A (λ x → f (Fin↑ x)) compA) (sumFin' n 0A (λ x → g (Fin↑ x)) compA) compA as com

·posFree : {n : ℕ} (a : ℕ) (x : Fin n) → Free (Fin n)
·posFree {n = n} zero x = ε
·posFree {n = n} (suc a) x = ⟦ x ⟧ ⋄ (·posFree {n = n} a x)

·Free : {n : ℕ} (a : ℤ) (x : Fin n) → Free (Fin n)
·Free (pos n) x = ·posFree n x
·Free (negsuc n) x = ·posFree (suc n) x ⁻¹

·Free-lid : {n : ℕ} (x : Fin n) → ·Free 0 x ≡ ε
·Free-lid x = refl

·Free-neg : {n : ℕ} (a : ℤ) (x : Fin n) → ·Free (-ℤ a) x ≡ (·Free a x) ⁻¹
·Free-neg {n = n} (pos zero) x = sym (GroupTheory.inv1g (AbGroup→Group FAGAbGroup))
·Free-neg {n = n} (pos (suc n₁)) x = refl
·Free-neg {n = n} (negsuc n₁) x = sym (GroupTheory.invInv (AbGroup→Group FAGAbGroup) _)

·Free-suc : {n : ℕ} (a : ℤ) (x : Fin n)
  → ·Free (sucℤ a) x ≡ ⟦ x ⟧ ⋄ ·Free a x
·Free-suc (pos n) x = refl
·Free-suc (negsuc zero) x =
  sym (cong (⟦ x ⟧ ⋄_) (cong (_⁻¹) (identityᵣ ⟦ x ⟧)) ∙ invᵣ ⟦ x ⟧)
·Free-suc (negsuc (suc n)) x =
  sym (cong (⟦ x ⟧ ⋄_)
           (GroupTheory.invDistr (AbGroup→Group FAGAbGroup) ⟦ x ⟧ (⟦ x ⟧ ⋄ ·posFree n x)
          ∙ comm _ _)
  ∙∙ assoc _ _ _
  ∙∙ (cong (_⋄ (⟦ x ⟧ ⋄ ·posFree n x) ⁻¹) (invᵣ ⟦ x ⟧)
  ∙ comm _ _
  ∙ identityᵣ ((⟦ x ⟧ ⋄ ·posFree n x) ⁻¹)))

·Free-hom-pos : {n : ℕ} (a : ℕ) (b : ℤ) (x : Fin n)
             → ·Free (pos a) x ⋄ ·Free b x ≡ ·Free (pos a + b) x
·Free-hom-pos zero b x = comm _ _ ∙ identityᵣ (·Free b x) ∙ cong (λ y → ·Free y x) (+Comm b 0)
·Free-hom-pos (suc n) b x =
    sym (assoc ⟦ x ⟧ (·Free (pos n) x) (·Free b x))
  ∙ cong (⟦ x ⟧ ⋄_) (·Free-hom-pos n b x)
  ∙ l b
  where
  l : (b : ℤ) → ⟦ x ⟧ ⋄ ·Free (pos n + b) x ≡ ·Free (pos (suc n) + b) x
  l (pos m) = cong (⟦ x ⟧ ⋄_) (λ i → ·Free (pos+ n m (~ i)) x)
                             ∙ λ i → ·Free (pos+ (suc n) m i) x
  l (negsuc m) = sym (·Free-suc (pos n +negsuc m) x)
               ∙ λ j → ·Free (sucℤ+negsuc m (pos n) j) x

·Free-hom : {n : ℕ} (a b : ℤ) (x : Fin n) → ·Free a x ⋄ ·Free b x ≡ ·Free (a + b) x
·Free-hom (pos n) b x = ·Free-hom-pos n b x
·Free-hom (negsuc n) b x =
     cong ((⟦ x ⟧ ⋄ ·posFree n x) ⁻¹ ⋄_)
       (sym (cong (_⁻¹) (·Free-neg b x)
          ∙ GroupTheory.invInv (AbGroup→Group FAGAbGroup) (·Free b x)))
   ∙ comm _ _
  ∙∙ sym (GroupTheory.invDistr (AbGroup→Group FAGAbGroup) (·Free (pos (suc n)) x) (·Free (-ℤ b) x))
  ∙∙ cong (_⁻¹) (·Free-hom-pos (suc n) (-ℤ b) x)
  ∙∙ sym (·Free-neg (pos (suc n) + -ℤ b) x)
  ∙∙ λ i → ·Free (help (~ i)) x
  where
  help : negsuc n + b ≡ -ℤ (pos (suc n) + -ℤ b)
  help = cong (negsuc n +_) (sym (-Involutive b))
       ∙ sym (-Dist+ (pos (suc n)) (-ℤ b))

toHIT : (n : ℕ) → ℤ[A n ] .fst → Free (Fin n)
toHIT n f = sumFin' n {A = Free (Fin n)} ε (λ x → ·Free (f x) x) _⋄_

isContr-Free⊥ : isContr (Free ⊥)
fst isContr-Free⊥ = ε
snd isContr-Free⊥ =
  FG.ElimProp.f (trunc _ _)
    (λ {()})
    refl
    (λ p q → sym (identityᵣ ε) ∙ cong₂ _⋄_ p q)
    λ s → sym (GroupTheory.inv1g (AbGroup→Group FAGAbGroup)) ∙ cong (_⁻¹) s

isContr-FreeFin0 : isContr (Free (Fin 0))
isContr-FreeFin0 = subst (isContr ∘ Free) (sym lem) isContr-Free⊥
  where
  lem : Fin 0 ≡ ⊥
  lem = isoToPath (iso ¬Fin0 (λ{()}) (λ{()}) λ p → ⊥.rec (¬Fin0 p))

generator-vanish : (n : ℕ) (x : _) → generator {n = suc n} flast (Fin↑ x) ≡ 0
generator-vanish n x with (n ≟ (fst x))
... | lt x₁ = refl
... | eq x₁ = ⊥.rec (¬m<m {fst x} ((fst (snd x) , snd (snd x) ∙ x₁)))
... | gt x₁ = refl


Free↑ : (n : ℕ) → Free (Fin n) → Free (Fin (suc n))
Free↑ n ⟦ x ⟧ = ⟦ Fin↑ x ⟧
Free↑ n ε = ε
Free↑ n (x ⋄ x₁) = Free↑ n x ⋄ Free↑ n x₁
Free↑ n (x ⁻¹) = (Free↑ n x) ⁻¹
Free↑ n (assoc x x₁ x₂ i) = assoc (Free↑ n x) (Free↑ n x₁) (Free↑ n x₂) i
Free↑ n (comm x x₁ i) = comm (Free↑ n x) (Free↑ n x₁) i
Free↑ n (identityᵣ x i) = identityᵣ (Free↑ n x) i
Free↑ n (invᵣ x i) = invᵣ (Free↑ n x) i
Free↑ n (trunc x x₁ x₂ y i i₁) =
  isSet→isSet' trunc
    (λ _ → Free↑ n x) (λ _ → Free↑ n x₁)
    (λ j → Free↑ n (x₂ j)) (λ j → Free↑ n (y j)) i₁ i

Free↑-sumFin : (n m : ℕ) (g : Fin m → Free (Fin n))
  → Free↑ n (sumFin' m ε g _⋄_) ≡ sumFin' m ε (Free↑ n ∘ g) _⋄_
Free↑-sumFin zero zero g = refl
Free↑-sumFin zero (suc m) g =
  cong (Free↑ zero (g flast) ⋄_) (Free↑-sumFin zero m (λ x → g (Fin↑ x)))
Free↑-sumFin (suc n) zero g = refl
Free↑-sumFin (suc n) (suc m) g =
  cong (Free↑ (suc n) (g flast) ⋄_) (Free↑-sumFin (suc n) m (λ x → g (Fin↑ x)))

sum-fin-generator≡1 : (n : ℕ) (f : Fin n)
  → sumFin' n ε (λ x → ·Free (generator f x) x) _⋄_ ≡ ⟦ f ⟧
sum-fin-generator≡1 zero f = isContr→isProp isContr-FreeFin0 _ _
sum-fin-generator≡1 (suc n) (f , zero , q) with (f ≟ n)
... | lt x = ⊥.rec (¬m<m (subst (_< n) (cong predℕ q) x))
... | eq r = ((λ i → identityᵣ ⟦ help (~ i) ⟧ i
             ⋄ sumFin' n ε (λ x → ·Free (generator (help i) (Fin↑ x)) (Fin↑ x)) _⋄_))
           ∙ cong (⟦ f , zero , q ⟧ ⋄_)
                    ((λ j → sumFin' n ε (λ x₁ → ·Free (generator-vanish n x₁ j) (Fin↑ x₁)) _⋄_)
                  ∙ sumFin'0 n ε _⋄_ (identityᵣ ε))
           ∙ identityᵣ _
  where
  help : Path (Fin (suc n)) (f , zero , q) flast
  help = Σ≡Prop (λ _ → isProp≤) r
... | gt x = ⊥.rec (¬m<m (subst (_< f) (cong predℕ (sym q)) x))
sum-fin-generator≡1 (suc n) (f , suc diff , q) with (f ≟ n)
... | lt x = (λ _ → ε ⋄ sumFin' n ε (λ x → ·Free (generator (f , suc diff , q) (Fin↑ x)) (Fin↑ x)) _⋄_)
           ∙ comm _ _
           ∙ identityᵣ _
           ∙ (λ i → sumFin' n ε (λ x → lem x i) _⋄_)
           ∙ sym (Free↑-sumFin n n (λ x₁ → ·Free (generator (f , diff , (λ i → predℕ (q i))) x₁) x₁))
           ∙ cong (Free↑ n) (sum-fin-generator≡1 n (f , diff , (cong predℕ q)))
           ∙ cong ⟦_⟧ (Σ≡Prop (λ _ → isProp≤) refl)
  where
  lem : (x₁ : Fin n) → ·Free (generator (f , suc diff , q) (Fin↑ x₁)) (Fin↑ x₁)
                      ≡ Free↑ n (·Free (generator (f , diff , (λ i → predℕ (q i))) x₁) x₁)
  lem x₁ with (f ≟ fst x₁)
  ... | lt x = refl
  ... | eq x = refl
  ... | gt x = refl
... | eq x = ⊥.rec (¬m<m {suc f} (diff , +-suc diff (suc f) ∙ q ∙ cong suc (sym x)))
... | gt x = ⊥.rec (¬m<m {f} (fst x +ℕ suc diff
            , sym ((sym (snd x)) ∙ cong (fst x +ℕ_) (sym q) ∙ +-assoc (fst x) (suc diff) (suc f))))

toHIT-generator : (n : ℕ) (x : _) → toHIT n (generator x) ≡ ⟦ x ⟧
toHIT-generator zero x = isContr→isProp isContr-FreeFin0 _ _
toHIT-generator (suc n) f = sum-fin-generator≡1 _ f

fromHIT : (n : ℕ) → Free (Fin n) → ℤ[A n ] .fst
fromHIT n ⟦ x ⟧ = generator x
fromHIT n ε _ = pos 0
fromHIT n (a Free.· a₁) x = fromHIT n a x + fromHIT n a₁ x
fromHIT n (a ⁻¹) x = -ℤ fromHIT n a x
fromHIT n (assoc a a₁ a₂ i) x = +Assoc (fromHIT n a x) (fromHIT n a₁ x) (fromHIT n a₂ x) i
fromHIT n (comm a a₁ i) x = +Comm (fromHIT n a x) (fromHIT n a₁ x) i
fromHIT n (identityᵣ a i) = fromHIT n a
fromHIT n (invᵣ a i) x = -Cancel (fromHIT n a x) i
fromHIT n (trunc a a₁ x y i j) k =
  isSet→isSet' isSetℤ
    (λ _ → fromHIT n a k) (λ _ → fromHIT n a₁ k)
    (λ j → fromHIT n (x j) k) (λ j → fromHIT n (y j) k) j i

toHIT+ : (n : ℕ) → (f g : ℤ[A n ] .fst) → toHIT n (λ x → f x + g x) ≡ toHIT n f ⋄ toHIT n g
toHIT+ n f g = (λ i → sumFin' n ε (λ x → ·Free-hom  (f x) (g x) x (~ i)) _⋄_)
  ∙ sumFin'+ n ε _⋄_
    (λ x → ·Free (f x) x) (λ x → ·Free (g x) x) (identityᵣ ε) comm assoc

toHIT-inv : (n : ℕ) → (f : ℤ[A n ] .fst) → toHIT n (λ x → -ℤ (f x)) ≡ (toHIT n f) ⁻¹
toHIT-inv n f =
    (λ i → sumFin' n ε (λ x → ·Free-neg (f x) x i) _⋄_ )
  ∙ sumFin'-neg n {A = FAGAbGroup} (λ x → ·Free (f x) x)

fromTo : (n : ℕ) (x : Free (Fin n)) → toHIT n (fromHIT n x) ≡ x
fromTo zero x = isContr→isProp (subst (isContr ∘ Free) (sym lem) isContr-Free⊥) _ _
  where
  lem : Fin 0 ≡ ⊥
  lem = isoToPath (iso ¬Fin0 (λ{()}) (λ{()}) λ p → ⊥.rec (¬Fin0 p))
fromTo (suc n) =
  FG.ElimProp.f (trunc _ _)
    (toHIT-generator (suc n))
    (help (suc n))
    (λ {x = x} {y = y} p q
      → toHIT+ (suc n) (fromHIT (suc n) x) (fromHIT (suc n) y) ∙ cong₂ _⋄_ p q)
    λ {x} p → toHIT-inv (suc n) (fromHIT (suc n) x) ∙ cong (_⁻¹) p
  where
  help : (m : ℕ) → sumFin' m {A = Free (Fin (suc n))} ε (λ x → ε) _⋄_ ≡ ε
  help zero = refl
  help (suc m) = comm _ _ ∙ identityᵣ (sumFin' m ε (λ x → ε) _⋄_) ∙ help m

toFrom : (n : ℕ) (x : _) → fromHIT n (toHIT n x) ≡ x
toFrom zero f = funExt λ x → ⊥.rec (¬Fin0 x)
toFrom (suc n) =
  preElimFreeAbGroup _ (λ x → cong (fromHIT (suc n)) (toHIT-generator (suc n) x))
    (λ f p → cong (fromHIT (suc n)) (toHIT-inv (suc n) f) ∙ λ i r → -ℤ (p i r))
    λ f g p q → cong (fromHIT (suc n)) (toHIT+ (suc n) f g) ∙ λ i r → p i r + q i r

Iso-ℤ[Fin]-FreeAbGroup : (n : ℕ) → Iso (ℤ[A n ] .fst) (FAGAbGroup {A = Fin n} .fst)
Iso.fun (Iso-ℤ[Fin]-FreeAbGroup n) = toHIT n
Iso.inv (Iso-ℤ[Fin]-FreeAbGroup n) = fromHIT n
Iso.rightInv (Iso-ℤ[Fin]-FreeAbGroup n) = fromTo n
Iso.leftInv (Iso-ℤ[Fin]-FreeAbGroup n) = toFrom n

ℤ[Fin]≅FreeAbGroup : (n : ℕ) → AbGroupIso (ℤ[A n ]) (FAGAbGroup {A = Fin n})
fst (ℤ[Fin]≅FreeAbGroup n) = Iso-ℤ[Fin]-FreeAbGroup n
snd (ℤ[Fin]≅FreeAbGroup n) = makeIsGroupHom (toHIT+ n)

elimPropℤ[Fin] : ∀ {ℓ} (n : ℕ)
  (A : ℤ[A n ] .fst → Type ℓ)
  → ((x : _) → isProp (A x))
  → (A (λ _ → 0))
  → ((x : _) → A (generator x))
  → ((f g : _) → A f → A g → A λ x → f x + g x)
  → ((f : _) → A f → A (-ℤ_ ∘ f))
  → (x : _) → A x
elimPropℤ[Fin] n A pr z t s u w =
  subst A (Iso.leftInv (Iso-ℤ[Fin]-FreeAbGroup n) w) (hel (toHIT n w))
  where
  hel : (x : _) → A (fromHIT n x)
  hel = FG.ElimProp.f (pr _) t z
    (λ {x} {y} → s (fromHIT n x) (fromHIT n y))
    λ {x} → u (fromHIT n x)

-- TODO: elimSET
-- TODO: clean up
