{-# OPTIONS --cubical --safe #-}

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
open import Cubical.HITs.Sn
open import Cubical.HITs.SetTruncation as ST

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Relation.Nullary

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure

module freeabgroup where

open IsGroup
open GroupStr
open IsMonoid
open IsSemigroup

module _ {ℓ ℓ' : Level} {X : Type ℓ} (G : X → Group ℓ') where

  -- TODO: upstream
  ΠGroup : Group (ℓ-max ℓ ℓ')
  fst ΠGroup = (x : X) → fst (G x)
  1g (snd ΠGroup) x = 1g (G x .snd)
  GroupStr._·_ (snd ΠGroup) f g x = GroupStr._·_ (G x .snd) (f x) (g x)
  inv (snd ΠGroup) f x = inv (G x .snd) (f x)
  is-set (isSemigroup (isMonoid (isGroup (snd ΠGroup)))) =
    isSetΠ λ x → is-set (G x .snd)
  IsSemigroup.·Assoc (isSemigroup (isMonoid (isGroup (snd ΠGroup)))) f g h =
    funExt λ x → IsSemigroup.·Assoc (isSemigroup (isMonoid (G x .snd))) (f x) (g x) (h x)
  IsMonoid.·IdR (isMonoid (isGroup (snd ΠGroup))) f =
    funExt λ x → IsMonoid.·IdR (isMonoid (isGroup (snd (G x)))) (f x)
  IsMonoid.·IdL (isMonoid (isGroup (snd ΠGroup))) f =
    funExt λ x → IsMonoid.·IdL (isMonoid (isGroup (snd (G x)))) (f x)
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

ℤ[Fin_] : (n : ℕ) → AbGroup ℓ-zero
ℤ[Fin n ] = FreeAbGroup (Fin n)

Fin↑ : {n : ℕ} → Fin n → Fin (suc n)
Fin↑ {n = n} p = fst p , <-trans (snd p) (0 , refl)

-- Summation over Fin n (most general version)
sumFinGen : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (_+_ : A → A → A) (0A : A) (f : Fin n → A) → A
sumFinGen {n = zero} _+_ 0A f = 0A
sumFinGen {n = suc n} _+_ 0A f = f flast + sumFinGen _+_ 0A (f ∘ Fin↑)

-- For groups
sumFinG : ∀ {ℓ} (G : Group ℓ) {n : ℕ} (f : Fin n → fst G) → fst G
sumFinG G f = sumFinGen (GroupStr._·_ (snd G)) (GroupStr.1g (snd G)) f

-- For Eilenberg-MacLane spaces
sumFinK : {n m : ℕ} (f : Fin n → coHomK m) → coHomK m
sumFinK {n = n} {m = m} = sumFinGen (λ x y → x +[ m ]ₖ y) (0ₖ m)

-- For ℤ[Fin_]
sumFin : {n : ℕ} (f : Fin n → ℤ) → ℤ
sumFin f = sumFinGen _+_ 0 f

sumFinGenId : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (_+_ : A → A → A) (0A : A)
  (f g : Fin n → A) → f ≡ g → sumFinGen _+_ 0A f ≡ sumFinGen _+_ 0A g
sumFinGenId _+_ 0A f g p i = sumFinGen _+_ 0A (p i)

sumFinId : (n : ℕ) {f g : Fin n → ℤ}
  → ((x : _) → f x ≡ g x) → sumFin f ≡ sumFin g
sumFinId n t i = sumFin λ x → t x i

module _ {ℓ} {A : Type ℓ} (_+A_ : A → A → A) (0A : A)
  (rUnit : (x : _) → x +A 0A ≡ x)
   where

  sumFinGen0 : (n : ℕ) (f : Fin n → A)
    → ((x : _) → f x ≡ 0A)
    → sumFinGen _+A_ 0A f
    ≡ 0A
  sumFinGen0 zero f ind = refl
  sumFinGen0 (suc n) f ind =
    cong₂ _+A_
      (ind flast)
      (sumFinGen0 n (f ∘ Fin↑) (λ x → ind (Fin↑ x))) ∙ rUnit 0A

  module _ (comm : (x y : A) → x +A y ≡ y +A x) where
    private
      lUnitA : (x : _) → 0A +A x ≡ x
      lUnitA x = comm _ _ ∙ rUnit x

    sumFin-choose :
      {n : ℕ} (f : Fin n → A)
      → (a : A) (x : Fin n)
      → (f x ≡ a)
      → ((x' : Fin n) → ¬ (x' ≡ x) → f x' ≡ 0A)
      → sumFinGen {n = n} _+A_ 0A f ≡ a
    sumFin-choose {zero} f a x p t = ⊥.rec (¬Fin0 x)
    sumFin-choose {suc n} f a x p t with (n ≟ fst x)
    ... | lt x₁ =
      ⊥.rec (¬m<m {suc n} ((fst (snd x)) +ℕ fst x₁
           , (sym (+-assoc (fst (snd x)) (fst x₁) (suc (suc n)))
           ∙ (cong (fst (snd x) +ℕ_ ) (+-suc (fst x₁) (suc n))))
           ∙ sym ((sym (snd x .snd))
                ∙ cong (fst (snd x) +ℕ_) (sym (cong suc (x₁ .snd))))))
    ... | eq x₁ =
      cong (f flast +A_) (sumFinGen0 n _
        λ h → t _ λ q → ¬m<m (subst (_< n) (cong fst q ∙ sym x₁) (snd h)))
             ∙ rUnit _ ∙ sym (cong f x=flast) ∙ p
      where
      x=flast : x ≡ flast
      x=flast = Σ≡Prop (λ _ → isProp≤) (sym x₁)
    ... | gt x₁ =
      cong₂ _+A_
         (t flast (λ p → ¬m<m (subst (_< n) (sym (cong fst p)) x₁)))
         refl
      ∙ lUnitA _
      ∙ sumFin-choose {n = n} (f ∘ Fin↑) a (fst x , x₁)
          (cong f (Σ≡Prop (λ _ → isProp≤) refl) ∙ p)
          λ a r → t (Fin↑ a) λ d → r (Σ≡Prop (λ _ → isProp≤)
          (cong fst d))

    module _ (assocA : (x y z : A) → x +A (y +A z) ≡ (x +A y) +A z) where
      sumFinGen-hom : (n : ℕ) (f g : Fin n → A)
        → sumFinGen _+A_ 0A (λ x → f x +A g x)
         ≡ (sumFinGen _+A_ 0A f +A sumFinGen _+A_ 0A g)
      sumFinGen-hom zero f g = sym (rUnit 0A)
      sumFinGen-hom (suc n) f g =
          cong ((f flast +A g flast) +A_) (sumFinGen-hom n (f ∘ Fin↑) (g ∘ Fin↑))
        ∙ move4 (f flast) (g flast)
                (sumFinGen _+A_ 0A (λ x → f (Fin↑ x)))
                (sumFinGen _+A_ 0A (λ x → g (Fin↑ x)))
                _+A_ assocA comm

sumFinK-comm : {n m : ℕ} (f : Fin n → S₊ m → coHomK m)
  → sumFinG (coHomGr m (S₊ m)) (λ x → ∣ f x ∣₂)
         ≡ ∣ (λ x → sumFinK {m = m} λ i → f i x) ∣₂
sumFinK-comm {n = zero} {m = m} f = refl
sumFinK-comm {n = suc n} {m = m} f =
  cong (λ y → ∣ f flast ∣₂ +[ m ]ₕ y)
    (sumFinK-comm {n = n} (f ∘ Fin↑))

sumFinG-comm : (G : Group₀) (h : GroupIso G ℤGroup) {n : ℕ}
  (f : Fin n → fst G) → sumFin (λ a → Iso.fun (fst h) (f a)) ≡ Iso.fun (fst h) (sumFinG G f)
sumFinG-comm G h {n = zero} f = sym (IsGroupHom.pres1 (snd h))
sumFinG-comm G h {n = suc n} f =
  cong₂ _+_ (λ _ → Iso.fun (fst h) (f flast)) (sumFinG-comm G h (f ∘ Fin↑))
  ∙ sym (IsGroupHom.pres· (snd h) (f flast) (sumFinG G (λ x → f (Fin↑ x))))

sumFin0 : (n : ℕ) → sumFin (λ (x : Fin n) → 0) ≡ 0
sumFin0 n = sumFinGen0 _+_ 0 (λ _ → refl) n (λ _ → 0) λ _ → refl

sumFin-hom : {n : ℕ} (f g : Fin n → ℤ)
  → sumFin (λ x → f x + g x) ≡ sumFin f + sumFin g
sumFin-hom {n = n} = sumFinGen-hom _+_ 0 (λ _ → refl) +Comm +Assoc n

generator : {n : ℕ} (k : Fin n) → ℤ[Fin n ] .fst
generator {n = n} k s with (fst k ≟ fst s)
... | lt x = 0
... | eq x = 1
... | gt x = 0

generator-comm : {n : ℕ} (x y : Fin n) → generator x y ≡ generator y x
generator-comm x y with (fst x ≟ fst y) | (fst y ≟ fst x)
... | lt x₁ | lt x₂ = refl
... | lt x₁ | eq x₂ = ⊥.rec (¬m<m (subst (_< fst y) (sym x₂) x₁))
... | lt x₁ | gt x₂ = refl
... | eq x₁ | lt x₂ = ⊥.rec (¬m<m (subst (fst y <_) x₁ x₂))
... | eq x₁ | eq x₂ = refl
... | eq x₁ | gt x₂ = ⊥.rec (¬m<m (subst (_< fst y) x₁ x₂))
... | gt x₁ | lt x₂ = refl
... | gt x₁ | eq x₂ = ⊥.rec (¬m<m (subst (_< fst x) x₂ x₁))
... | gt x₁ | gt x₂ = refl

generator-is-generator : {n : ℕ} (f : ℤ[Fin n ] .fst) (a : _)
  → f a ≡ sumFin {n = n} λ s → f s ·ℤ (generator s a)
generator-is-generator {n = zero} f a = ⊥.rec (¬Fin0 a)
generator-is-generator {n = suc n} f (a , zero , p) with (n ≟ a)
... | lt x = ⊥.rec (¬m<m (subst (n <_) (cong predℕ p) x))
... | eq x = λ i → (·Comm (f (help (~ i))) (pos 1) (~ i)) + lem₂ (~ i)
  where
  help : Path (Fin (suc n)) flast (a , 0 , p)
  help = Σ≡Prop (λ _ → isProp≤) x

  lem₁ : (s : _) → generator (Fin↑ s) (a , zero , p) ≡ 0
  lem₁ s with (fst s ≟ a)
  ... | lt x = refl
  ... | eq w = ⊥.rec (¬m<m {n} (snd s .fst , cong (fst (snd s) +ℕ_)
                (cong suc (sym (w ∙ cong predℕ p))) ∙ snd s .snd))
  ... | gt x = refl

  lem₂ : sumFin (λ s → f (Fin↑ s) ·ℤ generator (Fin↑ s) (a , zero , p)) ≡ 0
  lem₂ = (λ i → sumFin λ s → (cong (f (Fin↑ s) ·ℤ_) (lem₁ s)
                            ∙ ·Comm (f (Fin↑ s)) 0) i)
       ∙ (sumFin0 n)

... | gt x = ⊥.rec (¬m<m (subst (_< n) (cong predℕ p) x))
generator-is-generator {n = suc n} f (a , suc diff , p) =
     cong f (Σ≡Prop (λ _ → Cubical.Data.Nat.Order.isProp≤) refl)
  ∙∙ generator-is-generator {n = n} (f ∘ Fin↑) (a , diff , cong predℕ p)
  ∙∙ (λ i → sumFin (λ x → f (Fin↑ x) ·ℤ lem₁ x a diff p i))
  ∙∙ +Comm F 0
  ∙∙ λ i → (sym (·Comm (f flast) 0)
           ∙ (cong (f flast ·ℤ_) (sym (lem₂ flast refl)))) i + F
  where
  F = sumFin (λ x → f (Fin↑ x) ·ℤ generator (Fin↑ x) (a , suc diff , p))

  lem₁ : (x : _) (a : _) (diff : _) (p : _)
    → generator {n = n} x (a , diff , cong predℕ p)
     ≡ generator {n = suc n} (Fin↑ x) (a , suc diff , p)
  lem₁ x a diff p with (fst x ≟ a)
  ... | lt _ = refl
  ... | eq _ = refl
  ... | gt _ = refl

  lem₂ : (k : Fin (suc n)) → fst k ≡ n
    → generator {n = suc n} k (a , suc diff , p) ≡ 0
  lem₂ k q with (Cubical.Data.Nat.Order._≟_ (fst k) a)
  ... | lt _ = refl
  ... | eq x = ⊥.rec
    (snotz (sym (+∸ (suc diff) a)
           ∙ cong (_∸ a) (sym (+-suc diff a))
           ∙ (cong (_∸ suc a) (p ∙ cong suc (sym q ∙ x)))
           ∙ n∸n a))
  ... | gt _ = refl

generator-is-generator' : {n : ℕ} (f : ℤ[Fin n ] .fst) (a : _)
  → f a ≡ sumFin {n = n} λ s → (generator a s) ·ℤ f s
generator-is-generator' {n = n} f a =
  generator-is-generator f a
  ∙ sumFinId n λ x → ·Comm (f x) (generator x a)
                     ∙ cong (_·ℤ f x) (generator-comm x a)

module _ {ℓ} (n : ℕ) (P : ℤ[Fin (suc n) ] .fst → Type ℓ)
         (gens : (x : _) → P (generator x))
         (ind- : ((f : _) → P f → P (λ x → -ℤ (f x))))
         (ind+ : (f g : _) → P f → P g → P (λ x → f x + g x)) where

  private
    P-resp·pos : (x : ℕ) (f : ℤ[Fin (suc n) ] .fst) → P f → P (λ x₁ → pos x ·ℤ f x₁)
    P-resp·pos zero f d =
      subst P  (funExt (λ x → -Cancel (generator fzero x)))
      (ind+ (generator fzero)
        (λ x → -ℤ (generator fzero x))
          (gens fzero) (ind- _ (gens fzero)))
    P-resp·pos (suc zero) f d = d
    P-resp·pos (suc (suc x)) f d =
      ind+ f (λ a → pos (suc x) ·ℤ f a) d (P-resp·pos (suc x) f d)

  P-resp· : (x : _) (f : ℤ[Fin (suc n) ] .fst) → P f → P (λ x₁ → x ·ℤ f x₁)
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
    → (P : ℤ[Fin (suc n) ] .fst → Type ℓ)
    → ((x : _) → P (generator x))
    → ((f : _) → P f → P (λ x → -ℤ (f x)))
    → ((f g : _) → P f → P g → P (λ x → f x + g x))
    → (x : _) → P x
  preElimFreeAbGroup {n = n} P gen d ind f =
    subst P (sym (funExt (generator-is-generator f)))
      (P-resp-sumFin n P gen d ind (suc n) (λ x y → f y ·ℤ generator y x)
        λ t → P-resp· n P gen d ind (f t) (generator t) (gen t))
-- Calling this one preElim because I dunno how to prove the obvious computation rules


sumFinG-neg : ∀ {ℓ} (n : ℕ) {A : AbGroup ℓ}
  → (f : Fin n → fst A)
  → sumFinG (AbGroup→Group A) {n} (λ x → AbGroupStr.-_ (snd A) (f x))
   ≡ AbGroupStr.-_ (snd A) (sumFinG (AbGroup→Group A) {n} f)
sumFinG-neg zero {A} f = sym (GroupTheory.inv1g (AbGroup→Group A))
sumFinG-neg (suc n) {A} f =
  cong₂ compA refl (sumFinG-neg n {A = A} (f ∘ Fin↑))
  ∙∙ AbGroupStr.+Comm (snd A) _ _
  ∙∙ sym (GroupTheory.invDistr (AbGroup→Group A) _ _)
  where
  -A = AbGroupStr.-_ (snd A)
  0A = AbGroupStr.0g (snd A)
  compA = AbGroupStr._+_ (snd A)

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

toHIT : (n : ℕ) → ℤ[Fin n ] .fst → Free (Fin n)
toHIT n f = sumFinGen {A = Free (Fin n)} _⋄_ ε (λ x → ·Free (f x) x)

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
  → Free↑ n (sumFinGen _⋄_ ε g) ≡ sumFinGen _⋄_ ε (Free↑ n ∘ g)
Free↑-sumFin zero zero g = refl
Free↑-sumFin zero (suc m) g =
  cong (Free↑ zero (g flast) ⋄_) (Free↑-sumFin zero m (λ x → g (Fin↑ x)))
Free↑-sumFin (suc n) zero g = refl
Free↑-sumFin (suc n) (suc m) g =
  cong (Free↑ (suc n) (g flast) ⋄_) (Free↑-sumFin (suc n) m (λ x → g (Fin↑ x)))

sum-fin-generator≡1 : (n : ℕ) (f : Fin n)
  → sumFinGen _⋄_ ε (λ x → ·Free (generator f x) x) ≡ ⟦ f ⟧
sum-fin-generator≡1 zero f = isContr→isProp isContr-FreeFin0 _ _
sum-fin-generator≡1 (suc n) (f , zero , q) with (f ≟ n)
... | lt x = ⊥.rec (¬m<m (subst (_< n) (cong predℕ q) x))
... | eq r = ((λ i → identityᵣ ⟦ help (~ i) ⟧ i
             ⋄ sumFinGen _⋄_ ε (λ x → ·Free (generator (help i) (Fin↑ x)) (Fin↑ x))))
           ∙ cong (⟦ f , zero , q ⟧ ⋄_)
                    ((λ j → sumFinGen _⋄_ ε (λ x₁ → ·Free (generator-vanish n x₁ j) (Fin↑ x₁)))
                  ∙ sumFinGen0 _⋄_ ε identityᵣ n (λ x₁ → ·Free (pos 0) (Fin↑ x₁)) (λ _ → refl))
           ∙ identityᵣ _
  where
  help : Path (Fin (suc n)) (f , zero , q) flast
  help = Σ≡Prop (λ _ → isProp≤) r
... | gt x = ⊥.rec (¬m<m (subst (_< f) (cong predℕ (sym q)) x))
sum-fin-generator≡1 (suc n) (f , suc diff , q) with (f ≟ n)
... | lt x = (λ _ → ε ⋄ sumFinGen _⋄_ ε (λ x → ·Free (generator (f , suc diff , q) (Fin↑ x)) (Fin↑ x)))
           ∙ comm _ _
           ∙ identityᵣ _
           ∙ (λ i → sumFinGen _⋄_ ε (λ x → lem x i))
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

fromHIT : (n : ℕ) → Free (Fin n) → ℤ[Fin n ] .fst
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

toHIT+ : (n : ℕ) → (f g : ℤ[Fin n ] .fst) → toHIT n (λ x → f x + g x) ≡ toHIT n f ⋄ toHIT n g
toHIT+ n f g = (λ i → sumFinGen _⋄_ ε (λ x → ·Free-hom  (f x) (g x) x (~ i)))
  ∙ sumFinGen-hom _⋄_ ε identityᵣ comm assoc n
      (λ x → ·Free (f x) x) λ x → ·Free (g x) x

toHIT-inv : (n : ℕ) → (f : ℤ[Fin n ] .fst) → toHIT n (λ x → -ℤ (f x)) ≡ (toHIT n f) ⁻¹
toHIT-inv n f =
    (λ i → sumFinGen _⋄_ ε (λ x → ·Free-neg (f x) x i))
  ∙ sumFinG-neg n {A = FAGAbGroup} (λ x → ·Free (f x) x)

fromTo : (n : ℕ) (x : Free (Fin n)) → toHIT n (fromHIT n x) ≡ x
fromTo zero x = isContr→isProp (subst (isContr ∘ Free) (sym lem) isContr-Free⊥) _ _
  where
  lem : Fin 0 ≡ ⊥
  lem = isoToPath (iso ¬Fin0 (λ{()}) (λ{()}) λ p → ⊥.rec (¬Fin0 p))
fromTo (suc n) =
  FG.ElimProp.f (trunc _ _)
    (toHIT-generator (suc n))
    (comm _ _
    ∙∙ identityᵣ _
    ∙∙ sumFinGen0 _⋄_ ε identityᵣ n (λ _ → ε) (λ _ → refl))
    (λ {x = x} {y = y} p q
      → toHIT+ (suc n) (fromHIT (suc n) x) (fromHIT (suc n) y) ∙ cong₂ _⋄_ p q)
    λ {x} p → toHIT-inv (suc n) (fromHIT (suc n) x) ∙ cong (_⁻¹) p

toFrom : (n : ℕ) (x : _) → fromHIT n (toHIT n x) ≡ x
toFrom zero f = funExt λ x → ⊥.rec (¬Fin0 x)
toFrom (suc n) =
  preElimFreeAbGroup _
   (λ x → cong (fromHIT (suc n)) (toHIT-generator (suc n) x))
   (λ f p → cong (fromHIT (suc n)) (toHIT-inv (suc n) f) ∙ λ i r → -ℤ (p i r))
   λ f g p q → cong (fromHIT (suc n)) (toHIT+ (suc n) f g) ∙ λ i r → p i r + q i r

Iso-ℤ[Fin]-FreeAbGroup : (n : ℕ) → Iso (ℤ[Fin n ] .fst) (FAGAbGroup {A = Fin n} .fst)
Iso.fun (Iso-ℤ[Fin]-FreeAbGroup n) = toHIT n
Iso.inv (Iso-ℤ[Fin]-FreeAbGroup n) = fromHIT n
Iso.rightInv (Iso-ℤ[Fin]-FreeAbGroup n) = fromTo n
Iso.leftInv (Iso-ℤ[Fin]-FreeAbGroup n) = toFrom n

ℤ[Fin]≅FreeAbGroup : (n : ℕ) → AbGroupIso (ℤ[Fin n ]) (FAGAbGroup {A = Fin n})
fst (ℤ[Fin]≅FreeAbGroup n) = Iso-ℤ[Fin]-FreeAbGroup n
snd (ℤ[Fin]≅FreeAbGroup n) = makeIsGroupHom (toHIT+ n)

elimPropℤ[Fin] : ∀ {ℓ} (n : ℕ)
  (A : ℤ[Fin n ] .fst → Type ℓ)
  → ((x : _) → isProp (A x))
  → (A (λ _ → 0))
  → ((x : _) → A (generator x))
  → ((f g : _) → A f → A g → A λ x → f x + g x)
  → ((f : _) → A f → A (-ℤ_ ∘ f))
  → (x : _) → A x
elimPropℤ[Fin] n A pr z t s u w =
  subst A (Iso.leftInv (Iso-ℤ[Fin]-FreeAbGroup n) w) (help (toHIT n w))
  where
  help : (x : _) → A (fromHIT n x)
  help = FG.ElimProp.f (pr _) t z
    (λ {x} {y} → s (fromHIT n x) (fromHIT n y))
    λ {x} → u (fromHIT n x)

-- TODO: elimSET
-- TODO: clean up

pre-ℤ[]-funct : {n m : ℕ} (f : Fin n → Fin m) (g : ℤ[Fin n ] .fst)
  (x : Fin n) (y : Fin m) → ℤ
pre-ℤ[]-funct {n = n} {m} f g x y with ((f x .fst) ≟ y .fst)
... | lt _ = 0
... | eq _ = g x
... | gt _ = 0

pre-ℤ[]-funct-gen : {n m : ℕ} (f : Fin n → Fin m)
  (t : Fin n)  (y : Fin m)
  → pre-ℤ[]-funct f (generator t) t y
  ≡ generator (f t) y
pre-ℤ[]-funct-gen f t y with (f t .fst ≟ y .fst)
... | lt _ = refl
... | eq _ = lem
  where
  lem : _
  lem with (fst t ≟ fst t)
  ... | lt q = ⊥.rec (¬m<m q)
  ... | eq _ = refl
  ... | gt q = ⊥.rec (¬m<m q)
... | gt _ = refl

ℤ[]-funct-fun : {n m : ℕ} (f : Fin n → Fin m)
  → ℤ[Fin n ] .fst → ℤ[Fin m ] .fst
ℤ[]-funct-fun {n = n} {m} f g x =
  sumFin {n = n} λ y → pre-ℤ[]-funct f g y x

ℤ[]-funct : {n m : ℕ} (f : Fin n → Fin m)
  → AbGroupHom (ℤ[Fin n ]) (ℤ[Fin m ])
fst (ℤ[]-funct {n = n} {m} f) = ℤ[]-funct-fun f
snd (ℤ[]-funct {n = n} {m} f) =
  makeIsGroupHom λ g h
   → funExt λ x → sumFinGenId _+_ 0
              (λ y → pre-ℤ[]-funct f (λ x → g x + h x) y x)
              (λ y → pre-ℤ[]-funct f g y x + pre-ℤ[]-funct f h y x)
              (funExt (lem g h x))
          ∙ sumFinGen-hom _+_ (pos 0) (λ _ → refl) +Comm +Assoc n _ _
  where
  lem : (g h : _) (x : _) (y : Fin n)
    → pre-ℤ[]-funct f (λ x → g x + h x) y x
     ≡ pre-ℤ[]-funct f g y x + pre-ℤ[]-funct f h y x
  lem g h x y with (f y . fst ≟ x .fst)
  ... | lt _ = refl
  ... | eq _ = refl
  ... | gt _ = refl
