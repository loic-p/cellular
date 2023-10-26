{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Fin

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.FreeAbGroup.Base

open import Cubical.Homotopy.Loopspace

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Algebra.Group.MorphismProperties

-- all that stuff should probably go in the library somewhere

-- terminal map from any type to Unit
terminal : (A : Type) → A → Unit
terminal A x = tt

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

suspFun-comp : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} (f : B → C) (g : A → B)
               → suspFun (f ∘ g) ≡ (suspFun f) ∘ (suspFun g)
suspFun-comp f g i north = north
suspFun-comp f g i south = south
suspFun-comp f g i (merid a i₁) = merid (f (g a)) i₁

suspFun-const : ∀ {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} (b : B) → suspFun (λ (_ : A) → b) ≡ λ _ → north
suspFun-const b i north = north
suspFun-const b i south = merid b (~ i)
suspFun-const b i (merid a j) = merid b (~ i ∧ j)

suspFun-id : ∀ {ℓA} {A : Type ℓA} → suspFun (λ (a : A) → a) ≡ λ x → x
suspFun-id i north = north
suspFun-id i south = south
suspFun-id i (merid a j) = merid a j

-- a pointed map is constant iff its non-pointed part is constant
constant-pointed : ∀ {ℓA ℓB} {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B)
                 → fst f ≡ fst (const∙ A B) → f ≡ const∙ A B
constant-pointed {A = A} {B = B , b} f Hf i =
  (λ x → ((λ j → Hf j x) ∙∙ (λ j → Hf (~ j) (pt A)) ∙∙ (snd f)) i)
  , λ j → hcomp (λ k → λ { (i = i0) → invSides-filler (λ i → Hf i (pt A)) (λ i → snd f i) k (~ j)
                           ; (i = i1) → snd f k
                           ; (j = i1) → snd f k })
          (Hf ((~ i) ∧ (~ j)) (pt A))

constAbGroupHom : ∀ {ℓA} {ℓB} → (A : AbGroup ℓA) → (B : AbGroup ℓB) → AbGroupHom A B
fst (constAbGroupHom A B) = λ _ → B .snd .AbGroupStr.0g
snd (constAbGroupHom A B) = makeIsGroupHom λ a b → sym (B .snd .AbGroupStr.+IdL (B .snd .AbGroupStr.0g))
