{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

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
open import spherebouquet hiding (chooseS ; degree)

module cw-alt2 where

-- defn of the degree map
chooseS : (n : ℕ) (a b : ℕ) → S₊ n → S₊ n
chooseS n a b x with (discreteℕ a b)
... | yes p = x
... | no ¬p = ptSn n

degree : (n : ℕ) → (S₊ (suc n) → S₊ (suc n)) → ℤ
degree n f = Iso.fun ((Hⁿ-Sⁿ≅ℤ n) .fst) ∣ (λ x → ∣ f x ∣) ∣₂

--- CW complexes ---

-- Definition of (the skeleton) of an arbitrary CW complex
yieldsCW : (ℕ → Type) → Type
yieldsCW X =
  Σ[ f ∈ (ℕ → ℕ) ]
        (Σ[ α ∈ ((n : ℕ) → (Fin (f (suc n)) × (S₊ n)) → X n) ]
         ((X zero ≃ Fin (f 0))
        × ((n : ℕ) → X (suc n) ≃ Pushout (α n) fst)))

CW : Type₁
CW = Σ[ X ∈ (ℕ → Type) ] (yieldsCW X)

-- Technically, a CW complex should be the sequential colimit over the following maps
CW↪ : (T : CW) → (n : ℕ) → fst T n → fst T (suc n)
CW↪ (X , α , e₀ , e₊) n x = invEq (e₊ .snd n) (inl x)

-- But if it stabilises, no need for colimits.
yieldsFinCW : (n : ℕ) (X : ℕ → Type) → Type
yieldsFinCW n X =
  Σ[ CW ∈ yieldsCW X ] ((k : ℕ) → isEquiv (CW↪ (X , CW) (k +ℕ n)))

-- ... which should give us finite CW complexes.
finCW : (n : ℕ) → Type₁
finCW n = Σ[ C ∈ (ℕ → Type) ] (yieldsFinCW n C)

--the cofiber of the inclusion of X n into X (suc n)
cofiber : (n : ℕ) (C : CW) → Pointed₀
cofiber n C = Pushout (terminal (fst C n)) (CW↪ C n) , inl tt

--...is basically a sphere bouquet
cofiber≃bouquet : (n : ℕ) (C : CW)
  → cofiber n C ≃∙ (SphereBouquet (suc n) (Fin (snd C .fst (suc n))))
cofiber≃bouquet n C = Bouquet≃∙-gen n (fst (C .snd) (suc n)) (α n) e
  where
  α = C .snd .snd .fst
  e = C .snd .snd .snd .snd n

--sending X (suc n) into the cofiber
to_cofiber : (n : ℕ) (C : CW) → (fst C (suc n)) → fst (cofiber n C)
to_cofiber n C x = inr x

--the connecting map of the long exact sequence
δ : (n : ℕ) (C : CW) → fst (cofiber n C) → Susp (fst C n)
δ n C (inl x) = north
δ n C (inr x) = south
δ n C (push a i) = merid a i

--pointed version
δ∙ : (n : ℕ) (C : CW) → cofiber n C →∙ Susp∙ (fst C n)
δ∙ n C = (δ n C) , refl

suspFun-comp : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} (f : B → C) (g : A → B)
               → suspFun (f ∘ g) ≡ suspFun f ∘ (suspFun g)
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

diagonal-square : ∀ {ℓA} {A : Type ℓA} (x y z : A) (p : x ≡ y) (q : y ≡ z) → PathP (λ i → p i ≡ q i) p q
diagonal-square x y z p q i j =
  hcomp (λ k → λ { (i = i0) → p (j ∨ (~ k))
                  ; (i = i1) → q (j ∧ k)
                  ; (j = i0) → p (i ∨ (~ k))
                  ; (j = i1) → q (i ∧ k) }) y

-- there must be a less painful proof of this stupid lemma
constant-pointed : ∀ {ℓA ℓB} {A : Pointed ℓA} {B : Pointed ℓB} (f : A →∙ B)
                 → fst f ≡ fst (const∙ A B) → f ≡ const∙ A B
constant-pointed {A = A} {B = B , b} f Hf i =
  (λ x → ((λ j → Hf j x) ∙∙ (λ j → Hf (~ j) (pt A)) ∙∙ (snd f)) i)
  , λ j → hcomp (λ k → λ { (i = i0) → diagonal-square _ _ _ (λ i → Hf (~ i) (pt A)) (λ i → snd f i) j k
                           ; (i = i1) → snd f k
                           ; (j = i1) → snd f k })
          (Hf ((~ i) ∧ (~ j)) (pt A))

--now we define the boundary map as essentially Susp(to_cofiber) ∘ δ
module preboundary (n : ℕ) (C : CW) where
  Xn+1 = (fst C (suc n))
  An+1 = (snd C .fst (suc n))
  αn+1 = (snd C .snd .fst n)
  An+2 = (snd C .fst (suc (suc n)))
  αn+2 = (snd C .snd .fst (suc n))

  isoSuspBouquet : Susp∙ (fst (SphereBouquet (suc n) (Fin An+1))) →∙ SphereBouquet (suc (suc n)) (Fin An+1)
  isoSuspBouquet = Iso.fun sphereBouquetSuspIso , refl

  isoSuspBouquet↑ : Susp∙ (fst (SphereBouquet (suc (suc n)) (Fin An+1))) →∙ SphereBouquet (suc (suc (suc n))) (Fin An+1)
  isoSuspBouquet↑ = Iso.fun sphereBouquetSuspIso , refl

  isoSuspBouquetInv↑ : SphereBouquet (suc (suc (suc n))) (Fin An+2) →∙ Susp∙ (fst (SphereBouquet (suc (suc n)) (Fin An+2)))
  isoSuspBouquetInv↑ = Iso.inv sphereBouquetSuspIso , refl

  isoCofBouquet : cofiber n C →∙ SphereBouquet (suc n) (Fin An+1)
  isoCofBouquet = Iso.fun (BouquetIso-gen n An+1 αn+1 (snd C .snd .snd .snd n))
                  , refl

  isoCofBouquetInv↑ : SphereBouquet (suc (suc n)) (Fin An+2) →∙ cofiber (suc n) C
  isoCofBouquetInv↑ = (Iso.inv (BouquetIso-gen (suc n) An+2 αn+2 (snd C .snd .snd .snd (suc n))))
                     , refl

  connecting : cofiber (suc n) C →∙ Susp∙ Xn+1
  connecting = δ∙ (suc n) C

  pre∂ : (SphereBouquet (suc (suc n)) (Fin An+2)
         →∙ SphereBouquet (suc (suc n)) (Fin An+1))
  pre∂ = isoSuspBouquet ∘∙ (suspFun∙ (fst isoCofBouquet) ∘∙ ((suspFun∙ (to_cofiber n C) ∘∙ connecting) ∘∙ isoCofBouquetInv↑))

  susp-pre∂ = suspFun∙ (fst isoSuspBouquet) ∘∙ (suspFun∙ (suspFun (fst isoCofBouquet))
              ∘∙ ((suspFun∙ (suspFun (to_cofiber n C)) ∘∙ suspFun∙ (fst connecting)) ∘∙ (suspFun∙ (fst isoCofBouquetInv↑))))

  pre∂↑ : (SphereBouquet (suc (suc (suc n))) (Fin An+2)
          →∙ SphereBouquet (suc (suc (suc n))) (Fin An+1))
  pre∂↑ = isoSuspBouquet↑ ∘∙ (susp-pre∂ ∘∙ isoSuspBouquetInv↑)

  susp-pre∂-pre∂↑ : fst (bouquetSusp→ pre∂) ≡ fst pre∂↑
  susp-pre∂-pre∂↑ = congS (λ X → (fst isoSuspBouquet↑) ∘ X ∘ (fst isoSuspBouquetInv↑)) susp-distrib
    where
      susp-distrib : fst (suspFun∙ (fst pre∂)) ≡ fst susp-pre∂
      susp-distrib i north = north
      susp-distrib i south = south
      susp-distrib i (merid a i₁) = fst susp-pre∂ (merid a i₁)



module preboundary-cancellation (n : ℕ) (C : CW) where
  open preboundary

  -- interestingly, the exactness of the long cofiber sequence is really a result for pointed types
  -- so we have to exhibit a point of Xn+1 (assuming a point in Xn+2) for this result to be true
  -- which requires a bit of EM! but fortunately we are working with finite types...
  cofiber-exactness : (connecting n C .fst) ∘ (to_cofiber (suc n) C) ≡ λ x → north
  cofiber-exactness i x = merid (choose-point x) (~ i)
    where
      choose-aux : (card : ℕ) (α : Fin card × S₊ (suc n) → Xn+1 n C) → Pushout α (λ r → fst r) → Xn+1 n C
      choose-aux zero α (inl x) = x
      choose-aux zero α (inr x) with (¬Fin0 x)
      choose-aux zero α (inr x) | ()
      choose-aux zero α (push (x , _) i) with (¬Fin0 x)
      choose-aux zero α (push (x , _) i) | ()
      choose-aux (suc card') α x = α (fzero , ptSn (suc n))

      choose-point : Xn+1 (suc n) C → Xn+1 n C
      choose-point x = choose-aux (An+2 n C) (αn+2 n C) (snd C .snd .snd .snd (suc n) .fst x)

  cancellation : suspFun (connecting n C .fst) ∘ suspFun (isoCofBouquetInv↑ n C .fst)
                 ∘ (isoSuspBouquetInv↑ n C .fst) ∘ (isoSuspBouquet (suc n) C .fst)
                 ∘ (suspFun (isoCofBouquet (suc n) C .fst)) ∘ suspFun (to_cofiber (suc n) C) ≡ λ x → north
  cancellation = congS (λ X → suspFun (connecting n C .fst) ∘ suspFun (isoCofBouquetInv↑ n C .fst)
                              ∘ X ∘ (suspFun (isoCofBouquet (suc n) C .fst)) ∘ suspFun (to_cofiber (suc n) C))
                       iso-cancel-2
                 ∙∙ congS (λ X → suspFun (connecting n C .fst) ∘ X ∘ suspFun (to_cofiber (suc n) C))
                          iso-cancel-1
                 ∙∙ cofiber-exactness↑
    where
      cofiber-exactness↑ : suspFun (connecting n C .fst) ∘ suspFun (to_cofiber (suc n) C) ≡ λ x → north
      cofiber-exactness↑ = sym (suspFun-comp _ _)
                           ∙∙ congS suspFun cofiber-exactness
                           ∙∙ suspFun-const north

      iso-cancel-1 : suspFun (isoCofBouquetInv↑ n C .fst) ∘ suspFun (isoCofBouquet (suc n) C .fst) ≡ λ x → x
      iso-cancel-1 = sym (suspFun-comp _ _)
                     ∙∙ congS suspFun (λ i x → Iso.leftInv (BouquetIso-gen (suc n) (An+2 n C) (αn+2 n C)
                                                                            (snd C .snd .snd .snd (suc n))) x i)
                     ∙∙ suspFun-id

      iso-cancel-2 : (isoSuspBouquetInv↑ n C .fst) ∘ (isoSuspBouquet (suc n) C .fst) ≡ λ x → x
      iso-cancel-2 i x = Iso.leftInv sphereBouquetSuspIso x i

  left-maps = (isoSuspBouquet↑ n C .fst) ∘ (suspFun (isoSuspBouquet n C .fst))
              ∘ (suspFun (suspFun (isoCofBouquet n C .fst))) ∘ (suspFun (suspFun (to_cofiber n C)))

  right-maps = (connecting (suc n) C .fst) ∘ (isoCofBouquetInv↑ (suc n) C .fst)

  pre∂↑pre∂≡0 : fst (pre∂↑ n C) ∘ fst (pre∂ (suc n) C) ≡ λ _ → inl tt
  pre∂↑pre∂≡0 = congS (λ X → left-maps ∘ X ∘ right-maps) cancellation

  pre∂pre∂≡0 : (bouquetSusp→ (pre∂ n C)) ∘∙ (pre∂ (suc n) C) ≡ ((λ _ → inl tt) , refl)
  pre∂pre∂≡0 = constant-pointed ((bouquetSusp→ (pre∂ n C)) ∘∙ (pre∂ (suc n) C))
                                (congS (λ X → X ∘ (fst (pre∂ (suc n) C)))
                                       (susp-pre∂-pre∂↑ n C) ∙ pre∂↑pre∂≡0)

module boundary (n : ℕ) (C : CW) where
  Xn+1 = (fst C (suc n))
  An+1 = (snd C .fst (suc n))
  An+2 = (snd C .fst (suc (suc n)))

  --and then ∂ is defined as the bouquetDegree of pre∂
  ∂ : AbGroupHom (FreeAbGroup (Fin An+2)) (FreeAbGroup (Fin An+1))
  ∂ = bouquetDegree pre∂
    where
      open preboundary n C
