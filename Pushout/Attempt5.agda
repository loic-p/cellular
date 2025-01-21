{-# OPTIONS --cubical --lossy-unification --allow-unsolved-metas #-}
module Pushout.Attempt5 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.CW.Base
open import Cubical.CW.Map

open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
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

open import Cubical.Data.Nat

open import Cubical.CW.Properties
open import Cubical.Algebra.ChainComplex
open import Cubical.CW.ChainComplex
open import Cubical.CW.Homology
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Foundations.Pointed
open import Cubical.HITs.Wedge

open import Hurewicz.random
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Path


open import Cubical.Homotopy.Group.Base

private
  pathlem : ∀ {ℓ} {A : Type ℓ} {x : A}  (Fx : x ≡ x) (Fpt : refl ≡ Fx) (p q : Fx ≡ Fx)
     → Square (rUnit Fx ∙ cong (Fx ∙_) Fpt)
               (rUnit Fx ∙ cong (Fx ∙_) Fpt)
               (p ∙ q) (cong₂ _∙_ p q)
  pathlem = J> λ p q → sym (rUnit _)
    ◁ flipSquare (((λ i → (λ j → rUnit (p j) i) ∙ λ j → lUnit (q j) i)
    ▷ sym (cong₂Funct _∙_ p q)))
    ▷ rUnit _

open CWskel-fields


module _  {ℓ} {Cₙ Cₙ₊₁ Cₙ₊₂ : Type ℓ} (n mₙ mₙ₊₁ : ℕ)
      (αₙ : Fin mₙ × S⁻ n → Cₙ) (e₁ : Cₙ₊₁ ≃ Pushout αₙ (λ r → fst r))
      (αₙ₊₁ : Fin mₙ₊₁ × S₊ n → Cₙ₊₁) (e₂ : Cₙ₊₂ ≃ Pushout αₙ₊₁ (λ r → fst r))
      where
  genpre∂ : SphereBouquet (suc n) (Fin mₙ₊₁) → SphereBouquet (suc n) (Fin mₙ)
  genpre∂ = Iso.fun sphereBouquetSuspIso
            ∘ suspFun (Iso.fun (BouquetIso-gen n mₙ αₙ e₁))
            ∘ suspFun inr
            ∘ δ-pre (invEq e₂ ∘ inl)
            ∘ Iso.inv (BouquetIso-gen (suc n) mₙ₊₁ αₙ₊₁ e₂)
   where
   t  = preboundary.pre∂

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

genpre∂Simpl : ∀ {ℓ}  {Cₙ Cₙ₊₁ Cₙ₊₂ : Type ℓ} (n mₙ mₙ₊₁ : ℕ)
      (αₙ : Fin mₙ × S⁻ n → Cₙ) (e₁ : Cₙ₊₁ ≃ Pushout αₙ (λ r → fst r))
      (αₙ₊₁ : Fin mₙ₊₁ × S₊ n → Cₙ₊₁) (e₂ : Cₙ₊₂ ≃ Pushout αₙ₊₁ (λ r → fst r))
      (x : _)
      → genpre∂ n mₙ mₙ₊₁ αₙ e₁ αₙ₊₁ e₂ x
      ≡ genpre∂ n mₙ mₙ₊₁ αₙ e₁ αₙ₊₁ (idEquiv _) x
genpre∂Simpl n mₙ mₙ₊₁ αₙ e₁ αₙ₊₁ =
  EquivJ (λ _ e₂ → (x : SphereBouquet (suc n) (Fin mₙ₊₁)) →
      genpre∂ n mₙ mₙ₊₁ αₙ e₁ αₙ₊₁ e₂ x ≡
      genpre∂ n mₙ mₙ₊₁ αₙ e₁ αₙ₊₁
      (idEquiv (Pushout αₙ₊₁ (λ r → fst r))) x) λ _ → refl

genpre∂≡ : ∀ {ℓ} (B : CWskel ℓ) (n : _) (y : _)
  → preboundary.pre∂ B n y
   ≡ genpre∂ n (card B n) (card B (suc n)) (α B n) (e B n) (α B (suc n)) (e B (suc n)) y
genpre∂≡ B n y = refl

genpre∂≡Simpl : ∀ {ℓ} (B : CWskel ℓ) (n : _) (y : _)
  → preboundary.pre∂ B n y
   ≡ genpre∂ n (card B n) (card B (suc n)) (α B n) (e B n) (α B (suc n)) (idEquiv _) y
genpre∂≡Simpl B n y = genpre∂Simpl _ _ _ _ _ _ _ _

preboundarypre∂Simpl : ∀ {ℓ} (B : CWskel ℓ) (n : ℕ)
  → _
preboundarypre∂Simpl B n = genpre∂ n (card B n) (card B (suc n)) (α B n) (e B n) (α B (suc n)) (idEquiv _)

open import Cubical.Data.Empty as ⊥
module _ {ℓ : Level} (C : CWskel ℓ) where
  
  CW₁-discrete'Main : Iso (Pushout (fst (snd C .snd) 0) fst) (Fin (snd C .fst 0))
  Iso.fun CW₁-discrete'Main (inl x) = ⊥.rec (CW₀-empty C x)
  Iso.fun CW₁-discrete'Main (inr x) = x
  Iso.inv CW₁-discrete'Main = inr
  Iso.rightInv CW₁-discrete'Main x = refl
  Iso.leftInv CW₁-discrete'Main (inl x) = ⊥.rec (CW₀-empty C x)
  Iso.leftInv CW₁-discrete'Main (inr x) = refl

  CW₁-discrete' : fst C 1 ≃ Fin (snd C .fst 0)
  CW₁-discrete' = compEquiv (snd C .snd .snd .snd 0) (isoToEquiv CW₁-discrete'Main)

target source : ∀ {ℓ} (B : CWskel ℓ) → SphereBouquet 0 (Fin (card B 1)) → SphereBouquet 0 (Fin (card B 0))
target B (inl x) = inl tt
target B (inr (x , false)) = inr (fst (CW₁-discrete' B) (α B (suc zero) (x , false)) , false) 
target B (inr (x , true)) = inl tt
target B (push a i) = inl tt
source B (inl tt) = inl tt
source B (inr (x , false)) = inr (fst (CW₁-discrete' B) (α B (suc zero) (x , true)) , false) 
source B (inr (x , true)) = inl tt
source B (push a i) = inl tt

bouq1 : (B : CWskel ℓ-zero)
  → SphereBouquet∙Π (preboundary.pre∂ B 0 , refl) (bouquetSusp→ (source B) , refl)
    ≡ (bouquetSusp→ (target B) , refl) 
fst (bouq1 B i) (inl x) = inl tt
fst (bouq1 B i) (inr (x , base)) = inl tt
fst (bouq1 B i) (inr (x , loop j)) = lemma i j
  where
  lemma : cong (SphereBouquet∙Π (preboundary.pre∂ B 0 , refl)
               (bouquetSusp→ (source B) , refl) .fst) (λ j → inr (x , loop j))
      ≡ λ j → bouquetSusp→ (target B) (inr (x , loop j))
  lemma = cong₂ _∙_ (cong₃ _∙∙_∙∙_ (sym (rUnit refl)) refl (sym (rUnit refl)) ∙ sym (rUnit ((λ i₁ → preboundary.pre∂ B zero (inr (x , loop i₁))))))
                    ((cong₃ _∙∙_∙∙_ (sym (rUnit refl)) refl (sym (rUnit refl)) ∙ sym (rUnit ((λ i₁ → bouquetSusp→ (source B) (inr (x , loop i₁)))))))
        ∙ cong₂ _∙_ (cong-∙∙ (λ w → Iso.fun sphereBouquetSuspIso₀
                      (SuspBouquet→Bouquet (Fin (preboundary.An B zero)) (λ _ → S₊∙ zero)
                       (suspFun (preboundary.isoCofBouquet B zero)
                        (suspFun (to zero cofibCW B)
                         (δ-pre (CW↪ B (suc zero)) w)))))
                     _ _ _ -- _ _ _
                     ∙ doubleCompPath≡compPath _ _ _)
                    (cong-∙ (λ w → Iso.fun sphereBouquetSuspIso₀
            (SuspBouquet→Bouquet (Fin (card B 0)) (λ _ → S₊∙ zero)
             (suspFun (source B)
              (Bouquet→SuspBouquet (Fin (card B 1)) (λ _ → S₊∙ zero) (inr (x  , w)))))) _ _
              ∙ refl)
        ∙ assoc _ _ _
        ∙ cong₂ _∙_ (cong₂ _∙_ (cong₂ _∙_ (λ i → (cong (Iso.fun sphereBouquetSuspIso₀) (F (PB (fst (e B zero) (α B (suc zero) (x , false)))))))
                    (cong₂ _∙_ (λ _ _ → inl tt) (λ i → sym (cong (Iso.fun sphereBouquetSuspIso₀) (F (PB (fst (e B zero) (α B (suc zero) (x , true))))))) ∙ sym (lUnit _)))
                    (cong-∙∙ (Iso.fun sphereBouquetSuspIso₀) _ _ _
                    ∙ cong₃ _∙∙_∙∙_
                      (λ i → cong (Iso.fun sphereBouquetSuspIso₀)
                       (push (fst (CW₁-discrete' B) (α B (suc zero) (x , true)))))
                       (cong-∙ (λ w → (Iso.fun sphereBouquetSuspIso₀ (inr (fst (CW₁-discrete' B) (α B 1 (x , true))  , w)))) (merid false) (sym (merid true))
                       ∙ sym (rUnit (λ i → inr
                                      (CW₁-discrete'Main B .Iso.fun
                                       (snd B .snd .snd .snd 0 .fst (B .snd .snd .fst 1 (x , true)))
                                       , loop i))))
                       λ i → sym (cong (Iso.fun sphereBouquetSuspIso₀)
                       (push (fst (CW₁-discrete' B) (α B (suc zero) (x , true))))))

       ∙ (cong₂ _∙_ refl refl
       ∙ main (fst (e B zero) (α B 1 (x , true))) (fst (e B zero) (α B 1 (x , false))))
       ∙ cong₃ _∙∙_∙∙_ refl
         (sym (cong-∙ (λ w → (Iso.fun sphereBouquetSuspIso₀ (inr (fst (CW₁-discrete' B) (α B 1 (x , false))  , w)))) (merid false) (sym (merid true))
                       ∙ sym (rUnit (λ i → inr
                                      (CW₁-discrete'Main B .Iso.fun
                                       (snd B .snd .snd .snd 0 .fst (B .snd .snd .fst 1 (x , false)))
                                       , loop i))))) refl
       ∙ sym (cong-∙∙ (Iso.fun sphereBouquetSuspIso₀) _ _ _)) (λ _ _ → inl tt) -- cong₂ _∙_ {!!} refl
        ∙ sym (cong-∙ (λ w → Iso.fun sphereBouquetSuspIso₀
            (SuspBouquet→Bouquet (Fin (card B 0)) (λ _ → S₊∙ zero)
             (suspFun (target B)
              (Bouquet→SuspBouquet (Fin (card B 1)) (λ _ → S₊∙ zero) (inr (x  , w)))))) _ _)
        where
        F = Bouquet→ΩBouquetSusp (Fin (card B 0)) (λ _ → S₊∙ zero)
        PB = Pushout→Bouquet zero (card B zero) (α B zero) (e B zero)

        main : (x y : Pushout (fst (B .snd .snd) zero) fst)
          → (cong (Iso.fun sphereBouquetSuspIso₀ ) (F (PB y))
          ∙ cong (Iso.fun sphereBouquetSuspIso₀ ) (sym (F (PB x))))
           ∙ ((λ i → Iso.fun sphereBouquetSuspIso₀ (push (Iso.fun (CW₁-discrete'Main B) x) i))
           ∙∙ ((λ i → Iso.fun sphereBouquetSuspIso₀ (inr (Iso.fun (CW₁-discrete'Main B) x , merid false i))))
           ∙∙ (λ i → Iso.fun sphereBouquetSuspIso₀ (push (Iso.fun (CW₁-discrete'Main B) x) (~ i))))
          ≡  (λ i → Iso.fun sphereBouquetSuspIso₀ (push (Iso.fun (CW₁-discrete'Main B) y) i))
          ∙∙ (λ i → Iso.fun sphereBouquetSuspIso₀ (inr (Iso.fun (CW₁-discrete'Main B) y , merid false i)))
          ∙∙ λ i → Iso.fun sphereBouquetSuspIso₀ (push (Iso.fun (CW₁-discrete'Main B) y) (~ i))
        main (inl x) y = ⊥.rec (fst (snd (snd (snd B))) x)
        main (inr x) (inl x₁) = ⊥.rec (fst (snd (snd (snd B))) x₁)
        main (inr x) (inr y) = cong₂ _∙_ ((cong₂ _∙_ (cong-∙∙ (Iso.fun sphereBouquetSuspIso₀) _ _ _ ∙ cong₃ _∙∙_∙∙_ refl (cong-∙ (λ x → Iso.fun sphereBouquetSuspIso₀ (inr (y , x))) (merid false) (sym (merid true)) ∙ sym (rUnit (λ i → inr (y , loop i)))) refl) (
          ((cong-∙∙ (Iso.fun sphereBouquetSuspIso₀) _ _ _ ∙ cong₃ _∙∙_∙∙_ (λ _ → push x) (cong sym (cong-∙ (λ w → Iso.fun sphereBouquetSuspIso₀ (inr (x , w))) (merid false) (sym (merid true)) ∙ sym (rUnit _))) λ _ → sym (push x))))) ∙ refl) refl
          ∙ sym (assoc _ _ _)
          ∙ cong₂ _∙_ refl (rCancel _)
          ∙ sym (rUnit _)
fst (bouq1 B i) (push a j) = inl tt
snd (bouq1 B i) = refl

-- -- prefunctoriality.bouquetFunct

 -- BouquetFuns.CTB (suc n) (snd B .fst (suc n)) {!α B (suc n)!} {!!} {!!} -- (snd B .snd .fst n) ? -- (snd B .snd .snd .snd n) ? -- Pushout→Bouquet (suc n) (card B n) {!α B n!} {!!} {!!} -- Iso.fun (BouquetIso-gen (suc n) (An n) (αn n) ?) -- δ (suc n) ?
 --  where
 --  open preboundary B
 --  -- isoSuspBouquet ∘ (suspFun isoCofBouquet)
 --  --         ∘ (suspFun (to_cofibCW n C)) ∘ (δ (suc n) C) ∘ isoCofBouquetInv↑
 --  t = preboundary.pre∂ B n

Bouquet→ΩBouquetSuspPresStr : ∀ {ℓ} {A : Type ℓ} (n : ℕ)
  → (f g : S₊∙ (suc n) →∙ ⋁gen∙ A (λ _ → S₊∙ (suc n))) (s : _)
  → Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc n)) (∙Π f g .fst s)
  ≡ Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc n)) (fst f s)
  ∙ Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc n)) (fst g s)
Bouquet→ΩBouquetSuspPresStr {A = A} zero f g base =
    rUnit refl
  ∙ refl
  ∙ cong₂ _∙_ (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ 1)) (snd f)))
              (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ 1)) (snd g)))
Bouquet→ΩBouquetSuspPresStr {A = A} zero f g (loop i) j =
  m _ _ (sym (snd f)) _ (sym (snd g)) (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ 1))
    refl (cong (fst f) loop) (cong (fst g) loop) j i 
  where
  m : ∀ {ℓ} {A B : Type ℓ} (x : A) (fpt : A) (fp : x ≡ fpt) (gpt : A) (gp : x ≡ gpt)
    {b : B} (F : A → b ≡ b) (Fpt : F x ≡ refl) (fl : fpt ≡ fpt) (gl : gpt ≡ gpt)
    → Square (cong F ((fp ∙∙ fl ∙∙ sym fp) ∙ (gp ∙∙ gl ∙∙ sym gp)))
              (cong₂ _∙_ (cong F fl) (cong F gl))
              (rUnit (F x) ∙ cong (F x ∙_) (sym Fpt) ∙ cong₂ _∙_ (cong F fp) (cong F gp))
              (rUnit (F x) ∙ cong (F x ∙_) (sym Fpt) ∙ cong₂ _∙_ (cong F fp) (cong F gp))
  m x = J> (J> λ F Fpt fl gl
    → (cong (cong F) (λ j i → (rUnit fl (~ j) ∙ rUnit gl (~ j)) i)
    ∙ cong-∙ F fl gl)
    ◁ flipSquare (cong₂ _∙_ refl (sym (rUnit _))
                ◁ pathlem (F x) (sym Fpt) (cong F fl) (cong F gl)
                ▷ cong₂ _∙_ refl (rUnit _)))
Bouquet→ΩBouquetSuspPresStr {A = A} (suc n) f g north =
   rUnit refl
  ∙ refl
  ∙ cong₂ _∙_ (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc (suc n)))) (snd f)))
              (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc (suc n)))) (snd g)))
Bouquet→ΩBouquetSuspPresStr {A = A} (suc n) f g south =
  rUnit refl
  ∙ refl
  ∙ cong₂ _∙_ (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc (suc n))))
                   (cong (fst f) (sym (merid (ptSn (suc n)))) ∙ snd f)))
              (sym (cong (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc (suc n))))
                   (cong (fst g) (sym (merid (ptSn (suc n)))) ∙ snd g)))
Bouquet→ΩBouquetSuspPresStr {A = A} (suc n) f g (merid a i) j =
  m _ _ (sym (snd f)) _ (sym (snd g)) (Bouquet→ΩBouquetSusp A (λ _ → S₊∙ (suc (suc n)))) refl
    _ (cong (fst f)  (merid (ptSn (suc n)))) (cong (fst f) (merid a))
    _ (cong (fst g) (merid (ptSn (suc n)))) (cong (fst g) (merid a))
    _ (sym (cong-∙ (fst f) (merid a) (sym (merid (ptSn (suc n))))))
    _ (sym (cong-∙ (fst g) (merid a) (sym (merid (ptSn (suc n)))))) j i

  
  where
  m : ∀ {ℓ} {A B : Type ℓ} (n : A) (fn : A) (fp : n ≡ fn) (gn : A) (gp : n ≡ gn)
    {b : B} (F : A → b ≡ b) (Fn : F n ≡ refl) (fs : A) (flpt : fn ≡ fs) (fl : fn ≡ fs)  (gs : A) (glpt : gn ≡ gs) (gl : gn ≡ gs)
    (w : _) → fl ∙ sym flpt ≡ w → (u : _) → gl ∙ sym glpt ≡ u
    → Square (cong F ((fp ∙∙ w ∙∙ sym fp) ∙ (gp ∙∙ u ∙∙ sym gp)))
              (cong₂ _∙_ (cong F fl) (cong F gl)) -- (cong₂ _∙_ (cong F fl) (cong F gl))
              (rUnit (F n) ∙ cong (F n ∙_) (sym Fn) ∙ cong₂ _∙_ (cong F fp) (cong F gp))
              (rUnit (F n) ∙ cong (F n ∙_) (sym Fn)
                ∙ cong₂ _∙_ (cong F (sym (sym flpt ∙ sym fp)))
                            (cong F (sym (sym glpt ∙ sym gp))))
  m n = J> (J> λ F Fpt → J> λ fp → J> λ gp
    → J> (J> ((cong (cong F) (cong₂ _∙_ (sym (rUnit _) ∙ sym (rUnit fp))
                                         (sym (rUnit _) ∙ sym (rUnit gp)))
                           ∙  cong-∙ F fp gp)
            ◁ flipSquare (cong₂ _∙_ refl (sym (rUnit _))
              ◁ flipSquare (flipSquare (pathlem _ (sym Fpt) _ _))
            ▷ cong₂ _∙_ refl
               (rUnit _
               ∙ cong₂ _∙_ refl λ  j i → F (rUnit {x = n} refl j i)
                                       ∙ F (rUnit {x = n} refl j i))))))

⋁→Homogeneous≡ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Pointed ℓ'} {C : Type ℓ''}
  (f g : ⋁gen A B → C) → ((x : C) → isHomogeneous (C , x))
  → f (inl tt) ≡ g (inl tt)
  → ((x : _) → f (inr x) ≡ g (inr x))
  → (x : _) → f x ≡ g x
⋁→Homogeneous≡ {A = A} {B = B}{C = C} f g hom p q = funExt⁻ (cong fst main)
  where
  ptC = f (inl tt)

  f' g' : ⋁gen∙ A B →∙ (C , ptC)
  f' = f , refl
  g' = g , sym p

  ⋁→Iso : ∀ {ℓ} (C : Pointed ℓ) → Iso (⋁gen∙ A B →∙ C) ((x : A) → B x →∙ C)
  fst (Iso.fun (⋁→Iso C) f x) y = fst f (inr (x , y))
  snd (Iso.fun (⋁→Iso C) f x) = cong (fst f) (sym (push x)) ∙ snd f
  fst (Iso.inv (⋁→Iso C) f) (inl x) = pt C
  fst (Iso.inv (⋁→Iso C) f) (inr (x , y)) = f x .fst y 
  fst (Iso.inv (⋁→Iso C) f) (push a i) = f a .snd (~ i)
  snd (Iso.inv (⋁→Iso C) f) = refl
  Iso.rightInv (⋁→Iso C) f = funExt λ x → ΣPathP (refl , sym (rUnit _))
  Iso.leftInv (⋁→Iso C) f =
    ΣPathP ((funExt (λ { (inl x) → sym (snd f) ; (inr x) → refl
      ; (push a i) j → compPath-filler (cong (fst f) (sym (push a))) (snd f) (~ j) (~ i)}))
      , λ i j → snd f (~ i ∨ j))

  main : f' ≡ g'
  main = sym (Iso.leftInv (⋁→Iso (C , ptC)) f')
       ∙∙ cong (Iso.inv (⋁→Iso (C , ptC))) (funExt (λ x → →∙Homogeneous≡ (hom _) (funExt (λ y → q (x , y)))))
       ∙∙ Iso.leftInv (⋁→Iso (C , ptC)) g'

-- module _ {ℓ ℓ' : Level} where
--   Pushout→Bouquet' : {Cₙ Cₙ₊₁ Cₙ₊₂ : Type ℓ} (n mₙ mₙ₊₁ : ℕ)
--     (αₙ₊₁ : Fin mₙ₊₁ × S₊ n → Cₙ₊₁)
--     (αₙ : Fin mₙ × S⁻ n → Cₙ)
--     (e : Cₙ₊₁ ≃ Pushout αₙ fst)
--     (e2 : Cₙ₊₂ ≃ Pushout αₙ₊₁ fst)
--     → (a : Fin mₙ₊₁ × S₊ n) → SphereBouquet n (Fin mₙ)
--   Pushout→Bouquet' zero mₙ mₙ₊₁ αₙ₊₁ αₙ e e2 a = {!!}
--   Pushout→Bouquet' (suc zero) mₙ mₙ₊₁ αₙ₊₁ αₙ e e2 (l , base) = inl tt
--   Pushout→Bouquet' (suc zero) mₙ mₙ₊₁ αₙ₊₁ αₙ e e2 (l , loop i) = ({!!} ∙∙ {!λ i → ?!} ∙∙ {!!}) i
--   Pushout→Bouquet' (suc (suc n)) mₙ mₙ₊₁ αₙ₊₁ αₙ e e2 a = {!!}
--   -- inr {!!}

--   Pushout→BouquetEq : {Cₙ Cₙ₊₁ Cₙ₊₂ : Type ℓ} (n mₙ mₙ₊₁ : ℕ)
--     (αₙ₊₁ : Fin mₙ₊₁ × S₊ n → Cₙ₊₁)
--     (αₙ : Fin mₙ × S⁻ n → Cₙ)
--     (e : Cₙ₊₁ ≃ Pushout αₙ fst)
--     (e2 : Cₙ₊₂ ≃ Pushout αₙ₊₁ fst)
--     (t : _) (s : _)
--     → Pushout→Bouquet {Cₙ = Cₙ} {Cₙ₊₁} n mₙ αₙ e (fst e (αₙ₊₁ (t , s)))
--     ≡ {!Pushout→Bouquet!}
--   Pushout→BouquetEq n mₙ αₙ e = {!!}
{-
-- Maps back and forth
module BouquetFuns {Cₙ Cₙ₊₁ : Type ℓ} (n mₙ : ℕ)
    (αₙ : Fin mₙ × S⁻ n → Cₙ)
    (e : Cₙ₊₁ ≃ Pushout αₙ fst) where
  CTB : cofib (invEq e ∘ inl) → SphereBouquet n (Fin mₙ)
  CTB (inl x) = inl tt
  CTB (inr x) = Pushout→Bouquet n mₙ αₙ e (fst e x)
  CTB (push a i) = Pushout→Bouquet n mₙ αₙ e (secEq e (inl a) (~ i))
-}


module _ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} where
  foldL : A ⋁ B → fst A
  foldL (inl x) = x
  foldL (inr x) = pt A
  foldL (push a i) = pt A

  foldL∙ : (A ⋁∙ₗ B) →∙ A
  fst foldL∙ = foldL
  snd foldL∙ = refl
  
  foldR : A ⋁ B → fst B
  foldR (inl x) = pt B
  foldR (inr x) = x
  foldR (push a i) = pt B

  foldR∙ : (A ⋁∙ₗ B) →∙ B
  fst foldR∙ = foldR
  snd foldR∙ = refl

cellMap→finCellMap : ∀ {ℓ ℓ'} (m : ℕ) {C : CWskel ℓ} {D : CWskel ℓ'} (ϕ : cellMap C D) → finCellMap m C D
FinSequenceMap.fmap (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.map ϕ x
FinSequenceMap.fcomm (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.comm ϕ x


Pushout-⊎-Iso : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → Iso (A ⊎ B) (Pushout {A = ⊥} {B = A} {C = B} (λ()) λ())
Iso.fun Pushout-⊎-Iso (inl x) = inl x
Iso.fun Pushout-⊎-Iso (inr x) = inr x
Iso.inv Pushout-⊎-Iso (inl x) = inl x
Iso.inv Pushout-⊎-Iso (inr x) = inr x
Iso.rightInv Pushout-⊎-Iso (inl x) = refl
Iso.rightInv Pushout-⊎-Iso (inr x) = refl
Iso.leftInv Pushout-⊎-Iso (inl x) = refl
Iso.leftInv Pushout-⊎-Iso (inr x) = refl

IsoSphereSusp : (n : ℕ) → Iso (S₊ n) (Susp (S⁻ n))
IsoSphereSusp zero = BoolIsoSusp⊥
IsoSphereSusp (suc n) = IsoSucSphereSusp n

finSplit3≃ : ∀ n m l → Fin ((n +ℕ m) +ℕ l) ≃ ((Fin n) ⊎ (Fin m)) ⊎ (Fin l)
finSplit3≃ n m l = isoToEquiv (compIso (invIso (Iso-Fin⊎Fin-Fin+ {n = n + m} {l}))
    (⊎Iso (invIso (Iso-Fin⊎Fin-Fin+ {n = n} {m})) idIso))

finSplit3 : ∀ n m l → Fin ((n +ℕ m) +ℕ l) → ((Fin n) ⊎ (Fin m)) ⊎ (Fin l)
finSplit3 n m l = fst (finSplit3≃ n m l)

invSides-hfill : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → I → I → I → A
invSides-hfill {x = x} p q i j =
  hfill (λ k → λ { (i = i0) → p (k ∧ j)
                 ; (i = i1) → q (~ j ∧ k)
                 ; (j = i0) → q (i ∧ k)
                 ; (j = i1) → p (~ i ∧ k)})
        (inS x)

invSides-hfill1 : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → I → I → I → A
invSides-hfill1 {x = x} p q i j =
  hfill (λ k → λ { (i = i0) → p j
                 ; (i = i1) → q (~ j ∧ k)
                 ; (j = i0) → q (i ∧ k)
                 ; (j = i1) → p (~ i)})
        (inS (p ((~ i) ∧ j)))

invSides-hfill2 : {ℓ : Level} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z) → I → I → I → A
invSides-hfill2 {x = x} p q i j =
  hfill (λ k → λ { (i = i0) → p (k ∧ j)
                 ; (i = i1) → q (~ j)
                 ; (j = i0) → q (i)
                 ; (j = i1) → p (~ i ∧ k)})
        (inS (q (i ∧ (~ j))))


-- module _ {ℓ : Level} {Xₙ₊₁ : Type ℓ}

open import Cubical.Foundations.Path
open import Cubical.Data.Empty as ⊥

open import Cubical.Relation.Nullary

module _ {ℓ : Level} (B : CWskel ℓ) where
  open CWskel-fields
  open import Cubical.Foundations.Univalence
  strictifyFam : ℕ → Type ℓ
  strictifyFam≡ : (n : ℕ) → strictifyFam n ≡ fst B n
  strictifyFame : (n : ℕ) → fst B n ≃ strictifyFam n
  strictifyFamα : (n : ℕ) → Fin (fst (B .snd) n) × S⁻ n → strictifyFam n
  strictifyFame2 : (n : ℕ) → (Pushout (α B n) fst) ≃ (Pushout (strictifyFamα n) fst)
  strictifyFam zero = fst B 0
  strictifyFam (suc n) = Pushout (strictifyFamα n) fst
  strictifyFamα n = fst (strictifyFame n) ∘ α B n
  strictifyFame zero = idEquiv _
  strictifyFame (suc n) =
    compEquiv (e B n)
              (strictifyFame2 n)
  strictifyFame2 n =
    pushoutEquiv _ _ _ _ (idEquiv _) (strictifyFame n) (idEquiv _)
                   (λ _ x → fst (strictifyFame n) (α B n x))
                   (λ _ x → fst x)
  strictifyFam≡ zero = refl
  strictifyFam≡ (suc n) = ua (invEquiv (strictifyFame (suc n)))

  strictCWskel : CWskel ℓ
  fst strictCWskel = strictifyFam
  fst (snd strictCWskel) = card B
  fst (snd (snd strictCWskel)) = strictifyFamα
  fst (snd (snd (snd strictCWskel))) = fst (snd (snd (snd B)))
  snd (snd (snd (snd strictCWskel))) = λ _ → idEquiv _

  strict≡Gen : ∀ {ℓ ℓ'} {A : Type ℓ} {C D : Type ℓ'} (α : A → C) (e : C ≃ D) (x : A)
    → PathP (λ i → ua (invEquiv e) i) (fst e (α x)) (α x)
  strict≡Gen α e x i =
    hcomp (λ k → λ {(i = i0) → fst e (α x)
                   ; (i = i1) → retEq e (α x) k})
          (ua-gluePt (invEquiv e) i (fst e (α x)))

  strict≡GenT' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C D : Type ℓ''}
    {E : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))} (g : A → B)
    (e : C ≃ D)  (α : A → C) (e' : E ≃ Pushout (λ x₁ → α x₁) g)
    → PathP (λ k → ua (invEquiv (compEquiv {C = Pushout (fst e ∘ α) g} e'
                       (pushoutEquiv _ _ _ _ (idEquiv A) e (idEquiv B) (λ i x → fst e (α x)) λ i x → g x))) k
                 ≃ Pushout (λ x₁ → strict≡Gen α e x₁ k) g)
            (idEquiv _)
            e'
  strict≡GenT' {A = A} {B} {C} {D} {E} g =
    EquivJ (λ C e → (α : A → C) (e' : E ≃ Pushout (λ x₁ → α x₁) g)
    → PathP (λ k → ua (invEquiv (compEquiv {C = Pushout (fst e ∘ α) g} e'
                       (pushoutEquiv _ _ _ _ (idEquiv A) e (idEquiv B) (λ i x → fst e (α x)) λ i x → g x))) k
                 ≃ Pushout (λ x₁ → strict≡Gen α e x₁ k) g)
            (idEquiv _)
            e')
         λ a → EquivJ (λ E e' → PathP
      (λ k →
         ua
         (invEquiv
          (compEquiv e'
           (pushoutEquiv a g (λ z → idfun D (a z)) g (idEquiv A) (idEquiv D)
            (idEquiv B) (λ i x → idfun D (a x)) (λ i → g))))
         k
         ≃ Pushout (λ x₁ → strict≡Gen a (idEquiv D) x₁ k) g)
      (idEquiv (Pushout (λ x → idfun D (a x)) g)) e')
      (ΣPathPProp isPropIsEquiv
        (transport
          (λ k → PathP (λ i
            → (sym (lem g a) ∙ sym (cong (ua ∘ invEquiv) (compEquivIdEquiv ((pushoutEquiv a g
                 (λ z → idfun D (a z)) g (idEquiv A) (idEquiv D)
                   (idEquiv B) (λ i₁ x → idfun D (a x)) (λ i₁ → g)))))) k i
                             → Pushout (λ x₁ → strict≡GenId a x₁ (~ k) i) g)
                 (idfun _) (idfun _))
           (funExt (main _ _))))
    where
    strict≡GenId : ∀ {ℓ ℓ'} {A : Type ℓ} {C : Type ℓ'} (α : A → C)(x : A)
                 → strict≡Gen α (idEquiv C) x ≡ λ i → ua-gluePt (invEquiv (idEquiv C)) i (α x) 
    strict≡GenId {C = C} α x j i =
      hcomp (λ k → λ {(i = i0) → α x
                     ; (i = i1) → α x
                     ; (j = i1) → ua-gluePt (invEquiv (idEquiv C)) i (α x)})
            (ua-gluePt (invEquiv (idEquiv C)) i (α x))

    lem : (g : A → B) (α : A → D)
      → ua (invEquiv (pushoutEquiv α g α g (idEquiv A) (idEquiv D) (idEquiv B) refl refl))
      ≡ refl 
    lem g a = cong ua (cong invEquiv (Σ≡Prop isPropIsEquiv {v = idEquiv _}
      (funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) j → rUnit (push a) (~ j) i}))
      ∙ invEquivIdEquiv _) ∙ uaIdEquiv

    main : (g : A → B) (α : A → D) (w : _)
      → PathP (λ i → Pushout (λ x₁ → ua-gluePt (invEquiv (idEquiv D)) i (α x₁)) g) w w
    main g α (inl x) i = inl (ua-gluePt (invEquiv (idEquiv D)) i x)
    main g α (inr x) i = inr x
    main g α (push a j) i = push a j

  strict≡α : (n : ℕ) (x : Fin (card B n)) (y : S⁻ n)
    → PathP (λ i → strictifyFam≡ n i)
              
              (strictifyFamα n (x , y))
              (α B n (x , y))
  strict≡α (suc n) x y = strict≡Gen (α B (suc n)) (strictifyFame (suc n)) (x , y)
  
  strict≡e : (n : ℕ) → PathP (λ i → strictifyFam≡ (suc n) i
                                     ≃ Pushout (λ x → strict≡α n (fst x) (snd x) i) fst)
                               (idEquiv _)
                               (e B n)
  strict≡e zero = ΣPathPProp (λ _ → isPropIsEquiv _)
    (symP (toPathP (funExt λ { (inl x) → ⊥.rec (B .snd .snd .snd .fst x)
      ; (inr x) → cong (transport (λ i → Pushout (λ x₁ → strict≡α zero (fst x₁) (snd x₁) (~ i)) fst))
                         ((cong (e B 0 .fst) (transportRefl (invEq (e B 0) (inr x)))
                         ∙ secEq (e B 0) (inr x)))
                     ∙ λ j → inr (transportRefl x j)})))
  strict≡e (suc n) = strict≡GenT' fst (strictifyFame (suc n)) (α B (suc n)) (e B (suc n))    

  strict≡ : strictCWskel ≡ B
  fst (strict≡ i) n = strictifyFam≡ n i
  fst (snd (strict≡ i)) = card B
  fst (snd (snd (strict≡ i))) n (x , y) = strict≡α n x y i
  fst (snd (snd (snd (strict≡ i)))) = fst (snd (snd (snd B)))
  snd (snd (snd (snd (strict≡ i)))) n = strict≡e n i


-- module _ {ℓ ℓ'} {B : CWskel ℓ} {C : CWskel ℓ'} (f : cellMap B C) where

--   open CWskel-fields
--   open SequenceMap renaming (map to ∣_∣)

--   toStrictCWFun : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → fst C n → strictifyFam C n
--   toStrictCWFun C n x = {!!}

--   strictCellMapFun : (n : ℕ) → strictifyFam B n → strictifyFam C n
--   strictCellMapFun zero s = ∣ f ∣ zero s
--   strictCellMapFun (suc n) (inl x) = inl (strictCellMapFun n x)
--   strictCellMapFun (suc n) (inr x) = fst (strictifyFame C (suc n)) (∣ f ∣ (suc n) (invEq (e B n) (inr x))) 
--   strictCellMapFun (suc n) (push a i) =
--     ({!refl!} ∙∙ push ({!a!} , snd a) ∙∙ {!!}) i

--   strictFun : cellMap (strictCWskel B) (strictCWskel C)
--   ∣_∣ strictFun = {!!}
--   comm strictFun = {!!}

module _ {ℓ ℓ'} {P : CWskel ℓ → Type ℓ'} (e : (B : CWskel ℓ) → P (strictCWskel B)) where
  elimStrictCW : (B : _) → P B
  elimStrictCW B = subst P (strict≡ B) (e B)

  elimStrictCWβ : (B : _) → elimStrictCW (strictCWskel B) ≡ e B
  elimStrictCWβ B =
    (λ j → subst P (λ i → H strictCWskel (funExt (λ x → sym (strict≡ x))) B i j) (e (strict≡ B j)))
    ∙ transportRefl (e B)
    where
    H : ∀ {ℓ} {A : Type ℓ}  (F : A → A) (s : (λ x → x) ≡ F) (a : A)
      → Square (λ i → F (s (~ i) a)) refl (λ i → s (~ i) (F a)) refl
    H = J> λ _ → refl

module _ {ℓ ℓ' ℓ''} {P : CWskel ℓ → CWskel ℓ' → Type ℓ''}
         (e : (B : CWskel ℓ) (C : CWskel ℓ') → P (strictCWskel B) (strictCWskel C)) where
  elim2StrictCW : (B : _) (C : _) → P B C
  elim2StrictCW = elimStrictCW (λ B → elimStrictCW (e B))

  elim2StrictCWβ : (B : _) (C : _)
    → elim2StrictCW (strictCWskel B) (strictCWskel C) ≡ e B C
  elim2StrictCWβ B C = funExt⁻ ((elimStrictCWβ {P = λ B → (C : _) → P B C}
                                 (λ B → elimStrictCW (e B))) B) (strictCWskel C)
                     ∙ elimStrictCWβ {P = P (strictCWskel B)} (e B) C

module _ {ℓ ℓ' ℓ'' ℓ'''} {P : CWskel ℓ → CWskel ℓ' → CWskel ℓ'' → Type ℓ'''}
         (e : (B : CWskel ℓ) (C : CWskel ℓ') (D : CWskel ℓ'') → P (strictCWskel B) (strictCWskel C) (strictCWskel D)) where
  elim3StrictCW : (B : _) (C : _) (D : _) → P B C D
  elim3StrictCW = elim2StrictCW λ B C → elimStrictCW (e B C)

  elim3StrictCWβ : (B : _) (C : _) (D : _)
    → elim3StrictCW (strictCWskel B) (strictCWskel C) (strictCWskel D)
     ≡ e B C D
  elim3StrictCWβ B C D =
     funExt⁻ (elim2StrictCWβ {P = λ B C → (D : _) → P B C D}
             (λ B C → elimStrictCW (e B C)) B C) (strictCWskel D)
    ∙ elimStrictCWβ {P = P (strictCWskel B) (strictCWskel C)} (e B C) D

module _ {ℓ ℓ' ℓ'' : Level} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
  (f : cellMap B C)
  (g : cellMap B D) where

  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)

  pushoutA : ℕ → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') 
  pushoutA zero = Lift {ℓ} {ℓ-max ℓ' ℓ''} (B .fst zero)
  pushoutA (suc n) =
    Pushout {A = fst B n} {B = fst C (suc n)} {C = fst D (suc n)}
       (∣ f ∣ (suc n) ∘ CW↪ B n) (∣ g ∣ (suc n) ∘ CW↪ B n)

  pushoutMapₛ-filler : (n : ℕ) → (A B n) → (S⁻ n)
                     → I → I → pushoutA (suc n)
  pushoutMapₛ-filler n b x i k =
    doubleCompPath-filler ((λ i → inl (∣ f ∣ (suc n) (invEq (e B n) (push (b , x) (~ i))))))
      (push (α B n (b , x)))
      (λ i → inr (∣ g ∣ (suc n) (invEq (e B n) (push (b , x) i)))) k i

  pushoutMapₛ : (n : ℕ) → (((A C (suc n)) ⊎ (A D (suc n))) ⊎ (A B n)) × (Susp (S⁻ n)) → pushoutA (suc n)
  pushoutMapₛ n (inl (inl c) , x) =  inl (α C (suc n) (c , (Iso.inv (IsoSphereSusp n) x)))
  pushoutMapₛ n (inl (inr d) , x) = inr (α D (suc n) (d , (Iso.inv (IsoSphereSusp n) x)))
  pushoutMapₛ n (inr b , north) = inl (∣ f ∣ (suc n) (invEq (e B n) (inr b)))
  pushoutMapₛ n (inr b , south) = inr (∣ g ∣ (suc n) (invEq (e B n) (inr b)))
  pushoutMapₛ n (inr b , merid x i) = pushoutMapₛ-filler n b x i i1

  pushoutMidCells : ℕ → ℕ
  pushoutMidCells zero = 0
  pushoutMidCells (suc n) = (card B n)
  

  pushoutCells : ℕ → ℕ
  pushoutCells n = (card C n) +ℕ (card D n) + pushoutMidCells n

  pushoutMap₀ : (Fin (pushoutCells zero)) × (S⁻ 0) → pushoutA 0
  pushoutMap₀ ()

  pushoutMap' : (n : ℕ) → (Fin (pushoutCells (suc n))) × (Susp (S⁻ n)) → pushoutA (suc n)
  pushoutMap' n (a , x) = pushoutMapₛ n (finSplit3 (card C (suc n)) (card D (suc n)) (card B n) a , x)

  pushoutα> : (n : ℕ) → Fin (card C (suc n) + card D (suc n) + card B n) × S₊ n
                       → pushoutA (suc n)
  pushoutα> n (x , y) =
    pushoutMapₛ n ((finSplit3 (card C (suc n)) (card D (suc n)) (card B n) x)
                 , Iso.fun (IsoSphereSusp n) y)

  Iso-Pushoutα-PushoutPushoutMapₛ : (n : ℕ)
    → Iso (Pushout (pushoutMapₛ n) fst)
           (Pushout (pushoutα> n) fst)
  Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ n) (inl x) = inl x
  Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ n) (inr x) = inr (invEq (finSplit3≃ _ _ _) x)
  Iso.fun (Iso-Pushoutα-PushoutPushoutMapₛ n) (push a i) =
    ((λ j → inl (pushoutMapₛ n (secEq  (finSplit3≃ _ _ _) (fst a) (~ j)
                               , Iso.rightInv (IsoSphereSusp n) (snd a) (~ j))))
      ∙ push ((invEq (finSplit3≃ _ _ _)  (fst a))
                , (Iso.inv (IsoSphereSusp n) (snd a)))) i
  Iso.inv (Iso-Pushoutα-PushoutPushoutMapₛ n) (inl x) = inl x
  Iso.inv (Iso-Pushoutα-PushoutPushoutMapₛ n) (inr x) = inr (finSplit3 _ _ _ x)
  Iso.inv (Iso-Pushoutα-PushoutPushoutMapₛ n) (push a i) =
    (push ((finSplit3 _ _ _ (fst a))
          , (Iso.fun (IsoSphereSusp n) (snd a)))) i
  Iso.rightInv (Iso-Pushoutα-PushoutPushoutMapₛ n) (inl x) = refl
  Iso.rightInv (Iso-Pushoutα-PushoutPushoutMapₛ n) (inr x) i =
    inr (retEq (finSplit3≃ _ _ _) x i)
  Iso.rightInv (Iso-Pushoutα-PushoutPushoutMapₛ n) (push a i) j = {!!}
  Iso.leftInv (Iso-Pushoutα-PushoutPushoutMapₛ n) x = {!!}
  {- pushoutIso _ _ _ _
    (Σ-cong-equiv (invEquiv (finSplit3≃ _ _ _))
      λ _ → isoToEquiv (invIso (IsoSphereSusp n)))
    (idEquiv _)
    (invEquiv (finSplit3≃ _ _ _))
    (funExt λ x → cong (pushoutMapₛ n) (ΣPathP
      (sym (secEq (finSplit3≃ _ _ _) (fst x))
      , sym (Iso.rightInv (IsoSphereSusp n) (snd x)))))
    refl
    -}

  pushoutMap : (n : ℕ) → (Fin (pushoutCells n)) × (S⁻ n) → pushoutA n
  pushoutMap zero = pushoutMap₀
  pushoutMap (suc n) = pushoutα> n

  PushoutA→PushoutPushoutMapL : (n : ℕ) → Pushout (α C (suc n)) fst → Pushout (pushoutMapₛ n) fst
  PushoutA→PushoutPushoutMapL n (inl x) = inl (inl x)
  PushoutA→PushoutPushoutMapL n (inr x) = inr ((inl (inl x)))
  PushoutA→PushoutPushoutMapL n (push a i) =
    ((λ i → inl (inl (α C (suc n) (fst a , Iso.leftInv (IsoSphereSusp n) (snd a) (~ i)))))
    ∙ push (((inl (inl (fst a)))) , Iso.fun (IsoSphereSusp n) (snd a))) i

  PushoutA→PushoutPushoutMapR : (n : ℕ) → Pushout (α D (suc n)) fst → Pushout (pushoutMapₛ n) fst
  PushoutA→PushoutPushoutMapR n (inl x) = inl (inr x)
  PushoutA→PushoutPushoutMapR n (inr x) = inr ((inl (inr x)))
  PushoutA→PushoutPushoutMapR n (push a i) =
    ((λ i → inl (inr (α D (suc n) (fst a , Iso.leftInv (IsoSphereSusp n) (snd a) (~ i)))))
    ∙ push (((inl (inr (fst a)))) , Iso.fun (IsoSphereSusp n) (snd a))) i

  PushoutA→PushoutPushoutMapLR : (n : ℕ) (b : Pushout (α B n) fst)
    → Path (Pushout (pushoutMapₛ n) fst)
            (inl (inl (∣ f ∣ (suc n) (invEq (e B n) b))))
            (inl (inr (∣ g ∣ (suc n) (invEq (e B n) b))))
  PushoutA→PushoutPushoutMapLR n (inl x) i = inl (push x i)
  PushoutA→PushoutPushoutMapLR n (inr x) = push ((inr x) , north) ∙∙ refl ∙∙ sym (push ((inr x) , south))
  PushoutA→PushoutPushoutMapLR n (push (t , s) i) j =
    hcomp (λ k → λ {(i = i0) → inl (doubleCompPath-filler (λ i → inl (∣ f ∣ (suc n) (invEq (e B n) (push (t , s) (~ i)))))
                                                           (push (α B n (t , s)))
                                                           (λ i → inr (∣ g ∣ (suc n) (invEq (e B n) (push (t , s) i)))) (~ k) j)
                   ; (i = i1) → doubleCompPath-filler (push ((inr t) , north)) refl (sym (push ((inr t) , south))) k j
                   ; (j = i0) → invSides-filler (push (inr t , north))
                                                 (λ i → inl (inl (∣ f ∣ (suc n) (invEq (e B n) (push (t , s) (~ i)))))) k i
                   ; (j = i1) → invSides-filler (push (inr t , south))
                                                 (λ i → inl (inr (∣ g ∣ (suc n) (invEq (e B n) (push (t , s) (~ i)))))) k i})
          ((push (inr t , merid s j)) i)


  PushoutA→PushoutPushoutMap : (n : ℕ) → (pushoutA (suc (suc n))) → (Pushout (pushoutMapₛ n) fst)
  PushoutA→PushoutPushoutMap n (inl x) = PushoutA→PushoutPushoutMapL n (fst (e C (suc n)) x)
  PushoutA→PushoutPushoutMap n (inr x) = PushoutA→PushoutPushoutMapR n (fst (e D (suc n)) x)
  PushoutA→PushoutPushoutMap n (push a i) =
       (cong (PushoutA→PushoutPushoutMapL n) (cong (fst (e C (suc n))) (sym (comm f (suc n) a))
                    ∙ secEq (e C (suc n)) (inl (∣ f ∣ (suc n) a)))
    ∙∙ (λ i → ((λ i → inl (inl (∣ f ∣ (suc n) (retEq (e B n) a (~ i)))))
    ∙∙ PushoutA→PushoutPushoutMapLR n (fst (e B n) a)
    ∙∙ λ i → inl (inr (∣ g ∣ (suc n) (retEq (e B n) a i)))) i)
    ∙∙ cong (PushoutA→PushoutPushoutMapR n) (sym (cong (fst (e D (suc n))) (sym (comm g (suc n) a))
                       ∙ secEq (e D (suc n)) (inl (∣ g ∣ (suc n) a))))) i


  pushoutA↑ : (n : ℕ) → (pushoutA (suc n)) → (pushoutA (suc (suc n)))
  pushoutA↑ n (inl x) = inl (CW↪ C (suc n) x)
  pushoutA↑ n (inr x) = inr (CW↪ D (suc n) x)
  pushoutA↑ n (push a i) =
    ((λ i → inl (comm f (suc n) (CW↪ B n a) i))
    ∙∙ push (CW↪ B n a)
    ∙∙ λ i → inr (comm g (suc n) (CW↪ B n a) (~ i))) i


  module _ (n : ℕ) (x : _) (a : _) where
    PushoutPushoutMap→PushoutABotFillSide-filler : (i j k : _) → pushoutA (suc (suc n))
    PushoutPushoutMap→PushoutABotFillSide-filler i j k =
      hfill (λ k → λ {(i = i0) → push (invEq (e B n) (push (x , a) k)) j
                    ; (i = i1) → pushoutA↑ n
                      (doubleCompPath-filler
                        (λ i → inl (∣ f ∣ (suc n) (invEq (e B n) (push (x , a) (~ i)))))
                        (push (α B n (x , a)))
                        (λ i → inr (∣ g ∣ (suc n) (invEq (e B n) (push (x , a) i)))) k j)
                    ; (j = i0) → inl (comm f (suc n) (invEq (e B n) (push (x , a) k)) (~ i))
                    ; (j = i1) → inr (comm g (suc n) (invEq (e B n) (push (x , a) k)) (~ i))})
               (inS (doubleCompPath-filler
                 (λ i₂ → inl (comm f (suc n) (CW↪ B n (α B n (x , a))) i₂))
                 (push (CW↪ B n (α B n (x , a))))
                 (λ i₂ → inr (comm g (suc n) (CW↪ B n (α B n (x , a))) (~ i₂))) i j))
                 k


    PushoutPushoutMap→PushoutABotFillSide : Square {A = pushoutA (suc (suc n)) }
                ( (push (invEq (e B n) (inr x))))
                (λ i → pushoutA↑ n (pushoutMapₛ n (inr x , merid a i)))
                (λ k → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ k)))
                (λ k → inr (comm g (suc n) (invEq (e B n) (inr x)) (~ k)))
    PushoutPushoutMap→PushoutABotFillSide i j = PushoutPushoutMap→PushoutABotFillSide-filler i j i1


    PushoutPushoutMap→PushoutABotFill-filler : (i j k : _) → pushoutA (suc (suc n))
    PushoutPushoutMap→PushoutABotFill-filler i j k =
      hfill (λ k → λ {(i = i0) → PushoutPushoutMap→PushoutABotFillSide k j
                    ; (i = i1) → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ k))
                    ; (j = i0) → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ k))
                    ; (j = i1) → doubleCompPath-filler
                                    (λ i → inr (comm g (suc n) (invEq (e B n) (inr x)) i))
                                    (sym (push (invEq (e B n) (inr x))))
                                    (λ i₁ → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ i₁))) k i})
              (inS (push (invEq (e B n) (inr x)) (~ i ∧ j)))
              k


    PushoutPushoutMap→PushoutABotFill : Square {A = pushoutA (suc (suc n)) }
      (λ i → pushoutA↑ n (pushoutMapₛ n (inr x , merid a i)))
      (λ _ → inl (CW↪ C (suc n) (∣ f ∣ (suc n) (invEq (e B n) (inr x)))))
      (λ _ → inl (CW↪ C (suc n) (∣ f ∣ (suc n) (invEq (e B n) (inr x)))))
         ((λ i → inr (comm g (suc n) (invEq (e B n) (inr x)) i))
       ∙∙ sym (push (invEq (e B n) (inr x)))
       ∙∙ (λ i → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ i))))
    PushoutPushoutMap→PushoutABotFill i j = PushoutPushoutMap→PushoutABotFill-filler i j i1


  PushoutPushoutMap→PushoutABot :
    (n : ℕ) (x : A B n) (s : Susp (S⁻ n))
    → Path (pushoutA (suc (suc n))) (pushoutA↑ n (pushoutMapₛ n (inr x , s)))
            (inl (CW↪ C (suc n) ((∣ f ∣ (suc n) (invEq (e B n) (inr x))))))
  PushoutPushoutMap→PushoutABot n x north = refl
  PushoutPushoutMap→PushoutABot n x south =
    (λ i → inr (comm g (suc n) (invEq (e B n) (inr x)) i))
    ∙∙ sym (push (invEq (e B n) (inr x)))
    ∙∙ (λ i → inl (comm f (suc n) (invEq (e B n) (inr x)) (~ i)))
  PushoutPushoutMap→PushoutABot n x (merid a i) j = PushoutPushoutMap→PushoutABotFill n x a j i

  PushoutPushoutMap→PushoutA : (n : ℕ) → (Pushout (pushoutMapₛ n) fst) → (pushoutA (suc (suc n)))
  PushoutPushoutMap→PushoutA n (inl x) = pushoutA↑ n x
  PushoutPushoutMap→PushoutA n (inr (inl (inl x))) = inl (invEq (e C (suc n)) (inr x))
  PushoutPushoutMap→PushoutA n (inr (inl (inr x))) = inr (invEq (e D (suc n)) (inr x))
  PushoutPushoutMap→PushoutA n (inr (inr x)) = inl (CW↪ C (suc n) ((∣ f ∣ (suc n) (invEq (e B n) (inr x))))) --  
  PushoutPushoutMap→PushoutA n (push (inl (inl x) , b) i) =
    inl (invEq (e C (suc n)) ((push (x , (Iso.inv (IsoSphereSusp n) b))) i))
  PushoutPushoutMap→PushoutA n (push (inl (inr x) , b) i) =
    inr (invEq (e D (suc n)) ((push (x , (Iso.inv (IsoSphereSusp n) b))) i))
  PushoutPushoutMap→PushoutA n (push (inr x , b) i) =
    PushoutPushoutMap→PushoutABot n x b i




{-
  PushoutA→PushoutPushoutMapL : (n : ℕ) → Pushout (α C (suc n)) fst → Pushout (pushoutMapₛ n) fst
  PushoutA→PushoutPushoutMapL n (inl x) = inl (inl x)
  PushoutA→PushoutPushoutMapL n (inr x) = inr ((inl (inl x)))
  PushoutA→PushoutPushoutMapL n (push a i) =
    ((λ i → inl (inl (α C (suc n) (fst a , Iso.leftInv (IsoSphereSusp n) (snd a) (~ i)))))
    ∙ push (((inl (inl (fst a)))) , Iso.fun (IsoSphereSusp n) (snd a))) i

  PushoutA→PushoutPushoutMapR : (n : ℕ) → Pushout (α D (suc n)) fst → Pushout (pushoutMapₛ n) fst
  PushoutA→PushoutPushoutMapR n (inl x) = inl (inr x)
  PushoutA→PushoutPushoutMapR n (inr x) = inr ((inl (inr x)))
  PushoutA→PushoutPushoutMapR n (push a i) =
    ((λ i → inl (inr (α D (suc n) (fst a , Iso.leftInv (IsoSphereSusp n) (snd a) (~ i)))))
    ∙ push (((inl (inr (fst a)))) , Iso.fun (IsoSphereSusp n) (snd a))) i

-}


module _ {ℓ ℓ' ℓ'' : Level} {B' : CWskel ℓ} {C' : CWskel ℓ'} {D' : CWskel ℓ''}
  (f : cellMap (strictCWskel B') (strictCWskel C'))
  (g : cellMap (strictCWskel B') (strictCWskel D')) where
  private
    B = strictCWskel B'
    C = strictCWskel C'
    D = strictCWskel D'

  open CWskel-fields
  open SequenceMap renaming (map to ∣_∣)
  
  PushoutA→PushoutPushoutMapStrict : (n : ℕ)
    → (pushoutA f g (suc (suc n))) → (Pushout (pushoutMapₛ f g n) fst)
  PushoutA→PushoutPushoutMapStrict n (inl x) =
    PushoutA→PushoutPushoutMapL f g n (fst (e C (suc n)) x)
  PushoutA→PushoutPushoutMapStrict n (inr x) =
    PushoutA→PushoutPushoutMapR f g n (fst (e D (suc n)) x)
  PushoutA→PushoutPushoutMapStrict n (push a i) =
      (cong (PushoutA→PushoutPushoutMapL f g n)
        (cong (fst (e C (suc n))) (sym (comm f (suc n) a)))
    ∙∙ PushoutA→PushoutPushoutMapLR f g n (fst (e B n) a)
    ∙∙ cong (PushoutA→PushoutPushoutMapR f g n)
        (sym (cong (fst (e D (suc n))) (sym (comm g (suc n) a))))) i

  PushoutA→PushoutPushoutMapStrict≡ : (n : ℕ) (x : _)
    → PushoutA→PushoutPushoutMapStrict n x ≡ PushoutA→PushoutPushoutMap f g n x
  PushoutA→PushoutPushoutMapStrict≡ n (inl x) = refl
  PushoutA→PushoutPushoutMapStrict≡ n (inr x) = refl
  PushoutA→PushoutPushoutMapStrict≡ n (push a i) j =
    (cong (PushoutA→PushoutPushoutMapL f g n)
          (rUnit (cong (fst (e C (suc n))) (sym (comm f (suc n) a))) j)
    ∙∙ rUnit (PushoutA→PushoutPushoutMapLR f g n (fst (e B n) a)) j
    ∙∙ cong (PushoutA→PushoutPushoutMapR f g n)
        (sym (rUnit ((cong (fst (e D (suc n))) (sym (comm g (suc n) a)))) j))) i

{-

  mapBack : (n : ℕ) → Pushout (pushoutMapₛ f g n) fst → pushoutA f g (suc (suc n))
  mapBack n (inl (inl x)) = inl (inl x)
  mapBack n (inl (inr x)) = inr (inl x)
  mapBack n (inl (push a i)) = ((λ i → inl (comm f (suc n) (inl a) i)) ∙∙ push (inl a) ∙∙ λ i → inr (comm g (suc n) (inl a) (~ i))) i
  mapBack n (inr (inl (inl x))) = inl (inr x)
  mapBack n (inr (inl (inr x))) = inr (inr x)
  mapBack n (inr (inr x)) = inl (inl (∣ f ∣ (suc n) (inr x)))
  mapBack n (push (inl (inl x) , t) i) = inl ((push (x , Iso.inv (IsoSphereSusp n) t )) i)
  mapBack n (push (inl (inr x) , t) i) = inr ((push (x , Iso.inv (IsoSphereSusp n) t )) i)
  mapBack n (push (inr x , north) i) = inl (inl (∣ f ∣ (suc n) (inr x)))
  mapBack n (push (inr x , south) i) =
    ((λ i → inr (comm g (suc n) (inr x) i))
    ∙∙ sym (push (inr x))
    ∙∙ λ i → inl (comm f (suc n) (inr x) (~ i))) i
  mapBack n (push (inr x , merid a i) j) = {!!}
-}

sphereBouquetIso : (n : ℕ) {a b c : ℕ}
  → Iso (SphereBouquet n (Fin (a + b + c))) (SphereBouquet n ((Fin a ⊎ Fin b) ⊎ Fin c))
Iso.fun (sphereBouquetIso n) (inl x) = inl x
Iso.fun (sphereBouquetIso n) (inr (x , y)) = inr ((fst (finSplit3≃ _ _ _) x) , y)
Iso.fun (sphereBouquetIso n) (push a i) = push (fst (finSplit3≃ _ _ _) a) i
Iso.inv (sphereBouquetIso n) (inl x) = inl x
Iso.inv (sphereBouquetIso n) (inr (x , y)) = inr ((invEq (finSplit3≃ _ _ _) x) , y)
Iso.inv (sphereBouquetIso n) (push a i) = push (invEq (finSplit3≃ _ _ _) a) i
Iso.rightInv (sphereBouquetIso n) (inl x) = refl
Iso.rightInv (sphereBouquetIso n) (inr (x , y)) i = inr ((secEq (finSplit3≃ _ _ _) x i) , y)
Iso.rightInv (sphereBouquetIso n) (push a i) j = push (secEq (finSplit3≃ _ _ _) a j) i
Iso.leftInv (sphereBouquetIso n) (inl x) = refl
Iso.leftInv (sphereBouquetIso n) (inr (x , y)) i = inr ((retEq (finSplit3≃ _ _ _) x i) , y)
Iso.leftInv (sphereBouquetIso n) (push a i) j = push (retEq (finSplit3≃ _ _ _) a j) i

SplitBouquet : (n : ℕ) (a b c : ℕ) → Type ℓ-zero
SplitBouquet n a b c = (SphereBouquet∙ n (Fin a) ⋁∙ₗ SphereBouquet∙ n (Fin b))
                                          ⋁ SphereBouquet∙ n (Fin c)

module _ (n : ℕ) {a b c : ℕ} where
  sumSphereBouquet→SplitBouquet : (SphereBouquet n ((Fin a ⊎ Fin b) ⊎ Fin c))
     → SplitBouquet n a b c
  sumSphereBouquet→SplitBouquet (inl x) = inl (inl (inl x))
  sumSphereBouquet→SplitBouquet (inr (inl (inl x) , y)) = inl (inl (inr (x , y)))
  sumSphereBouquet→SplitBouquet (inr (inl (inr x) , y)) = inl (inr (inr (x , y)))
  sumSphereBouquet→SplitBouquet (inr (inr x , y)) = inr (inr (x , y))
  sumSphereBouquet→SplitBouquet (push (inl (inl x)) i) = inl (inl (push x i))
  sumSphereBouquet→SplitBouquet (push (inl (inr x)) i) =
    inl (((λ i → push tt i) ∙ λ i → (inr (push x i))) i)
  sumSphereBouquet→SplitBouquet (push (inr x) i) = (push tt ∙ λ i → inr (push x i)) i

  SplitBouquet→sumSphereBouquet : SplitBouquet n a b c
    → SphereBouquet n ((Fin a ⊎ Fin b) ⊎ Fin c)
  SplitBouquet→sumSphereBouquet (inl (inl (inl x))) = inl x
  SplitBouquet→sumSphereBouquet (inl (inl (inr (x , y)))) = inr ((inl (inl x)) , y)
  SplitBouquet→sumSphereBouquet (inl (inl (push a i))) = push (inl (inl a)) i
  SplitBouquet→sumSphereBouquet (inl (inr (inl x))) = inl x
  SplitBouquet→sumSphereBouquet (inl (inr (inr (x , y)))) = inr ((inl (inr x)) , y)
  SplitBouquet→sumSphereBouquet (inl (inr (push a i))) = push (inl (inr a)) i
  SplitBouquet→sumSphereBouquet (inl (push a i)) = inl tt
  SplitBouquet→sumSphereBouquet (inr (inl x)) = inl x
  SplitBouquet→sumSphereBouquet (inr (inr (x , y))) = inr (inr x , y)
  SplitBouquet→sumSphereBouquet (inr (push a i)) = push (inr a) i
  SplitBouquet→sumSphereBouquet (push a i) = inl tt

  Iso-sumSphereBouquet-SplitBouquet : Iso (SphereBouquet n ((Fin a ⊎ Fin b) ⊎ Fin c))
                                          (SplitBouquet n a b c)
  Iso.fun Iso-sumSphereBouquet-SplitBouquet = sumSphereBouquet→SplitBouquet
  Iso.inv Iso-sumSphereBouquet-SplitBouquet = SplitBouquet→sumSphereBouquet
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inl (inl x))) = refl
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inl (inr x))) = refl
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inl (push a i))) = refl
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inr (inl x))) i = inl (push tt i)
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inr (inr x))) = refl
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (inr (push a i))) j =
    inl (compPath-filler' (push tt) (λ i → inr (push a i)) (~ j) i)
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inl (push a i)) j = inl (push tt (i ∧ j))
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inr (inl x)) = push tt
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inr (inr x)) = refl
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (inr (push a i)) j =
    compPath-filler' (push tt) (λ i → inr (push a i)) (~ j) i
  Iso.rightInv Iso-sumSphereBouquet-SplitBouquet (push a i) j = push tt (i ∧ j)
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inl x) = refl
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inr (inl (inl x) , y)) = refl
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inr (inl (inr x) , y)) = refl
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (inr (inr x , y)) = refl
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (push (inl (inl x)) i) = refl
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (push (inl (inr x)) i) j =
    SplitBouquet→sumSphereBouquet (inl (lUnit (λ i → inr (push x i)) (~ j) i))
  Iso.leftInv Iso-sumSphereBouquet-SplitBouquet (push (inr x) i) j =
    SplitBouquet→sumSphereBouquet (compPath-filler' (push tt) (λ i → inr (push x i)) (~ j) i)


open import Cubical.Data.Nat.Order.Inductive
Pushout→Bouquet-pre∂ : ∀ {ℓ} (B : CWskel ℓ) (n : ℕ)
  → Fin (CWskel-fields.card B (suc n)) × S₊ n
  → SphereBouquet n (Fin (CWskel-fields.card B n))
Pushout→Bouquet-pre∂ B n x =
  (Pushout→Bouquet n (CWskel-fields.card B n)
        (CWskel-fields.α B n) (CWskel-fields.e B n)
          (fst (CWskel-fields.e B n) (CWskel-fields.α B (suc n) x)))

-- module _ where
--   open FinSequenceMap renaming (fmap to ∣_∣)
--   open CWskel-fields
--   preFunctImproved : ∀ {ℓ ℓ'} {C : CWskel ℓ} {D : CWskel ℓ'}
--     (m : ℕ) (f : finCellMap m C D) (n' : Fin m)
--     → SphereBouquet (fst n')
--         (Fin (CWskel-fields.card C (fst n')))
--     → SphereBouquet (fst n')
--         (Fin (CWskel-fields.card D (fst n')))
--   preFunctImproved m f n' (inl x) = inl tt
--   preFunctImproved {C = C} {D} (suc n) f (zero , p) (inr (x , w)) =
--     inr ((fst (CW₁-discrete D) (∣ f ∣ fone (invEq (e C 0) (inr x)))) , w)
--   preFunctImproved n f (suc zero , p) (inr (x , base)) = inl tt
--   preFunctImproved {C = C} {D = D} (suc (suc n)) f (suc zero , p) (inr (x , loop i)) =
--      (cong G (push (∣ f ∣ (1 , p) (α C 1 (x , false)))
--            ∙ (λ i → inr (fcomm f (1 , p) (α C 1 (x , false)) i)))
--     ∙∙ cong (G ∘ inr ∘ ∣ f ∣ (fsuc (1 , tt)) ∘ invEq (e C 1)) (push (x , false))
--       ∙ cong (G ∘ inr ∘ ∣ f ∣ (fsuc (1 , tt)) ∘ invEq (e C 1)) (sym (push (x , true)))
--     ∙∙ sym (cong G (push (∣ f ∣ (1 , p) (α C 1 (x , true)))
--            ∙ (λ i → inr (fcomm f (1 , p) (α C 1 (x , true)) i))))) i
--     where
--     G = BouquetFuns.CTB 1 (D .snd .fst 1) (D .snd .snd .fst 1)
--           (D .snd .snd .snd .snd 1)
--   preFunctImproved n f (suc (suc s) , p) (inr (x , north)) = inl tt
--   preFunctImproved n f (suc (suc s) , p) (inr (x , south)) = inl tt
--   preFunctImproved {C = C} {D = D} (suc n') f (suc (suc n) , p) (inr (x , merid a i)) =
--     (cong G ((push (∣ f ∣ (suc (suc n) , <ᵗ-trans-suc p) (α C (suc (suc n)) (x , a)))
--             ∙ λ i → inr (fcomm f (suc (suc n) , p) (α C (suc (suc n)) (x , a)) i)))
--     ∙ cong G (λ j → inr (∣ f ∣ (fsuc (suc (suc n) , p))
--                       (invEq (e C (suc (suc n))) (push (x , a) j))))
--     ∙ {!!}) i
--     where
--     G = BouquetFuns.CTB (suc (suc n)) (D .snd .fst (suc (suc n))) (D .snd .snd .fst (suc (suc n)))
--           (D .snd .snd .snd .snd (suc (suc n)))
--   preFunctImproved {C = C} {D = D} (suc m) f (zero , p) (push a i) =
--     push (fst (CW₁-discrete D) (∣ f ∣ fone (invEq (e C 0) (inr a)))) i
--   preFunctImproved m f (suc zero , p) (push a i) = inl tt
--   preFunctImproved m f (suc (suc s) , p) (push a i) = inl tt

pre∂Improved : ∀ {ℓ} (B : CWskel ℓ) (n : ℕ)
      → SphereBouquet (suc n) (Fin (preboundary.An+1 (strictCWskel B) n))
      → SphereBouquet (suc n) (Fin (preboundary.An (strictCWskel B) n))
pre∂Improved B n (inl x) = inl tt
pre∂Improved B zero (inr (x , base)) = inl tt
pre∂Improved B zero (inr (x , loop i)) =
  (cong (Iso.fun sphereBouquetSuspIso₀)
    (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B zero)) (λ _ → S₊∙ zero)
      (Pushout→Bouquet-pre∂ B zero (x , false)))
  ∙ sym (cong (Iso.fun sphereBouquetSuspIso₀)
    (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B zero)) (λ _ → S₊∙ zero)
      (Pushout→Bouquet-pre∂ B zero (x , true))))) i
pre∂Improved B (suc n) (inr (x , north)) = inl tt
pre∂Improved B (suc n) (inr (x , south)) = inl tt
pre∂Improved B (suc n) (inr (x , merid a i)) =
    Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n))) (λ _ → S₊∙ (suc n))
      (Pushout→Bouquet-pre∂ B (suc n) (x , a)) i
pre∂Improved B zero (push a i) = inl tt
pre∂Improved B (suc n) (push a i) = inl tt

pre∂Improved≡ : ∀ {ℓ} (B : CWskel ℓ) (n : ℕ)
  (x : SphereBouquet (suc n) (Fin (preboundary.An+1 B n)))
  → preboundary.pre∂ B n x ≡ pre∂Improved B n x
pre∂Improved≡ B zero (inl x) = refl
pre∂Improved≡ B (suc n) (inl x) = refl
pre∂Improved≡ B zero (inr (x , base)) = refl
pre∂Improved≡ B zero (inr (x , loop i)) j =
  hcomp (λ k →
    λ {(i = i0) → Iso.fun sphereBouquetSuspIso₀ (w (push (preboundary.αn+1 B 0 (x , false)) (~ k ∧ ~ j)))
     ; (i = i1) → Iso.fun sphereBouquetSuspIso₀ (w (push (preboundary.αn+1 B 0 (x , true)) (~ k)))
     ; (j = i0) → Iso.fun sphereBouquetSuspIso₀
                   (w (doubleCompPath-filler
                     (push (preboundary.αn+1 B 0 (x , false)))
                     (λ i → inr (invEq (CWskel-fields.e B (suc zero))
                       ((push (x , false) ∙ sym (push (x , true))) i)))
                     (sym (push (preboundary.αn+1 B 0 (x , true)))) k i))})
        (Iso.fun sphereBouquetSuspIso₀ (w (push (preboundary.αn+1 B 0 (x , false)) (~ j ∨ i))))
  where
  w = (SuspBouquet→Bouquet (Fin (preboundary.An B 0)) (λ _ → S₊∙ zero))
       ∘ (suspFun (preboundary.isoCofBouquet B 0))
       ∘  (suspFun (to 0 cofibCW B))
       ∘ (δ-pre (CW↪ B 1))

pre∂Improved≡ B (suc n) (inr (x , north)) = refl
pre∂Improved≡ B (suc n) (inr (x , south)) =
   (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
      (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , ptSn (suc n))))
pre∂Improved≡ B (suc n) (inr (x , merid a i)) j = h j i
  where
  open preboundary B (suc n)
  h : Square (λ i → preboundary.pre∂ B (suc n) (inr (x , merid a i)))
             (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
                (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , a)))
             refl ((Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
      (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , ptSn (suc n)))))
  h = cong-∙∙ (SuspBouquet→Bouquet (Fin An) (λ _ → S₊∙ (suc n))
            ∘ suspFun isoCofBouquet
            ∘ suspFun (to suc n cofibCW B)
            ∘ δ-pre (CW↪ B (suc (suc n))))
            (push (αn+1 (x , a))) _ (sym (push (αn+1 (x , ptSn (suc n)))))
    ∙ doubleCompPath≡compPath _ _ _ -- 
    ∙ cong₂ _∙_ refl ((sym (lUnit _))) -- cong₂ _∙_ refl (sym (lUnit _)) ∙ refl
    ◁ symP (compPath-filler (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
                         (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , a)))
                        (sym (Bouquet→ΩBouquetSusp (Fin (CWskel-fields.card B (suc n)))
                         (λ _ → S₊∙ (suc n)) (Pushout→Bouquet-pre∂ B (suc n) (x , ptSn (suc n))))))
pre∂Improved≡ B zero (push a i) = refl
pre∂Improved≡ B (suc n) (push a i) = refl

module MOOO (isEquivPushoutA→PushoutPushoutMapStrict : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
  (f : cellMap B C)
  (g : cellMap B D)
   → (n : ℕ) → retract (PushoutPushoutMap→PushoutA f g n) (PushoutA→PushoutPushoutMap f g n)
               × section (PushoutPushoutMap→PushoutA f g n) (PushoutA→PushoutPushoutMap f g n))
   where
  eCWPushout : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
     (f : cellMap B C) (g : cellMap B D) (n : ℕ)
     → pushoutA f g (suc (suc n)) ≃ Pushout (pushoutMapₛ f g n) (λ r → fst r)
  eCWPushout f g n = isoToEquiv theIso
    where
    theIso : Iso _ _
    Iso.fun theIso = PushoutA→PushoutPushoutMap f g n
    Iso.inv theIso = PushoutPushoutMap→PushoutA f g n
    Iso.rightInv theIso = isEquivPushoutA→PushoutPushoutMapStrict f g n .fst
    Iso.leftInv theIso = isEquivPushoutA→PushoutPushoutMapStrict f g n .snd

  PushoutCWSkel : ∀ {ℓ ℓ' ℓ''} {B : CWskel ℓ} {C : CWskel ℓ'} {D : CWskel ℓ''}
    (f : cellMap B C) (g : cellMap B D) → CWskel _
  fst (PushoutCWSkel f g) = pushoutA f g
  fst (snd (PushoutCWSkel f g)) = pushoutCells f g
  fst (snd (snd (PushoutCWSkel f g))) = pushoutMap f g
  fst (snd (snd (snd ((PushoutCWSkel {B = B}) f g)))) (lift t) =
    fst (snd (snd (snd B))) t
  snd (snd (snd (snd (PushoutCWSkel {B = B} {C = C} {D} f g)))) zero =
    compEquiv (compEquiv (symPushout _ _)
      (compEquiv (invEquiv (pushoutEquiv _ _ _ _
        (propBiimpl→Equiv (λ())
          (λ x → ⊥.rec (fst (snd (snd (snd B))) x)) (λ()) (fst (snd (snd (snd B)))))
        (idEquiv _) (idEquiv _) (funExt λ()) (funExt λ())))
        (compEquiv (invEquiv (isoToEquiv Pushout-⊎-Iso))
        (compEquiv
          (compEquiv (invEquiv ⊎-IdR-⊥-≃)
            (isoToEquiv (⊎Iso (compIso (compIso
              (⊎Iso (equivToIso (CW₁-discrete D))
                (equivToIso (CW₁-discrete C))) ⊎-swap-Iso)
                  (Iso-Fin⊎Fin-Fin+))
                    (iso (λ()) (λ()) (λ()) λ()))))
          (isoToEquiv (Iso-Fin⊎Fin-Fin+ {m = zero}))))))
      (compEquiv (isoToEquiv (PushoutEmptyFam (λ())
        λ {(lift t) → fst (snd (snd (snd B))) t}))
        (symPushout _ _))
  snd (snd (snd (snd (PushoutCWSkel f g)))) (suc n) =
    compEquiv (eCWPushout f g n)
              (isoToEquiv (Iso-Pushoutα-PushoutPushoutMapₛ  f g n))


  open import Cubical.Data.Unit
  UnitCWskel : CWskel ℓ-zero
  fst UnitCWskel zero = ⊥
  fst UnitCWskel (suc n) = Unit
  fst (snd UnitCWskel) zero = 1
  fst (snd UnitCWskel) (suc n) = 0
  fst (snd (snd UnitCWskel)) zero ()
  fst (snd (snd UnitCWskel)) (suc n) t = tt
  fst (snd (snd (snd UnitCWskel))) ()
  snd (snd (snd (snd UnitCWskel))) zero =
    compEquiv (isoToEquiv Iso-Unit-Fin1)
      (compEquiv (isoToEquiv (PushoutEmptyFam (λ()) λ())) (symPushout _ _))
  snd (snd (snd (snd UnitCWskel))) (suc n) =
    isoToEquiv (PushoutEmptyFam (λ()) λ())


  terminalCW : ∀ {ℓ} {C : CWskel ℓ} → cellMap C UnitCWskel
  SequenceMap.map (terminalCW {C = C}) zero = fst (snd (snd (snd C)))
  SequenceMap.map terminalCW (suc n) _ = tt
  SequenceMap.comm terminalCW _ _ = refl


  module MIAU {ℓ ℓ'' : Level} {B' : CWskel ℓ} {D' : CWskel ℓ''}
    (f : cellMap (strictCWskel B') (strictCWskel D')) where
    private
      B = strictCWskel B'
      D = strictCWskel D'
      C = UnitCWskel

    open CWskel-fields
    open SequenceMap renaming (map to ∣_∣)
    open import Cubical.HITs.Wedge
    open import Cubical.Foundations.Pointed

    cofibCWskel : CWskel _
    cofibCWskel = PushoutCWSkel terminalCW f


    PushoutA→PushoutPushoutMap' : (n : ℕ) → pushoutA terminalCW f (suc (suc n))
                       → Pushout (pushoutMapₛ terminalCW f n) (λ r → fst r)
    PushoutA→PushoutPushoutMap' n (inl x) = inl (inl x)
    PushoutA→PushoutPushoutMap' n (inr x) =
      PushoutA→PushoutPushoutMapR terminalCW f n x
    PushoutA→PushoutPushoutMap' n (push a i) =
      (PushoutA→PushoutPushoutMapLR terminalCW f n a
     ∙ cong (PushoutA→PushoutPushoutMapR terminalCW f n) (comm f (suc n) a)) i

    PushoutA→PushoutPushoutMap'≡ : (n : ℕ) (x : _)
      → PushoutA→PushoutPushoutMap terminalCW f n x ≡ PushoutA→PushoutPushoutMap' n x
    PushoutA→PushoutPushoutMap'≡ n (inl x) = refl
    PushoutA→PushoutPushoutMap'≡ n (inr x) = refl
    PushoutA→PushoutPushoutMap'≡ n (push a i) k = help k i
      where
      help : cong (PushoutA→PushoutPushoutMap terminalCW f n) (push a) ≡ cong (PushoutA→PushoutPushoutMap' n) (push a)
      help = cong₃ _∙∙_∙∙_
        (cong (cong (PushoutA→PushoutPushoutMapL terminalCW f n)) (sym (rUnit refl)))
        (sym (rUnit _))
        ((cong (sym ∘ cong (PushoutA→PushoutPushoutMapR terminalCW f n)) (sym (rUnit _))))

    module _ (n : ℕ) where
      F1 = preboundarypre∂Simpl cofibCWskel n
      F2↓ = preboundarypre∂Simpl cofibCWskel n

      F2 = suspFun (preboundarypre∂Simpl cofibCWskel n)
      F3 = suspFun (to n cofibCW cofibCWskel)
      F4 = δ (suc n) cofibCWskel
      F5 = preboundary.isoCofBouquetInv↑ cofibCWskel n

    -- SphereBouquetCellIso : (n m : ℕ) → Iso (SphereBouquet (suc n) (Fin (card cofibCWskel m)))
    --                                          (SplitBouquet n (card C m) (card D m) (pushoutMidCells terminalCW f m))
    -- SphereBouquetCellIso n m = compIso (sphereBouquetIso (suc n)) (Iso-sumSphereBouquet-SplitBouquet n) --  -- 

    -- sphereBouquetSuspIso∙ : ∀ {ℓ} {A : Type ℓ} {n : ℕ} → Iso.fun (sphereBouquetSuspIso {A = A} {n}) north ≡ inl tt
    -- sphereBouquetSuspIso∙ {n = zero} = refl
    -- sphereBouquetSuspIso∙ {n = suc n} = refl

    -- QuotCW : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Type ℓ 
    -- QuotCW C n = cofib (CW↪ C n)

    -- QuotCW∙ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → Pointed ℓ 
    -- QuotCW∙ C n = QuotCW C n , inl tt

    -- bouquetFun1 : (n : ℕ) → SphereBouquet n (Fin (card cofibCWskel n)) → QuotCW cofibCWskel n
    -- bouquetFun1 n = BouquetFuns.BTC n (card cofibCWskel n) (α cofibCWskel n) (e cofibCWskel n)

    -- SphereBouquetCellEquiv : (n m : ℕ)
    --   → SphereBouquet n (Fin (card cofibCWskel m)) ≃ (SplitBouquet n (card C m) (card D m) (pushoutMidCells terminalCW f m))
    -- SphereBouquetCellEquiv n m = isoToEquiv (compIso (sphereBouquetIso n) (Iso-sumSphereBouquet-SplitBouquet n))

    -- bouquetFun1' : (n : ℕ) → SplitBouquet n (card C n) (card D n) (pushoutMidCells terminalCW f n)
    --                         → QuotCW cofibCWskel n
    -- bouquetFun1' n = bouquetFun1 n ∘ invEq (SphereBouquetCellEquiv n n)

    -- bouquetFun'-inl : (n : ℕ) → (SphereBouquet∙ (suc n) (Fin zero) ⋁ SphereBouquet∙ (suc n) (Fin (card D (suc n))))
    --                            → (QuotCW D (suc n))
    -- bouquetFun'-inl n (inl x) = {!!}
    -- bouquetFun'-inl n (inr x) = {!!}
    -- bouquetFun'-inl n (push a i) = {!!}

    -- bouquetFun' : (n : ℕ) → SplitBouquet (suc n) zero (card D (suc n)) (pushoutMidCells terminalCW f (suc n))
    --                         → (QuotCW∙ D (suc n)) ⋁ Susp∙ (QuotCW B n)
    -- bouquetFun' n (inl x) = inl (bouquetFun'-inl n x)
    -- bouquetFun' n (inr x) = {!!}
    -- bouquetFun' n (push a i) = {!!}

    -- SphereBouquetSplit : (n : ℕ) → Type
    -- SphereBouquetSplit n = SphereBouquet (suc (suc n)) (Fin (card D (suc (suc n))) ⊎ Fin (card B (suc n)))

    -- cofibskel' : (n : ℕ) → Type _
    -- cofibskel' n = Pushout (pushoutMapₛ terminalCW f n) fst

    -- Iso-cofibskel' : (n : ℕ) → (fst cofibCWskel (suc (suc n))) ≃ (cofibskel' n)
    -- Iso-cofibskel' = eCWPushout terminalCW f

    -- cofibskel'↑ : (n : ℕ) → cofibskel' n → cofibskel' (suc n)
    -- cofibskel'↑ n x = inl (invEq (Iso-cofibskel' n) x)

    -- cofibskelQuot : (n : ℕ) → Type _
    -- cofibskelQuot n = cofib {A = cofibskel' n} {B = cofibskel' (suc n)} (cofibskel'↑ n)

    -- -- bouquetFun2Inr : (n : ℕ) (x : Fin (card D (suc (suc n))) ⊎ Fin (card B (suc n))) → S₊ (suc (suc n)) → cofibskel' (suc n)
    -- -- bouquetFun2Inr n x north = inl {!!}
    -- -- bouquetFun2Inr n x south = {!!}
    -- -- bouquetFun2Inr n x (merid a i) = {!!}

    -- -- bouquetFun2 : (n : ℕ) → SplitBouquet n zero (card D (suc (suc n))) (pushoutMidCells terminalCW f (suc (suc n)))
    -- --                         → cofibskelQuot n
    -- -- bouquetFun2 n (inl x) = {!!}
    -- -- bouquetFun2 n (inr x) = {!x!}
    -- -- bouquetFun2 n (push a i) = {!!}

    -- cofibskelQuot≃ : (n : ℕ) → cofibskelQuot n ≃ QuotCW cofibCWskel (suc (suc n))
    -- cofibskelQuot≃ n =
    --   pushoutEquiv _ _ _ _
    --   (invEquiv (Iso-cofibskel' n)) (idEquiv _) (invEquiv (Iso-cofibskel' (suc n)))
    --   (λ _ _ → tt) (funExt λ x → refl)

    -- cofib→wedgeInr : (n : ℕ) → cofibskel' (suc n) → (QuotCW∙ D (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc n))
    -- cofib→wedgeInr n (inl x) = inl (inl tt)
    -- cofib→wedgeInr n (inr (inl (inr x))) = inl (inr (inr x))
    -- cofib→wedgeInr n (inr (inr x)) = inr north
    -- cofib→wedgeInr n (push (inl (inr x) , b) i) =
    --   ((λ i → inl (push (α D (suc (suc n)) (x , Iso.inv (IsoSphereSusp (suc n)) b)) i)) ∙ (λ i → inl (inr (push (x , Iso.inv (IsoSphereSusp (suc n)) b) i)))) i
    -- cofib→wedgeInr n (push (inr x , b) i) = (push tt ∙ λ i → inr (toSusp (_ , inl tt) (haha b x) i)) i
    --   where
    --   haha : (x : Susp (S₊ n)) (y : A B (suc n)) → QuotCW B (suc n)
    --   haha north y = inl tt
    --   haha south y = inr (inr y)
    --   haha (merid a i) y =
    --     (push (α B (suc n) (y , a)) ∙ λ i → inr ((push (y , a)) i)) i

    -- cofib→wedge : (n : ℕ) → cofibskelQuot n → (QuotCW∙ D (suc (suc n))) ⋁ Susp∙ (QuotCW B (suc n))
    -- cofib→wedge n (inl x) = inl (inl tt)
    -- cofib→wedge n (inr x) = cofib→wedgeInr n x
    -- cofib→wedge n (push a i) = inl (inl tt)

    


    
