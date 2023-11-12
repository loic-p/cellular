{-# OPTIONS --cubical --allow-unsolved-metas --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base

open import prelude
open import cw-complex
open import choice

module cw-approx where

open Sequence

-- The embedding of stage n into stage n+1 is (n+1)-connected
-- 2 calls to univalence in there
isConnected-CW↪ : (n : ℕ) (C : CW) → isConnectedFun n (CW↪ C n)
isConnected-CW↪ zero C x = isContrUnit*
isConnected-CW↪ (suc n) C = EquivJ (λ X E → isConnectedFun (suc n) (λ x → invEq E (inl x)))
                             inPushoutConnected (e₊ (suc n))
  where
    A = snd C .fst
    α = snd C .snd .fst
    e₊ = snd C .snd .snd .snd

    inPushout : fst C (suc n) → Pushout (α (suc n)) fst
    inPushout x = inl x

    fstProjPath : (b : Fin (A (suc n))) → S₊ n ≡ fiber fst b
    fstProjPath b = ua (fiberProjEquiv (Fin (A (suc n))) (λ _ → S₊ n) b)

    inPushoutConnected : isConnectedFun (suc n) inPushout
    inPushoutConnected = inlConnected (suc n) (α (suc n)) fst
      λ b → subst (isConnected (suc n)) (fstProjPath b) (sphereConnected n)

-- The embedding of stage n into the colimit is (n+1)-connected
isConnected-CW↪∞ : (n : ℕ) (C : CW) → isConnectedFun n (CW↪∞ C n)
isConnected-CW↪∞ zero C b = isContrUnit*
isConnected-CW↪∞ (suc n) C = isConnectedIncl∞ (realiseSeq C) (suc n) (suc n) subtr
  where
    subtr : (k : ℕ) → isConnectedFun (suc n) (CW↪ C (k +ℕ (suc n)))
    subtr k = isConnectedFunSubtr (suc n) k (CW↪ C (k +ℕ (suc n)))
                                   (isConnected-CW↪ (k +ℕ (suc n)) C)

-- We can merely fill n-spheres in (n+2)-connected spaces
module connectedSpace {A : Type} where
  contractSphere : (n : ℕ) (HA : isConnected (suc (suc n)) A)
    → (f : S₊ n → A)
    →  ∃[ a ∈ A ] ((s : S₊ n) → f s ≡ a)
  contractSphere zero HA f =
    TR.rec squash₁
      (λ p → ∣ (f true) , (λ { false → sym p ; true → refl}) ∣₁)
      (Iso.fun (PathIdTruncIso _) (isContr→isProp HA ∣ f true ∣ₕ ∣ f false ∣ₕ))
  contractSphere (suc n) HA f =
    PT.map (λ p → (f (ptSn (suc n))) , funExt⁻ p) main-path
    where
    A⋆ : Pointed₀
    A⋆ = A , f (ptSn (suc n))

    π-iso : Iso (π' (suc n) A⋆) (π' (suc n) (Unit , tt))
    π-iso =
       compIso (fst (π'Gr≅πGr n A⋆))
      (compIso (πTruncIso (suc n))
      (compIso (invIso (fst (π'Gr≅πGr n (hLevelTrunc∙ (3 +ℕ n) A⋆))))
               (equivToIso (π'Iso n (isoToEquiv (isContr→Iso HA isContrUnit) , refl) .fst))))

    contr-π : isContr (π' (suc n) A⋆)
    contr-π = isOfHLevelRetractFromIso 0 π-iso
             (∣ const∙ (S₊∙ (suc n)) _ ∣₂
             , ST.elim (λ _ → isSetPathImplicit) λ f → refl)

    main-path : ∥ f ≡ (λ _ → f (ptSn (suc n))) ∥₁
    main-path =
      PT.map (cong fst)
      (Iso.fun PathIdTrunc₀Iso
                 (isContr→isProp contr-π
                   ∣ f , refl ∣₂ ∣ (λ _ → f (ptSn (suc n))) , refl ∣₂))

-- Now we are going to prove that connectedness is enough to lift a map from
-- stage n of the CW approximation to stage n+1
module connectedFunLifts {A B : Type}
  (f : A → B) (n : ℕ) (Hf : isConnectedFun (suc (suc n)) f) where

  -- contractions of spheres can be (merely) lifted along connected maps
  contractSphere : (g : S₊ n → A) (b : B)
    → (diskB : (s : S₊ n) → f (g s) ≡ b)
    → ∥ Σ[ a ∈ A ] (Σ[ Ha ∈ f a ≡ b ] (Σ[ diskA ∈ ((s : S₊ n) → g s ≡ a) ]
           ((s : S₊ n) → diskB s ≡ (cong f (diskA s) ∙ Ha)))) ∥₁
  contractSphere g b diskB = PT.map aux (connectedSpace.contractSphere n (Hf b) (λ s → (g s , diskB s)))
    where
      aux : (Σ[ a ∈ fiber f b ] ((s : S₊ n) → (g s , diskB s) ≡ a)) →
            Σ[ a ∈ A ] (Σ[ Ha ∈ f a ≡ b ] (Σ[ diskA ∈ ((s : S₊ n) → g s ≡ a) ]
              ((s : S₊ n) → diskB s ≡ (cong f (diskA s) ∙ Ha))))
      aux ((a , Ha) , c) = a , Ha , (λ s → fst (pathFiber f b (c s)))
                         , (λ s → snd (pathFiber f b (c s)))

  -- this also works for a finite amount of sphere contractions by Finite Choice
  contractSpheres : (m : ℕ) (g : Fin m → S₊ n → A)
    → (b : (k : Fin m) → B)
    → (diskB : (k : Fin m) → (s : S₊ n) → f (g k s) ≡ b k)
    → ∥ (Σ[ a ∈ (Fin m → A) ] ((k : Fin m) → Σ[ Ha ∈ f (a k) ≡ b k ]
            (Σ[ diskA ∈ ((s : S₊ n) → g k s ≡ a k) ]
            ((s : S₊ n) → diskB k s ≡ (cong f (diskA s) ∙ Ha))))) ∥₁
  contractSpheres m g b diskB = invEq (_ , satAC∃Fin m (λ _ → A)
    (λ k a → (Σ[ Ha ∈ f a ≡ b k ] (Σ[ diskA ∈ ((s : S₊ n) → g k s ≡ a) ]
      ((s : S₊ n) → diskB k s ≡ (cong f (diskA s) ∙ Ha))))))
    (λ k → contractSphere (g k) (b k) (diskB k))

  -- this allows us to lift a map out of a pushout with spheres
  module _ (X : Type) (g : X → A) (m : ℕ) (α : Fin m × S₊ n → X)
    (h : Pushout α fst → B) (comm : (x : X) → f (g x) ≡ h (inl x)) where

    module _ (spheresContr : (Σ[ a ∈ (Fin m → A) ] ((k : Fin m) → Σ[ Ha ∈ f (a k) ≡ h (inr k) ]
      (Σ[ diskA ∈ ((s : S₊ n) → g (α (k , s)) ≡ a k) ]
      ((s : S₊ n) → comm (α (k , s)) ∙ (cong h (push (k , s))) ≡ (cong f (diskA s) ∙ Ha)))))) where

      centerA : Fin m → A
      centerA = fst spheresContr

      HcenterA : (k : Fin m) → f (centerA k) ≡ h (inr k)
      HcenterA = λ k → fst (snd spheresContr k)

      diskA : (k : Fin m) → (s : S₊ n) → g (α (k , s)) ≡ centerA k
      diskA = λ k → fst (snd (snd spheresContr k))

      HdiskA : (k : Fin m) → (s : S₊ n) → comm (α (k , s)) ∙ (cong h (push (k , s))) ≡ (cong f (diskA k s) ∙' (HcenterA k))
      HdiskA = λ k s → (snd (snd (snd spheresContr k)) s) ∙ (compPath≡compPath' (cong f (diskA k s)) (HcenterA k))

      liftPushout-fun : Pushout α fst → A
      liftPushout-fun (inl x) = g x
      liftPushout-fun (inr a) = centerA a
      liftPushout-fun (push (a , s) i) = diskA a s i

      liftPushout-H1 : (x : X) → (g x ≡ liftPushout-fun (inl x))
      liftPushout-H1 x = refl

      liftPushout-H2 : (x : Pushout α fst) → f (liftPushout-fun x) ≡ h x
      liftPushout-H2 (inl x) = comm x
      liftPushout-H2 (inr a) = HcenterA a
      liftPushout-H2 (push (a , s) i) j =
        hcomp (λ k → λ { (i = i0) → compPath-filler (comm (α (a , s))) (cong h (push (a , s))) (~ k) j
                       ; (i = i1) → compPath'-filler (cong f (diskA a s)) (HcenterA a) (~ k) j
                       ; (j = i0) → f (diskA a s (i ∧ k))
                       ; (j = i1) → h (push (a , s) (i ∨ (~ k))) })
              (HdiskA a s i j)

      -- pasting the two commutativity triangles gives the commutativity of the outer square
      -- unused for now, probably useful later
      liftPushout-H12 : (x : X) → comm x ≡ (cong f (liftPushout-H1 x) ∙ liftPushout-H2 (inl x))
      liftPushout-H12 x = lUnit (comm x)

      liftPushout-aux : Σ[ lift ∈ (Pushout α fst → A) ]
        ((x : X) → g x ≡ lift (inl x)) × ((x : Pushout α fst) → f (lift x) ≡ h x)
      liftPushout-aux = liftPushout-fun , liftPushout-H1 , liftPushout-H2

    liftPushout : ∃[ lift ∈ (Pushout α fst → A) ]
      ((x : X) → g x ≡ lift (inl x)) × ((x : Pushout α fst) → f (lift x) ≡ h x)
    liftPushout = PT.map liftPushout-aux
      (contractSpheres m (λ a s → g (α (a , s)))
                         (λ k → h (inr k))
                         (λ k s → comm (α (k , s)) ∙ cong h (push (k , s))))

  -- which in turn, allows us to lift maps from a CW stage to the next one
  module _ (C : CW) (g : fst C (suc n) → A) where
    An = snd C .fst
    α = snd C .snd .fst
    e₊ = snd C .snd .snd .snd

    lifting-prop : (Y : Type) (E : Y ≃ Pushout (α (suc n)) fst) → Type
    lifting-prop Y E = (h : Y → B) (comm : (x : fst C (suc n)) → f (g x) ≡ h (invEq E (inl x)))
      → ∃[ lift ∈ (Y → A) ] ((x : fst C (suc n)) → g x ≡ lift (invEq E (inl x)))
                            × ((x : Y) → f (lift x) ≡ h x)

    liftCW : (h : fst C (suc (suc n)) → B)
      (comm : (x : fst C (suc n)) → f (g x) ≡ h (CW↪ C (suc n) x))
      → ∃[ lift ∈ (fst C (suc (suc n)) → A) ] ((x : fst C (suc n)) → g x ≡ lift (CW↪ C (suc n) x))
                                        × ((x : fst C (suc (suc n))) → f (lift x) ≡ h x)
    liftCW = EquivJ lifting-prop (liftPushout (fst C (suc n)) g (An (suc n)) (α (suc n))) (e₊ (suc n))

-- Cellular approximation
module _ (C D : CW) (f : realise C → realise D) where
  find-connected-component : (d : realise D) → ∃[ d0 ∈ fst D 1 ] incl d0 ≡ d
  find-connected-component = CW→Prop D (λ _ → squash₁) λ a → ∣ a , refl ∣₁

  find-connected-component-C₀ : (c : fst C 1) → ∃[ d0 ∈ fst D 1 ] incl d0 ≡ f (incl c)
  find-connected-component-C₀ c = find-connected-component (f (incl c))

  satAC∃Fin-C0 : ∀ {ℓ ℓ'} → satAC∃ ℓ ℓ' (fst C 1)
  satAC∃Fin-C0 {ℓ} {ℓ'} = subst (satAC∃ ℓ ℓ') (sym (ua (CW₁-discrete C))) (satAC∃Fin _)

  -- existence of f₁ : C₁ → D₁
  approx₁ : ∃[ f₁ ∈ (fst C 1 → fst D 1) ] ((c : _) → incl (f₁ c) ≡ f (incl c) )
  approx₁ =
    invEq (_ , satAC∃Fin-C0 (λ _ → fst D 1) (λ c d0 → incl d0 ≡ f (incl c)))
      find-connected-component-C₀

  approx : (n : ℕ)
    → ∃[ fₙ ∈ (fst C n → fst D n) ] ((c : _) → incl (fₙ c) ≡ f (incl c))
  approx zero = ∣ (λ x → ⊥.rec (CW₀-empty C x)) , (λ x → ⊥.rec (CW₀-empty C x)) ∣₁
  approx (suc zero) = approx₁
  approx (suc (suc n)) = PT.rec squash₁ (λ {(f' , p) → PT.rec squash₁
    (λ F → ∣ (fst F) , (snd F .snd) ∣₁)
    (connectedFunLifts.liftCW {A = fst D (suc (suc n))} {B = realise D} incl n
      (isConnected-CW↪∞ (suc (suc n)) D) C (λ x → CW↪ D (suc n) (f' x))
        (λ x → f (incl x))
        λ x → sym (push (f' x)) ∙ p x ∙ cong f (push x))})
      (approx (suc n))
