{-# OPTIONS --cubical --allow-unsolved-metas --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SequentialColimit
open import Cubical.Homotopy.Connected

open import prelude
open import cw-complex
open import choice

module cw-approx where

open Sequence

-- todo: clean up imports

realiseSeq : CW → Sequence ℓ-zero
Sequence.obj (realiseSeq (C , p)) = C
Sequence.map (realiseSeq C) = CW↪ C _

-- realisation of CW complex from skeleton
realise : CW → Type
realise C = SeqColim (realiseSeq C)

-- send the stage n to the realization (the same as incl, but with explicit args and type)
CW↪∞ : (C : CW) → (n : ℕ) → fst C n → realise C
CW↪∞ C n x = incl x

-- elimination from colimit into prop (move to lib)
Lim→Prop : ∀ {ℓ ℓ'} {C : Sequence ℓ} {B : SeqColim C → Type ℓ'}
  → ((x : _) → isProp (B x))
  → (s : (n : ℕ) (x : obj C n) → B (incl x))
  → (x : _) → B x
Lim→Prop {C = C} pr ind (incl x) = ind _ x
Lim→Prop {C = C} {B = B} pr ind (push x i) =
  isProp→PathP {B = λ i → B (push x i)}
    (λ i → pr _)
    (ind _ x) (ind (suc _) (C .Sequence.map x)) i

-- elimination from Cₙ into prop
CWskel→Prop : (C : CW) {A : (n : ℕ) → fst C n → Type}
  → ((n : ℕ) (x : _) → isProp (A n x))
  → ((a : _) → A zero a)
  → ((n : ℕ) (a : _) → (A n a → A (suc n) (CW↪ C n a)))
  → (n : _) (c : fst C n) → A n c
CWskel→Prop C {A = A} pr b eqs zero c = b c
CWskel→Prop C {A = A} pr b eqs (suc n) c =
  subst (A (suc n))
        (retEq (snd C .snd .snd .snd n) c)
        (help (CWskel→Prop C pr b eqs n) _)
  where
  help : (inder : (c₁ : fst C n) → A n c₁)
       → (a : Pushout _ fst)
       → A (suc n) (invEq (snd C .snd .snd .snd n) a)
  help inder =
    elimProp _ (λ _ → pr _ _) (λ b → eqs n _ (inder b))
     λ c → subst (A (suc n))
                  (cong (invEq (snd C .snd .snd .snd n)) (push (c , ptSn n)))
                  (eqs n _ (inder _))

-- eliminating from CW complex into prop
CW→Prop : (C : CW) {A : realise C → Type}
  → ((x : _) → isProp (A x))
  → ((a : _) → A (incl {n = zero} a))
  → (a : _) → A a
CW→Prop C {A = A} pr ind  =
  Lim→Prop pr (CWskel→Prop C (λ _ _ → pr _)
    ind
    λ n a → subst A (push a))

isSet-CW₀ : (C : CW) → isSet (fst C 0)
isSet-CW₀ C =
  isOfHLevelRetractFromIso 2 (equivToIso (snd C .snd .snd .fst))
    isSetFin

-- The embedding of stage n into stage n+1 is (n+1)-connected
-- 2 calls to univalence in there
isConnected-CW↪ : (n : ℕ) (C : CW) → isConnectedFun (suc n) (CW↪ C n)
isConnected-CW↪ n C = EquivJ (λ X E → isConnectedFun (suc n) (λ x → invEq E (inl x)))
                             inPushoutConnected (e₊ n)
  where
    A = snd C .fst
    α = snd C .snd .fst
    e₊ = snd C .snd .snd .snd

    inPushout : fst C n → Pushout (α n) fst
    inPushout x = inl x

    fstProjPath : (b : Fin (A (suc n))) → S₊ n ≡ fiber fst b
    fstProjPath b = ua (fiberProjEquiv (Fin (A (suc n))) (λ _ → S₊ n) b)

    inPushoutConnected : isConnectedFun (suc n) inPushout
    inPushoutConnected = inlConnected (suc n) (α n) fst
      (λ b → subst (isConnected (suc n)) (fstProjPath b) (sphereConnected n))

-- The embedding of stage n into the colimit is (n+1)-connected
isConnected-CW↪∞ : (n : ℕ) (C : CW) → isConnectedFun (suc n) (CW↪∞ C n)
isConnected-CW↪∞ n C = isConnectedIncl∞ (realiseSeq C) (suc n) n subtr
  where
    subtr : (k : ℕ) → isConnectedFun (suc n) (CW↪ C (k +ℕ n))
    subtr k = isConnectedFunSubtr (suc n) k (CW↪ C (k +ℕ n))
                                  (subst (λ X → isConnectedFun X (CW↪ C (k +ℕ n)))
                                         (sym (+-suc k n)) (isConnected-CW↪ (k +ℕ n) C))

-- We can merely fill n-spheres in (n+2)-connected spaces
module connectedSpace {A : Type} (n : ℕ) (HA : isConnected (suc (suc n)) A) where
  contractSphere : (f : S₊ n → A) →  ∃[ a ∈ A ] ((s : S₊ n) → f s ≡ a)
  contractSphere f = {!!}

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
  module _ (C : CW) (g : fst C n → A) where
    An = snd C .fst
    α = snd C .snd .fst
    e₊ = snd C .snd .snd .snd

    lifting-prop : (Y : Type) (E : Y ≃ Pushout (α n) fst) → Type
    lifting-prop Y E = (h : Y → B) (comm : (x : fst C n) → f (g x) ≡ h (invEq E (inl x)))
      → ∃[ lift ∈ (Y → A) ] ((x : fst C n) → g x ≡ lift (invEq E (inl x)))
                            × ((x : Y) → f (lift x) ≡ h x)

    liftCW : (h : fst C (suc n) → B)
      (comm : (x : fst C n) → f (g x) ≡ h (CW↪ C n x))
      → ∃[ lift ∈ (fst C (suc n) → A) ] ((x : fst C n) → g x ≡ lift (CW↪ C n x))
                                        × ((x : fst C (suc n)) → f (lift x) ≡ h x)
    liftCW = EquivJ lifting-prop
      (liftPushout (fst C n) g (An (suc n)) (α n)) (e₊ n)

-- Cellular approximation
module _ (C D : CW) (f : realise C → realise D) where
  find-connected-component : (d : realise D) → ∃[ d0 ∈ fst D 0 ] incl d0 ≡ d
  find-connected-component = CW→Prop D (λ _ → squash₁) λ a → ∣ a , refl ∣₁

  find-connected-component-C₀ : (c : fst C 0) → ∃[ d0 ∈ fst D 0 ] incl d0 ≡ f (incl c)
  find-connected-component-C₀ c = find-connected-component (f (incl c))

  satAC∃Fin-C0 : ∀ {ℓ ℓ'} → satAC∃ ℓ ℓ' (fst C 0)
  satAC∃Fin-C0 {ℓ} {ℓ'} = subst (satAC∃ ℓ ℓ') ( sym (ua (snd C .snd .snd .fst))) (satAC∃Fin _)

  -- existence of f₀ : C₀ → D₀
  approx₀ : ∃[ f₀ ∈ (fst C 0 → fst D 0) ] ((c : _) → incl (f₀ c) ≡ f (incl c) )
  approx₀ =
    invEq (_ , satAC∃Fin-C0 (λ _ → fst D 0) (λ c d0 → incl d0 ≡ f (incl c)))
      find-connected-component-C₀

  -- todo: higher dims...
