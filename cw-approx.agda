{-# OPTIONS --cubical --lossy-unification --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (isProp≤ ; _≤_)
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
open import cw-map
open import freeabgroup


module cw-approx where

open Sequence

-- move
sphereElim' : {ℓ : Level} (n : ℕ) {A : S₊ n → Type ℓ} →
      ((x : S₊ n) → isOfHLevel n (A x)) →
      A (ptSn n) → (x : S₊ n) → A x
sphereElim' zero st _ x = st x .fst
sphereElim' (suc n) = sphereElim n

PathPIdTruncIso : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} {b : A i1} (n : HLevel)
  → Iso (PathP (λ i → ∥ A i ∥ suc n) ∣ a ∣ ∣ b ∣) (∥ PathP (λ i → A i) a b ∥ n)
PathPIdTruncIso {A = A} n = help (A i0) (A i1) (λ i → A i) n
  where
  help : ∀ {ℓ} (A B : Type ℓ) (A' : A ≡ B) {a : A} {b : B} (n : HLevel)
       → Iso (PathP (λ i → ∥ A' i ∥ suc n) ∣ a ∣ ∣ b ∣) (∥ PathP (λ i → A' i) a b ∥ n)
  help A = J> PathIdTruncIso

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
satAC∃Fin-C0 : ∀ {ℓ ℓ'} → (C : CW) → satAC∃ ℓ ℓ' (fst C 1)
satAC∃Fin-C0 {ℓ} {ℓ'} C = subst (satAC∃ ℓ ℓ') (sym (ua (CW₁-discrete C))) (satAC∃Fin _)

module _ (C D : CW) (f : realise C → realise D) where
  find-connected-component : (d : realise D) → ∃[ d0 ∈ fst D 1 ] incl d0 ≡ d
  find-connected-component = CW→Prop D (λ _ → squash₁) λ a → ∣ a , refl ∣₁

  find-connected-component-C₀ : (c : fst C 1) → ∃[ d0 ∈ fst D 1 ] incl d0 ≡ f (incl c)
  find-connected-component-C₀ c = find-connected-component (f (incl c))

  -- existence of f₁ : C₁ → D₁
  approx₁ : ∃[ f₁ ∈ (fst C 1 → fst D 1) ] ((c : _) → incl (f₁ c) ≡ f (incl c) )
  approx₁ =
    invEq (_ , satAC∃Fin-C0 C (λ _ → fst D 1) (λ c d0 → incl d0 ≡ f (incl c)))
      find-connected-component-C₀

  open import Cubical.Foundations.Transport
  approx : (m : ℕ)
    → ∃[ fₙ ∈ ((n : Fin (suc m)) → Σ[ h ∈ (fst C (fst n) → fst D (fst n)) ]
            ((c : _) → incl (h c) ≡ f (incl c))) ]
        ((n : Fin m) (c : fst C (fst n))
          → fₙ (fsuc n) .fst (CW↪ C (fst n) c) ≡ CW↪ D (fst n) (fₙ (Fin↑ n) .fst c))
  approx zero =
    ∣ (λ { (zero , p) → (λ x → ⊥.rec (CW₀-empty C x))
                      , (λ x → ⊥.rec (CW₀-empty C x))
        ; (suc x , p) → ⊥.rec (¬-<-zero (pred-≤-pred p))})
        , (λ n → ⊥.rec (¬Fin0 n)) ∣₁
  approx (suc zero) =
    PT.map (λ a1 →
     (λ { (zero , p) → (λ x → ⊥.rec (CW₀-empty C x))
                      , (λ x → ⊥.rec (CW₀-empty C x))
         ; (suc zero , p) → a1
         ; (suc (suc x) , p) → ⊥.rec (¬-<-zero (pred-≤-pred (pred-≤-pred p)))})
    , λ { (zero , p) → λ c → ⊥.rec (CW₀-empty C c)
        ; (suc x , p) → ⊥.rec (¬-<-zero (pred-≤-pred p))})
    approx₁
  approx (suc (suc m)) =
    PT.rec
      squash₁
      (λ {(p , f')
      → PT.rec squash₁ (λ r
        → PT.map (λ ind
        → (λ { (n , zero , q) → fst ∘ F↓'-gen _ _ _ ind n (sym (cong predℕ q))
                                , snd ∘ F↓'-gen _ _ _ ind n (sym (cong predℕ q))
              ; (n , suc diff , q) → p (n , diff , cong predℕ q)})
          , λ { (n , zero , q) c →
                   cong (λ w → F↓'-gen (p (suc m , 0 , (λ _ → suc (suc m))) .fst) r
                        (p (suc m , 0 , (λ _ → suc (suc m))) .snd) ind (suc n) w (CW↪ C n c) .fst)
                        (isSetℕ _ _ _ _)
                   ∙∙ (F↓'-gen-coh _ _ _ ind n (cong predℕ (sym q)) c)
                   ∙∙ cong (CW↪ D n)
                       ((λ j → transp (λ i → fst D (predℕ (q (~ i ∧ ~ j)))) j
                                 (p (predℕ (q (~ j)) , 0 , λ i → suc (predℕ (q (~ j ∨ i)))) .fst
                                  (transp (λ i → fst C (predℕ (q (~ i ∨ ~ j)))) (~ j)
                                   (subst (fst C) (cong predℕ q) c))))
                      ∙ cong (p (n , 0 , (λ i → suc (predℕ (q i)))) .fst)
                          (subst⁻Subst (fst C) (cong predℕ q) c)
                      ∙ cong (λ w → p (n , w) .fst c) (isProp≤ _ _))
              ; (n , suc diff , q) c
                → cong (λ w → p (suc n , w) .fst (CW↪ C n c)) (isProp≤ _ _)
                 ∙∙ f' (n , diff , cong predℕ q) c
                 ∙∙ cong (λ w → CW↪ D n (p (n , w) .fst c)) (isProp≤ _ _)})
          (mere-fib-f-coh (p (suc m , 0 , refl) .fst)
            r (p (suc m , 0 , refl) .snd)))
            (fst-lem (p (suc m , 0 , refl) .fst)
                     (p (suc m , 0 , refl) .snd))})
      (approx (suc m))
    where
    open CW-fields C
    F↓-big-ty : (n : ℕ) → Type _
    F↓-big-ty n = (c : fst C n) → Σ[ x ∈ fst D n ] incl x ≡ f (incl c)

    fst-lem : (fm : fst C (suc m) → fst D (suc m))
      → ((c : fst C (suc m)) → incl (fm c) ≡ f (incl c))
      → ∥ ((x : A (suc m)) (y : S₊ m) →
                       CW↪ D (suc m) (fm (α (suc m) (x , y)))
                     ≡ CW↪ D (suc m) (fm (α (suc m) (x , ptSn m)))) ∥₁
    fst-lem fm fh =
      invEq propTrunc≃Trunc1
       (invEq (_ , FinSatAC 1 (CW-fields.card C (suc m)) _) λ a →
         fst propTrunc≃Trunc1
           (sphereToTrunc m λ y →
             TR.map fst (isConnectedCong _ _ (isConnected-CW↪∞ (suc (suc m)) D)
                     (sym (push _)
                     ∙ (fh (CW-fields.α C (suc m) (a , y))
                     ∙ cong f (push _
                            ∙ cong incl (cong (invEq (CW-fields.e C (suc m)))
                               (push (a , y) ∙ sym (push (a , ptSn m))))
                            ∙ sym (push _))
                     ∙ sym (fh (CW-fields.α C (suc m) (a , ptSn m))))
                     ∙ push _) .fst)))

    module _ (fm : fst C (suc m) → fst D (suc m))
             (fm-coh : (x : A (suc m)) (y : S₊ m) →
                       CW↪ D (suc m) (fm (α (suc m) (x , y)))
                     ≡ CW↪ D (suc m) (fm (α (suc m) (x , ptSn m))))
             where
      F↓ : fst C (suc (suc m)) → fst D (suc (suc m))
      F↓ = CW-elim C (suc m) (CW↪ D (suc m) ∘ fm) (λ x → CW↪ D (suc m) (fm (α (suc m) (x , ptSn m))))
                   fm-coh

      module _ (ind : ((c : fst C (suc m)) → incl (fm c) ≡ f (incl c))) where
        fib-f-incl : (c : fst C (suc (suc m))) → Type _
        fib-f-incl c = Σ[ x ∈ fst D (suc (suc m)) ] incl x ≡ f (incl c)

        fib-f-l : (c : fst C (suc m)) → fib-f-incl (CW↪ C (suc m) c)
        fst (fib-f-l c) = CW↪ D (suc m) (fm c)
        snd (fib-f-l c) = sym (push _) ∙∙ ind c ∙∙ cong f (push _)

        fib-f-r : (x : A (suc m))
          → fib-f-incl (invEq (e (suc m)) (inr x))
        fib-f-r x = subst fib-f-incl (cong (invEq (e (suc m)))
                                     (push (x , ptSn m)))
                                     (fib-f-l (α (suc m) (x , ptSn m)))

        fib-f-l-coh : (x : A (suc m))
          → PathP (λ i → fib-f-incl (invEq (e (suc m)) (push (x , ptSn m) i)))
                   (fib-f-l (α (suc m) (x , ptSn m)))
                   (fib-f-r x)
        fib-f-l-coh x i =
          transp (λ j → fib-f-incl (invEq (e (suc m)) (push (x , ptSn m) (i ∧ j))))
                 (~ i)
                 (fib-f-l (α (suc m) (x , ptSn m)))

        mere-fib-f-coh : ∥ ((x : A (suc m)) (y : S₊ m)
                         → PathP (λ i → fib-f-incl (invEq (e (suc m)) (push (x , y) i)))
                                  (fib-f-l (α (suc m) (x , y)))
                                  (fib-f-r x)) ∥₁
        mere-fib-f-coh = invEq propTrunc≃Trunc1
          (invEq (_ , FinSatAC 1 (card (suc m)) _)
            λ a → fst propTrunc≃Trunc1 (sphereToTrunc m
              (sphereElim' m
                (λ x → isOfHLevelRetractFromIso m
                (invIso (PathPIdTruncIso (suc m)))
                (isOfHLevelPathP' m (isProp→isOfHLevelSuc m
                  (isContr→isProp
                    (isConnected-CW↪∞  (suc (suc m)) D _))) _ _))
                ∣ fib-f-l-coh a ∣ₕ)))

      module _ (ind : ((c : fst C (suc m)) → incl (fm c) ≡ f (incl c)))
               (ind2 : ((x : A (suc m)) (y : S₊ m)
                         → PathP (λ i → fib-f-incl ind (invEq (e (suc m)) (push (x , y) i)))
                                  (fib-f-l ind (α (suc m) (x , y)))
                                  (fib-f-r ind x)))
        where
        F↓-big : F↓-big-ty (suc (suc m))
        F↓-big = CW-elim C (suc m) (fib-f-l ind) (fib-f-r ind) ind2

        F↓' : (c : fst C (suc m)) → F↓-big (CW↪ C (suc m) c) ≡ fib-f-l ind c
        F↓' = CW-elim-inl C (suc m) (fib-f-l ind) (fib-f-r ind) ind2

        F↓'-gen : (n : ℕ) (p : suc (suc m) ≡ n) → F↓-big-ty n
        F↓'-gen = J> F↓-big

        F↓'-gen-coh : (n : ℕ) (p : suc m ≡ n) → (c : fst C n)
          → F↓'-gen (suc n) (cong suc p) (CW↪ C n c) .fst
          ≡ CW↪ D n (subst (fst D) p
                       (fm (subst (fst C) (sym p) c)))
        F↓'-gen-coh = J> λ c
          → cong fst (funExt⁻ (transportRefl F↓-big) (CW↪ C (suc m) c))
           ∙ cong fst (F↓' c)
           ∙ sym (cong (CW↪ D (suc m))
                 (transportRefl _
                ∙ cong fm (transportRefl c)))

        F↓-gen-typ : (n : ℕ) (p : suc (suc m) ≡ suc n) → Type _
        F↓-gen-typ n p =
          Σ[ F ∈ F↓-big-ty (suc n) ]
               ((c : fst C n)
               → F (CW↪ C n c) .fst
                ≡ CW↪ D n (subst (fst D) (cong predℕ p)
                            (fm (subst (fst C) (cong predℕ (sym p)) c))))

        F↓-gen : (n : ℕ) (p : suc m ≡ n) → F↓-gen-typ n (cong suc p)
        F↓-gen = J> (F↓-big
          , (λ c → cong fst (F↓' c)
                  ∙ cong (CW↪ D (suc m))
                     (sym (transportRefl _
                        ∙ cong fm (transportRefl c)))))

        F↓-gener : (n : ℕ) (p : suc (suc m) ≡ suc n) → F↓-gen-typ n p
        F↓-gener n p = subst (F↓-gen-typ n) (isSetℕ _ _ _ _) (F↓-gen n (cong predℕ p))

  -- approx : (n : ℕ)
  --   → ∃[ fₙ ∈ (fst C n → fst D n) ] ((c : _) → incl (fₙ c) ≡ f (incl c))
  -- approx zero = ∣ (λ x → ⊥.rec (CW₀-empty C x)) , (λ x → ⊥.rec (CW₀-empty C x)) ∣₁
  -- approx (suc zero) = approx₁
  -- approx (suc (suc n)) = PT.rec squash₁ (λ {(f' , p) → PT.rec squash₁
  --   (λ F → ∣ (fst F) , (snd F .snd) ∣₁)
  --   (connectedFunLifts.liftCW {A = fst D (suc (suc n))} {B = realise D} incl n
  --     (isConnected-CW↪∞ (suc (suc n)) D) C (λ x → CW↪ D (suc n) (f' x))
  --       (λ x → f (incl x))
  --       λ x → sym (push (f' x)) ∙ p x ∙ cong f (push x))})
  --     (approx (suc n))

open import Cubical.Data.Sum
module _ (m : ℕ) (C D : finCW m) (f : realise (finCW→CW m C) → realise (finCW→CW m D)) where

  approxFinCw : ∃[ fₙ ∈ ((n : ℕ) → Σ[ f' ∈ (fst C n → fst D n) ] ((c : _) → incl (f' c) ≡ f (incl c))) ]
                 ((n : ℕ) (c : fst C n) → fₙ (suc n) .fst (CW↪ (finCW→CW m C) n c)
                                           ≡ CW↪ (finCW→CW m D) n (fₙ n .fst c))
  approxFinCw =
    PT.map (λ appr → (λ n → (f-full (fst ∘ fst appr) (snd appr) n )
                            , f-full-coh' _ _ (snd ∘ fst appr) n)
                            , (f-coh-full (fst ∘ fst appr) (snd appr)))
           (approx (finCW→CW m C) (finCW→CW m D) f (suc m))
    where
    module _ (fbase : (n : Fin (suc (suc m))) → fst C (fst n) → fst D (fst n))
             (fcoh : (n : Fin (suc m)) (c : fst C (fst n))
                  → fbase (fsuc n) (CW↪ (finCW→CW m C) (fst n) c)
                   ≡ CW↪ (finCW→CW m D) (fst n) (fbase (Fin↑ n) c)) where

      C≃ : (a : ℕ) → fst C (a +ℕ m) ≃ fst C (suc (a +ℕ m))
      C≃ a = _ , C .snd .snd a

      D≃ : (a : ℕ) → fst D (a +ℕ m) ≃ fst D (suc (a +ℕ m))
      D≃ a = _ , D .snd .snd a

      f-extend : (a : ℕ) → fst C (a +ℕ m) → fst D (a +ℕ m)
      f-extend zero = fbase (m , (1 , refl))
      f-extend (suc a) c = fst (D≃ a) (f-extend a (invEq (C≃ a) c))

      f-extend-comm : (x n : ℕ) (p : x +ℕ m ≡ n) (t : fst C n)
        → subst (fst D) (cong suc p)
                (f-extend (suc x)
                  (subst (fst C) (sym (cong suc p)) (CW↪ (finCW→CW m C) n t)))
         ≡ CW↪ (finCW→CW m D) n (subst (fst D) p (f-extend x (subst (fst C) (sym p) t)))
      f-extend-comm x = J> λ t →
          transportRefl _
        ∙ cong (CW↪ (finCW→CW m D) (x +ℕ m))
            (sym (transportRefl _
            ∙ cong (f-extend x) (transportRefl _
              ∙ sym (cong (invEq (C≃ x)) (transportRefl _)
                    ∙ retEq (C≃ x) t))))

      ≤-lem : (n : ℕ) → suc n ≤ m → suc n ≤ suc (suc m)
      ≤-lem n x = suc (suc (fst x)) , (cong (2 +ℕ_) (snd x))

      f-full : (n : ℕ) → fst C n → fst D n
      f-full n with (Dichotomyℕ m n)
      ... | inl x = subst (λ n → fst C n → fst D n) (snd x)
                          (f-extend (fst x))
      ... | inr x = fbase (n , ≤-lem n x)

      f-full-coh' : (ind : (a : Fin (suc (suc m))) (c : fst (finCW→CW m C) (fst a))
                    → incl (fbase a c) ≡ f (incl c))
            (n : ℕ) (c : fst C n) → incl (f-full n c) ≡ f (incl c)
      f-full-coh' ind n c with Dichotomyℕ m n
      ... | inl (a , p) = help2 a n p c
        where
        lem2 : (a : ℕ) (c : fst C (a +ℕ m))
          → incl (f-extend a c) ≡ f (incl c)
        lem2 zero c = ind (m , 1 , refl) c
        lem2 (suc a) c =
            sym (push _)
          ∙ lem2 a (invEq (C≃ a) c)
          ∙ cong f (push (invEq (C≃ a) c)
          ∙ cong incl (secEq (C≃ a) c))

        help2 : (a n : ℕ) (p : a +ℕ m ≡ n) (c : fst C n)
              → incl (subst (λ n₁ → fst C n₁ → fst D n₁) p (f-extend a) c)
               ≡ f (incl c)
        help2 a = J> λ c → cong incl (λ j → transportRefl (f-extend a) j c)
                ∙ lem2 a c
      ... | inr x = ind (n , ≤-lem n x) c

      f-coh-full : (n : ℕ) (c : fst C n)
        → f-full (suc n) (CW↪ (finCW→CW m C) n c)
         ≡ CW↪ (finCW→CW m D) n (f-full n c)
      f-coh-full n c with (Dichotomyℕ m n) | (Dichotomyℕ m (suc n))
      ... | inl x | inl x₁ =
           cong (λ x₁ → subst (λ n₁ → fst C n₁ → fst D n₁) (snd x₁) (f-extend (fst x₁))
                (CW↪ (finCW→CW m C) n c)) (isProp≤ x₁ (suc (fst x) , cong suc (snd x)))
         ∙ f-extend-comm _ _ (snd x) c
      ... | inl x | inr x₁ = ⊥.rec (¬-suc-n<n (<≤-trans x₁ x))
      ... | inr x | inl (zero , p) =
          (λ i → transp (λ j → fst D (p (j ∨ i))) i
                  (fbase (p i , 1 , (λ j → suc (suc (p (~ j ∧ i)))))
                   (transp (λ j → fst C (p (~ j ∨ i))) i
                     (CW↪ (finCW→CW m C) n c))))
        ∙ cong (λ w → fbase (suc n , w) (CW↪ (finCW→CW m C) n c))
               (isProp≤ _ _)
        ∙ fcoh (n , suc (fst x) , cong suc (snd x)) c
        ∙ cong (CW↪ (finCW→CW m D) n)
            (cong (λ w → fbase (n , w) c) (isProp≤ _ _))
      ... | inr x | inl (suc diff , p) = ⊥.rec (¬m<m (<≤-trans x (diff , cong predℕ p)))
      ... | inr x | inr x₁ = cong (λ w → fbase (suc n , w) (CW↪ (finCW→CW m C) n c)) (isProp≤ _ _)
                          ∙∙ fcoh (n , ≤-trans x (1 , refl)) c
                          ∙∙ cong (CW↪ (finCW→CW m D) n)
                              (cong (λ w → fbase (n , w) c) (isProp≤ _ _))


module SeqHomotopyTypes {ℓ} {C D : Sequence ℓ}
  (f-c g-c : SequenceMap C D)
  where

  f = SequenceMap.map f-c
  g = SequenceMap.map g-c
  f-hom = SequenceMap.comm f-c
  g-hom = SequenceMap.comm g-c

  cell-hom : (n : ℕ) (c : obj C n) → Type ℓ
  cell-hom n c = Sequence.map D (f n c) ≡ Sequence.map D (g n c)

  cell-hom-coh : (n : ℕ) (c : obj C n)
    → cell-hom n c → cell-hom (suc n) (Sequence.map C c) → Type ℓ
  cell-hom-coh n c h h' =
    Square (cong (Sequence.map D) h) h'
           (cong (Sequence.map D) (f-hom n c))
           (cong (Sequence.map D) (g-hom n c))

  agrees-in-lim : (h∞ : realiseSequenceMap f-c ≡ realiseSequenceMap g-c)
    → {n : ℕ} (x : obj C n) (h : cell-hom n x) → Type ℓ
  agrees-in-lim  h∞ {n = n} x h =
     Square (funExt⁻ h∞ (incl x)) (cong incl h)
            (push (f n x)) (push (g n x))

  goalTypeFin : (m : ℕ) → Type _
  goalTypeFin m =
    Σ[ hₙ ∈ ((n : Fin (suc m)) (c : obj C (fst n)) → cell-hom (fst n) c) ]
       ((n : Fin m) (c : obj C (fst n))
         → cell-hom-coh (fst n) c
             (hₙ (Fin↑ n) c)
             (hₙ (fsuc n) (Sequence.map C c)))

  goalType : Type _
  goalType =
    Σ[ hₙ ∈ ((n : ℕ) (c : obj C n)
       → (cell-hom n c)) ]
            ((n : ℕ) (c : obj C n)
              → cell-hom-coh n c
                (hₙ n c) (hₙ (suc n) (Sequence.map C c)))

-- homotopy in colimit → cellular homotopy
module _ {C D : CW} (f-c g-c : cellMap C D)
         (h∞ : realiseCellMap f-c ≡ realiseCellMap g-c) where
  open SeqHomotopyTypes f-c g-c
  open CW-fields C

  -- base case
  pathToCellularHomotopy₁ : (c : fst C 1) → ∃[ h ∈ cell-hom 1 c ] agrees-in-lim h∞ c h
  pathToCellularHomotopy₁ c = TR.rec squash₁
    (λ {(d , p)
      → ∣ d
      , (λ i j
      → hcomp (λ k →
           λ {(i = i0) → doubleCompPath-filler
                            (sym (push (f 1 c)))
                            (funExt⁻ h∞ (incl c))
                            (push (g 1 c)) (~ k) j
            ; (i = i1) → incl (d j)
            ; (j = i0) → push (f 1 c) (~ k ∨ i)
            ; (j = i1) → push (g 1 c) (~ k ∨ i)})
              (p (~ i) j)) ∣₁})
    (isConnectedCong 1 (CW↪∞ D 2)
      (isConnected-CW↪∞ 2 D) h∞* .fst)
    where
    h∞* : CW↪∞ D 2 (CW↪ D 1 (f 1 c)) ≡ CW↪∞ D 2 (CW↪ D 1 (g 1 c))
    h∞* = sym (push (f 1 c)) ∙∙ funExt⁻ h∞ (incl c) ∙∙ push (g 1 c)

  -- induction step
  pathToCellularHomotopy-ind : (n : ℕ)
    → (hₙ : (c : fst C (suc n)) → Σ[ h ∈ cell-hom (suc n) c ] agrees-in-lim h∞ c h)
    → ∥ Σ[ hₙ₊₁ ∈ ((c : fst C (suc (suc n)))
                → Σ[ h ∈ cell-hom (suc (suc n)) c ] agrees-in-lim h∞ c h) ]
        ((c : _) → cell-hom-coh (suc n) c
                     (hₙ c .fst) (hₙ₊₁ (CW↪ C (suc n) c) .fst)) ∥₁
  pathToCellularHomotopy-ind n ind =
    PT.map (λ q → hₙ₊₁ q , hₙ₊₁-coh q)
           Πfiber-cong²-hₙ₊₁-push∞
    where
    Pushout→C = invEq (e (suc n))

    hₙ'-filler : (x : fst C (suc n)) → _
    hₙ'-filler x =
      doubleCompPath-filler
            (sym (f-hom (suc n) x))
            (ind x .fst)
            (g-hom (suc n) x)

    hₙ' : (x : fst C (suc n))
      → f (suc (suc n)) (CW↪ C (suc n) x)
       ≡ g (suc (suc n)) (CW↪ C (suc n) x)
    hₙ' x = hₙ'-filler x i1

    -- homotopy for inl
    hₙ₊₁-inl : (x : fst C (suc n))
      → cell-hom (suc (suc n)) (invEq (e (suc n)) (inl x))
    hₙ₊₁-inl x = cong (CW↪ D (suc (suc n))) (hₙ' x)

    -- hₙ₊₁-inl coherent with h∞
    hₙ₊₁-inl-coh : (x : fst C (suc n))
      → agrees-in-lim h∞ (invEq (e (suc n)) (inl x)) (hₙ₊₁-inl x)
    hₙ₊₁-inl-coh x i j =
      hcomp (λ k
        → λ {(i = i0) → h∞ j (incl (CW↪ C (suc n) x))
            ; (i = i1) → push (hₙ' x j) k
            ; (j = i0) → push (f (suc (suc n)) (CW↪ C (suc n) x)) (k ∧ i)
            ; (j = i1) → push (g (suc (suc n)) (CW↪ C (suc n) x)) (k ∧ i)})
       (hcomp (λ k
         → λ {(i = i0) → h∞ j (push x k)
             ; (i = i1) → incl (hₙ'-filler x k j)
             ; (j = i0) → compPath-filler'
                             (push (f (suc n) x))
                             ((λ i₁ → incl (f-hom (suc n) x i₁))) (~ i) k
             ; (j = i1) → compPath-filler'
                             (push (g (suc n) x))
                             ((λ i₁ → incl (g-hom (suc n) x i₁))) (~ i) k})
           (ind x .snd i j))

    module _ (x : A (suc n)) (y : S₊ n) where
      push-path-filler : I → I → Pushout (α (suc n)) fst
      push-path-filler i j =
        compPath-filler'' (push (x , y)) (sym (push (x , ptSn n))) i j

      push-path :
        Path (Pushout (α (suc n)) fst)
             (inl (α (suc n) (x , y)))
             (inl (α (suc n) (x , ptSn n)))
      push-path j = push-path-filler i1 j

      D∞PushSquare : Type
      D∞PushSquare =
        Square {A = realise D}
          (cong (CW↪∞ D (suc (suc (suc n))))
            (hₙ₊₁-inl (snd C .snd .fst (suc n) (x , y))))
          (cong (CW↪∞ D (suc (suc (suc n))))
            (hₙ₊₁-inl (snd C .snd .fst (suc n) (x , ptSn n))))
          (λ i → incl (CW↪ D (suc (suc n))
                        (f (suc (suc n)) (Pushout→C (push-path i)))))
          (λ i → incl (CW↪ D (suc (suc n))
                        (g (suc (suc n)) (Pushout→C (push-path i)))))

      cong² : PathP (λ i → cell-hom (suc (suc n))
                             (Pushout→C (push-path i)))
                    (hₙ₊₁-inl (α (suc n) (x , y)))
                    (hₙ₊₁-inl (α (suc n) (x , ptSn n)))
            → D∞PushSquare
      cong² p i j = incl (p i j)

      isConnected-cong² : isConnectedFun (suc n) cong²
      isConnected-cong² =
        isConnectedCong² (suc n) (CW↪∞ D (3 +ℕ n))
          (isConnected-CW↪∞ (3 +ℕ n) D)

      hₙ₊₁-push∞ : D∞PushSquare
      hₙ₊₁-push∞ i j =
        hcomp (λ k
        → λ {(i = i0) → hₙ₊₁-inl-coh (α (suc n) (x , y)) k j
            ; (i = i1) → hₙ₊₁-inl-coh (α (suc n) (x , ptSn n)) k j
            ; (j = i0) → push (f (suc (suc n)) (Pushout→C (push-path i))) k
            ; (j = i1) → push (g (suc (suc n)) (Pushout→C (push-path i))) k})
        (hcomp (λ k
         → λ {(i = i0) → h∞ j (incl (Pushout→C (push (x , y) (~ k))))
             ; (i = i1) → h∞ j (incl (Pushout→C (push (x , ptSn n) (~ k))))
             ; (j = i0) → incl (f (suc (suc n))
                                 (Pushout→C (push-path-filler k i)))
             ; (j = i1) → incl (g (suc (suc n))
                                 (Pushout→C (push-path-filler k i)))})
         (h∞ j (incl (Pushout→C (inr x)))))

      fiber-cong²-hₙ₊₁-push∞ : hLevelTrunc (suc n) (fiber cong² hₙ₊₁-push∞)
      fiber-cong²-hₙ₊₁-push∞ = isConnected-cong² hₙ₊₁-push∞ .fst

      hₙ₊₁-coh∞ : (q : fiber cong² hₙ₊₁-push∞)
        → PathP (λ i → agrees-in-lim h∞ (Pushout→C (push-path i)) (q .fst i))
                 (hₙ₊₁-inl-coh (α (suc n) (x , y)))
                 (hₙ₊₁-inl-coh (α (suc n) (x , ptSn n)))
      hₙ₊₁-coh∞ q j i k =
        hcomp (λ r
          → λ {(i = i0) → h∞ k (incl (Pushout→C (push-path j)))
              ; (i = i1) → q .snd (~ r) j k
              ; (j = i0) → hₙ₊₁-inl-coh (α (suc n) (x , y)) i k
              ; (j = i1) → hₙ₊₁-inl-coh (α (suc n) (x , ptSn n)) i k
              ; (k = i0) → push (f (suc (suc n)) (Pushout→C (push-path j))) i
              ; (k = i1) → push (g (suc (suc n)) (Pushout→C (push-path j))) i})
         (hcomp (λ r
           → λ {(i = i0) → h∞ k (incl (Pushout→C (push-path j)))
               ; (j = i0) → hₙ₊₁-inl-coh (α (suc n) (x , y)) (i ∧ r) k
               ; (j = i1) → hₙ₊₁-inl-coh (α (suc n) (x , ptSn n)) (i ∧ r) k
               ; (k = i0) → push (f (suc (suc n))
                               (Pushout→C (push-path j))) (i ∧ r)
               ; (k = i1) → push (g (suc (suc n))
                               (Pushout→C (push-path j))) (i ∧ r)})
          (hcomp (λ r
            → λ {(i = i0) → h∞ k (incl (Pushout→C (push-path-filler r j)))
                ; (j = i0) → h∞ k (incl (invEq (e (suc n))
                                    (push (x , y) (~ r))))
                ; (j = i1) → h∞ k (incl (invEq (e (suc n))
                                    (push (x , ptSn n) (~ r))))
                ; (k = i0) → incl (f (suc (suc n))
                               (Pushout→C (push-path-filler r j)))
                ; (k = i1) → incl (g (suc (suc n))
                               (Pushout→C (push-path-filler r j)))})
            (h∞ k (incl (Pushout→C (inr x))))))

    Πfiber-cong²-hₙ₊₁-push∞ :
      ∥ ((x : _) (y : _) → fiber (cong² x y) (hₙ₊₁-push∞ x y)) ∥₁
    Πfiber-cong²-hₙ₊₁-push∞ =
      Iso.inv propTruncTrunc1Iso
        (invEq (_ , FinSatAC 1 _ _)
        λ x → Iso.fun propTruncTrunc1Iso
                (sphereToTrunc n (fiber-cong²-hₙ₊₁-push∞ x)))

    module _ (q : (x : Fin (fst (snd C) (suc n))) (y : S₊ n)
                → fiber (cong² x y) (hₙ₊₁-push∞ x y)) where
      main-inl : (x : fst C (suc n))
        → Σ (cell-hom (suc (suc n)) (CW↪ C (suc n) x))
             (agrees-in-lim h∞ (CW↪ C (suc n) x))
      main-inl x = hₙ₊₁-inl x , hₙ₊₁-inl-coh x

      main-push : (x : A (suc n)) (y : S₊ n)
        → PathP (λ i → Σ (cell-hom (suc (suc n)) (Pushout→C (push-path x y i)))
                           (agrees-in-lim h∞ (Pushout→C (push-path x y i))))
                 (main-inl (α (suc n) (x , y)))
                 (main-inl (α (suc n) (x , ptSn n)))
      main-push x y = ΣPathP (fst (q x y) , hₙ₊₁-coh∞ x y (q x y))

      hₙ₊₁ : (c : fst C (suc (suc n)))
        → Σ (cell-hom (suc (suc n)) c) (agrees-in-lim h∞ c)
      hₙ₊₁ = CW-elim' C n main-inl main-push

      hₙ₊₁-coh-pre : (c : fst C (suc n)) →
        Square (cong (CW↪ D (suc (suc n))) (ind c .fst))
               (hₙ₊₁-inl c)
               (cong (CW↪ D (suc (suc n))) (f-hom (suc n) c))
               (cong (CW↪ D (suc (suc n))) (g-hom (suc n) c))
      hₙ₊₁-coh-pre c i j = CW↪ D (suc (suc n)) (hₙ'-filler c i j)

      hₙ₊₁-coh : (c : fst C (suc n)) →
        Square (cong (CW↪ D (suc (suc n))) (ind c .fst))
               (hₙ₊₁ (CW↪ C (suc n) c) .fst)
               (cong (CW↪ D (suc (suc n))) (f-hom (suc n) c))
               (cong (CW↪ D (suc (suc n))) (g-hom (suc n) c))
      hₙ₊₁-coh c = hₙ₊₁-coh-pre c
        ▷ λ i → CW-elim'-inl C n
                  {B = λ c → Σ (cell-hom (suc (suc n)) c) (agrees-in-lim h∞ c)}
                  main-inl main-push c (~ i) .fst

  -- main theorem
  pathToCellularHomotopy : {m : ℕ}
    → ∃[ hₙ ∈ ((n : Fin (suc m)) (c : fst C (fst n))
            → Σ[ h ∈ cell-hom (fst n) c ] agrees-in-lim h∞ c h ) ]
         ((n : Fin m) (c : fst C (fst n))
           → cell-hom-coh (fst n) c
                (hₙ (Fin↑ n) c .fst)
                (hₙ (fsuc n) (CW↪ C (fst n) c) .fst))
  pathToCellularHomotopy {m = zero} = ∣ hom₀ , (λ n → ⊥.rec (¬Fin0 n)) ∣₁
    where
    hom₀ : (n : Fin 1) (c : fst C (fst n)) → Σ (cell-hom (fst n) c) (agrees-in-lim h∞ c)
    hom₀ (zero , p) c = ⊥.rec (CW₀-empty C c)
    hom₀ (suc n , p) =
      ⊥.rec (snotz (sym (+-suc (fst (pred-≤-pred p)) n)
                  ∙ pred-≤-pred p .snd))
  pathToCellularHomotopy {m = suc zero} =
    TR.rec squash₁
      (λ hom → ∣ hom
      , (λ { (zero , p) c → ⊥.rec (CW₀-empty C c)
           ; (suc n , p) → ⊥.rec (¬-<-zero (pred-≤-pred p))}) ∣₁)
      (invEq (_ , FinSatAC 1 _ _) hom₁)
    where
    hom₁ : (n : Fin 2)
      → hLevelTrunc 1 ((c : fst C (fst n))
                     → Σ (cell-hom (fst n) c) (agrees-in-lim h∞ c))
    hom₁ (zero , p) = ∣ (λ c → ⊥.rec (CW₀-empty C c)) ∣
    hom₁ (suc zero , p) =
      PT.rec (isOfHLevelTrunc 1)
      (λ {(f , p) → ∣ (λ c → f c , p c) ∣ₕ})
        (invEq (_ , satAC∃Fin-C0 C (cell-hom 1) (agrees-in-lim h∞))
               pathToCellularHomotopy₁)
    hom₁ (suc (suc n) , p) =
      ⊥.rec (¬-<-zero (pred-≤-pred (pred-≤-pred p)))
  pathToCellularHomotopy {m = suc (suc m)} =
    PT.rec squash₁
      (λ {(h , h-coh) → PT.rec squash₁
             (λ f → ∣ hom h h-coh (fst f) (snd f)
                    , hom-coh h h-coh (fst f) (snd f) ∣₁)
      (pathToCellularHomotopy-ind _ (h flast))})
      (pathToCellularHomotopy {m = suc m})
    where
    module _ (h : (n : Fin (suc (suc m))) (c : fst C (fst n))
                → Σ (cell-hom (fst n) c) (agrees-in-lim h∞ c))
             (h-coh : (n : Fin (suc m)) (c : fst C (fst n))
                    → cell-hom-coh (fst n) c
                         (h (Fin↑ n) c .fst)
                         (h (fsuc n) (CW↪ C (fst n) c) .fst))
             (h-max : (c : fst C (suc (suc m)))
                   → Σ (cell-hom (suc (suc m)) c) (agrees-in-lim h∞ c))
             (h-max-coh : (c : fst C (suc m)) →
                          cell-hom-coh (suc m) c
                            (h flast c .fst)
                            (h-max (CW↪ C (suc m) c) .fst))
      where
      h-help : {n : ℕ} {x : _} {p : _} {q : _} → h (n , p) x .fst ≡ h (n , q) x .fst
      h-help {n = n} {x} {p} {q} i = h (n , isProp≤ p q i) x .fst

      hom : (n : Fin (suc (suc (suc m)))) (c : fst C (fst n))
           → Σ (cell-hom (fst n) c) (agrees-in-lim h∞ c)
      hom (n , zero , p) =
        subst (λ n → (c : fst C n) → Σ (cell-hom n c) (agrees-in-lim h∞ c))
              (cong predℕ (sym p)) h-max
      hom (n , suc diff , p) = h (n , diff , cong predℕ p)

      hom₀-refl : {p : _} → hom (_ , zero , p) ≡ h-max
      hom₀-refl {p = p} =
        (λ j → subst (λ n → (c : fst C n)
                   → Σ (cell-hom n c) (agrees-in-lim h∞ c))
                     (isSetℕ _ _ (sym (cong predℕ p)) refl j)
                     h-max)
        ∙ transportRefl h-max

      hom-coh : (n : Fin (suc (suc m))) (c : fst C (fst n)) →
                   cell-hom-coh (fst n) c
                     (hom (Fin↑ n) c .fst)
                     (hom (fsuc n) (CW↪ C (fst n) c) .fst)
      hom-coh (n , zero , p) =
        transport (λ j → (c : fst C (predℕ (p (~ j))))
               → cell-hom-coh (predℕ (p (~ j))) c
                    (hom (Fin↑ (predℕ (p (~ j)) , zero , p-coh j)) c .fst)
                    (hom (fsuc (predℕ (p (~ j)) , zero , p-coh j))
                      (CW↪ C (predℕ (p (~ j))) c) .fst))
           (λ c → cong (cong (CW↪ D (suc (suc m)))) h-help
                ◁ h-max-coh c
                ▷ cong fst (funExt⁻ (sym (hom₀-refl)) (CW↪ C (suc m) c)))
        where
        p-coh : PathP (λ j → suc (predℕ (p (~ j))) ≡ suc (suc m)) refl p
        p-coh = isProp→PathP (λ i → isSetℕ _ _) _ p

      hom-coh (n , suc diff , p) c =
          cong (cong (CW↪ D (suc n))) h-help
        ◁ h-coh (n , diff , cong predℕ p) c
        ▷ h-help

module _ (m : ℕ) {C D : finCW m}
  (f-c g-c : cellMap (finCW→CW m C) (finCW→CW m D))
  (h∞ : realiseCellMap f-c ≡ realiseCellMap g-c) where
  open SeqHomotopyTypes f-c g-c
  C' = finCW→CW m C
  D' = finCW→CW m D

  open CW-fields C'

  private
    GoalTy =
      Σ[ hₙ ∈ ((n : ℕ) (c : fst C' n) → cell-hom n c) ]
           ((n : ℕ) (c : fst C' n)
             → cell-hom-coh n c
                  (hₙ n c)
                  (hₙ (suc n) (CW↪ C' n c)))

  pathToCellularHomotopyFin :
     ∃[ hₙ ∈ ((n : ℕ) (c : fst C' n) → cell-hom n c) ]
         ((n : ℕ) (c : fst C' n)
           → cell-hom-coh n c
                (hₙ n c)
                (hₙ (suc n) (CW↪ C' n c)))
  pathToCellularHomotopyFin =
    PT.map (λ p → main₁ p , main₂ p)
      (pathToCellularHomotopy f-c g-c h∞ {m = suc m})
    where
    module _ (ind : Σ
      ((c : Fin (suc (suc m))) (n : fst (finCW→CW m C) (fst c)) →
       Σ (cell-hom (fst c) n) (agrees-in-lim h∞ n))
      (λ hₙ →
         (n : Fin (suc m)) (c : fst (finCW→CW m C) (fst n)) →
         cell-hom-coh (fst n) c (hₙ (Fin↑ n) c .fst)
         (hₙ (fsuc n) (CW↪ (finCW→CW m C) (fst n) c) .fst)))
      where
      open import Cubical.Foundations.Equiv.HalfAdjoint
      cEq : (a : ℕ) → fst C' (a +ℕ suc m) ≃ fst C' (suc (a +ℕ suc m))
      cEq a = CW↪ (fst C , fst (C .snd)) (a +ℕ suc m)
            , transport (λ i → isEquiv (CW↪ (fst C , fst (C .snd)) (+-suc a m (~ i))))
              (C .snd .snd (suc a))

      cEq' : (a : ℕ) → HAEquiv (fst C' (a +ℕ suc m)) (fst C' (suc (a +ℕ suc m)))
      cEq' a = iso→HAEquiv (equivToIso (cEq a))
      open isHAEquiv renaming (g to haInv)

      baz : (a : ℕ) → (c : fst C' (a +ℕ suc m)) → cell-hom (a +ℕ suc m) c
      baz zero c = fst ind (suc m , 0 , refl) c .fst
      baz (suc a) c =
        cong (CW↪ (finCW→CW m D) (suc (a +ℕ suc m))
             ∘ SequenceMap.map f-c (suc (a +ℕ suc m)))
             (sym (rinv (cEq' a .snd) c))
        ∙∙ cong (CW↪ (finCW→CW m D) (suc (a +ℕ suc m)))
                (sym (SequenceMap.comm f-c (a +ℕ suc m) (haInv (cEq' a .snd) c))
             ∙∙ baz a (haInv (cEq' a .snd) c)
             ∙∙ SequenceMap.comm g-c (a +ℕ suc m) (haInv (cEq' a .snd) c)) 
        ∙∙ cong (CW↪ (finCW→CW m D) (suc (a +ℕ suc m))
             ∘ SequenceMap.map g-c (suc (a +ℕ suc m)))
             (rinv (cEq' a .snd) c) -- (linv (cEq' a) c)

      main₁ : (n : ℕ) (c : fst C' n) → cell-hom n c
      main₁ n with (Dichotomyℕ (suc m) n)
      ... | inl (a , b) = subst (λ n → (c : fst C' n) → cell-hom n c) b (baz a)
      ... | inr x = λ c → fst ind (n , <-trans x (0 , refl)) c .fst

      main₂* : (x1 n : ℕ) (c : fst C' (x1 +ℕ suc m))
        → cell-hom-coh (x1 +ℕ suc m) c (baz x1 c) (baz (suc x1) (CW↪ C' (x1 +ℕ suc m) c))
      main₂* x1 n c i j =
        hcomp (λ k → λ {(i = i0) → CW↪ (finCW→CW m D) (suc (x1 +ℕ suc m)) (baz x1 (linv (cEq' x1 .snd) c k) j)
                       ; (j = i0) → CW↪ (finCW→CW m D) (suc (x1 +ℕ suc m)) (help' i k)
                       ; (j = i1) → CW↪ (finCW→CW m D) (suc (x1 +ℕ suc m)) (help i k)})
          (CW↪ (finCW→CW m D) (suc (x1 +ℕ suc m))
            (hcomp (λ k → λ {(i = i0) → baz x1 (haInv (cEq' x1 .snd) (fst (cEq' x1) c)) j
                            ; (j = i0) → SequenceMap.comm f-c (x1 +ℕ suc m)
                                            (haInv (cEq' x1 .snd) (fst (cEq' x1) c)) (i ∧ k)
                            ; (j = i1) → SequenceMap.comm g-c (x1 +ℕ suc m)
                                            (haInv (cEq' x1 .snd) (fst (cEq' x1) c)) (i ∧ k)})
                   (baz x1 (haInv (cEq' x1 .snd) (fst (cEq' x1) c)) j)))
          where
          help' : Square (cong (CW↪ (finCW→CW m D) (x1 +ℕ suc m))
                               (cong (f (x1 +ℕ suc m)) (linv (cEq' x1 .snd) c)))
                         (cong (f (suc (x1 +ℕ suc m)))
                         (rinv (cEq' x1 .snd) (CW↪ C' (x1 +ℕ suc m) c)))
                         (f-hom (x1 +ℕ suc m) (haInv (cEq' x1 .snd) (fst (cEq' x1) c)))
                         (SequenceMap.comm f-c (x1 +ℕ suc m) c)
          help' = (λ i j → f-hom (x1 +ℕ suc m) (linv (cEq' x1 .snd) c j) i)
                ▷ cong (cong (f (suc (x1 +ℕ suc m)))) (com (cEq' x1 .snd) c)

          help : Square (cong (CW↪ (finCW→CW m D) (x1 +ℕ suc m) ∘ SequenceMap.map g-c (x1 +ℕ suc m))
                        (linv (cEq' x1 .snd) c))
                   (cong (SequenceMap.map g-c (suc (x1 +ℕ suc m)))
                     (rinv (cEq' x1 .snd) (CW↪ C' (x1 +ℕ suc m) c)))
                   (SequenceMap.comm g-c (x1 +ℕ suc m)
                     (haInv (cEq' x1 .snd) (CW↪ C' (x1 +ℕ suc m) c)))
                   (SequenceMap.comm g-c (x1 +ℕ suc m) c)
          help = ((λ i j → g-hom (x1 +ℕ suc m) (linv (cEq' x1 .snd) c j) i))
               ▷ cong (cong (g (suc (x1 +ℕ suc m)))) (com (cEq' x1 .snd) c)

      main₂-inl : (x1 n : ℕ) (p : x1 +ℕ suc m ≡ n) (x₁ : suc m ≤ suc n) (c : fst C' n)
        → cell-hom-coh n c
            (subst (λ n → (c : fst C' n) → cell-hom n c) p (baz x1) c)
            (subst (λ n → (c : fst C' n) → cell-hom n c) (snd x₁) (baz (fst x₁))
                   (CW↪ (finCW→CW m C) n c))
      main₂-inl x1 =
        J> λ r c → subst2 (cell-hom-coh (x1 +ℕ suc m) c)
          (λ j → transportRefl (baz x1) (~ j) c)
          (cong (λ path → subst (λ n → (c₁ : fst C' n) → cell-hom n c₁) path (baz (fst r))
                 (CW↪ (finCW→CW m C) (x1 +ℕ suc m) c))
                 (isSetℕ _ _ (cong (_+ℕ suc m) (inj-+m {n = suc x1} (snd r))) (snd r)))
          (main₂-inl' (fst r) (sym (inj-+m {n = suc x1} (snd r))) c)
        where
        main₂-inl' : (r1 : ℕ) (r2 : suc x1 ≡ r1) (c : fst C' (x1 +ℕ suc m))
          → cell-hom-coh (x1 +ℕ suc m) c (baz x1 c)
              (subst (λ n → (c₁ : fst C' n) → cell-hom n c₁)
               (λ i → r2 (~ i) +ℕ suc m) (baz r1)
               (CW↪ (finCW→CW m C) (x1 +ℕ suc m) c))
        main₂-inl' = J> λ c
          → subst (cell-hom-coh (x1 +ℕ suc m) c (baz x1 c))
                  (λ j → transportRefl (baz (suc x1)) (~ j)
                           (CW↪ (finCW→CW m C) (x1 +ℕ suc m) c))
                  (main₂* x1 m c)

      main₂ : (n : ℕ) (c : fst C' n) →
        cell-hom-coh n c (main₁ n c) (main₁ (suc n) (CW↪ C' n c))
      main₂ n with (Dichotomyℕ (suc m) n) | Dichotomyℕ (suc m) (suc n)
      ... | inl x | inl x₁ = main₂-inl (fst x) n (snd x) x₁
      ... | inl x | inr x₁ = ⊥.rec (¬m<m (<-trans x (pred-≤-pred x₁)))
      ... | inr x | inl (zero , x₁) = λ c → snd ind (n , x) c
        ▷ (lem n (cong predℕ x₁) c _
        ∙ cong (λ w → subst (λ n₁ → (c₁ : fst C' n₁) → cell-hom n₁ c₁) w
                        (λ c₁ → fst ind (suc m , 0 , (λ _ → suc (suc m))) c₁ .fst)
                        (snd (snd (snd (snd (fst (snd C)))) n) .equiv-proof (inl c) .fst .fst))
               (isSetℕ _ _ (cong suc (cong predℕ x₁)) x₁))
        where
        lem : (n : ℕ) (p : m ≡ n) (c : fst C n) (w : _)
          → fst ind (suc n , w) (CW↪ C' n c) .fst
           ≡ subst (λ n₂ → (c₁ : fst C' n₂) → cell-hom n₂ c₁)
                   (cong suc p) (λ c → ind .fst (suc m , 0 , refl) c .fst)
                   (CW↪ C' n c)
        lem = J> λ c w → cong (λ w → fst ind (suc m , w) (CW↪ C' m c) .fst) (isProp≤ _ _)
          ∙ λ j → transportRefl (λ (c₁ : fst C' (suc m)) → ind .fst (suc m , 0 , refl) c₁ .fst) (~ j) (CW↪ C' m c)
      ... | inr x | inl (suc diff , x₁) =
        ⊥.rec (⊥.rec (¬m<m (≤<-trans x (diff , +-suc diff (suc m) ∙ x₁))))
      ... | inr x | inr x₁ = λ c → snd ind (n , x) c
        ▷ cong (λ p → fst ind (suc n , p) (CW↪ (finCW→CW m C) n c) .fst) (isProp≤ _ _)



-- module _ (m : ℕ) (C D : finCW m) (f : realise (finCW→CW m C) → realise (finCW→CW m D)) where
--   finMap→cellMap : ∥ cellMap (finCW→CW m C) (finCW→CW m D) ∥₂
--   finMap→cellMap = elim→Set {P = λ _ → ∥ cellMap (finCW→CW m C) (finCW→CW m D) ∥₂}
--                               (λ _ → squash₂)
--                               ∣_∣₂
--                               {!!}
--                               (finMap→cellMap₁ m C D f)
