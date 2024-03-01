{-# OPTIONS --cubical --lossy-unification --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (isProp≤ ; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.CW
open import Cubical.Data.CW.Map

open import Cubical.Data.Sequence

open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.PropositionalTruncation as PT hiding (elimFin)
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.Axiom.Choice

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base
open import Cubical.Algebra.ChainComplex

open import fin-cw-map



module cw-approx2 where

open Sequence

private
  variable
    ℓ ℓ' ℓ'' : Level


open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open FinSequenceMap
record finiteCellHom {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ) (f g : finCellMap m C D) : Type (ℓ-max ℓ ℓ') where
  field
    hom : (n : Fin (suc m)) → (x : C .fst (fst n)) → CW↪ D (fst n) (f .fmap n x) ≡ CW↪ D (fst n) (g .fmap n x)
    coh : (n : Fin m) → (c : C .fst (fst n)) → Square (cong (CW↪ D (suc (fst n))) (hom (injectSuc n) c))
                                            (hom (fsuc n) (CW↪ C (fst n) c))
                                            (cong (CW↪ D (suc (fst n))) (f .fcomm n c))
                                            (cong (CW↪ D (suc (fst n))) (g .fcomm n c))

finiteCellHom-rel : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (f g : finCellMap m C D)
  (h∞ : (n : Fin (suc m)) (c : fst C (fst n))
    → Path (realise D) (incl (f .fmap n c)) (incl (g .fmap n c)))
  → Type (ℓ-max ℓ ℓ')
finiteCellHom-rel {C = C} {D = D} m f g h∞ =
  Σ[ ϕ ∈ finiteCellHom m f g ] ((n : Fin (suc m)) (x : fst C (fst n)) →
  Square (h∞ n x)
         (cong incl (finiteCellHom.hom ϕ n x))
         (push (f .fmap n x)) (push (g .fmap n x)))

-- The embedding of stage n into stage n+1 is (n+1)-connected
-- 2 calls to univalence in there
isConnected-CW↪ : (n : ℕ) (C : CWskel ℓ) → isConnectedFun n (CW↪ C n)
isConnected-CW↪ zero C x = isContrUnit*
isConnected-CW↪ (suc n) C =
  EquivJ (λ X E → isConnectedFun (suc n) (λ x → invEq E (inl x)))
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
isConnected-CW↪∞ : (n : ℕ) (C : CWskel ℓ) → isConnectedFun n (CW↪∞ C n)
isConnected-CW↪∞ zero C b = isContrUnit*
isConnected-CW↪∞ (suc n) C = isConnectedIncl∞ (realiseSeq C) (suc n) (suc n) subtr
  where
    subtr : (k : ℕ) → isConnectedFun (suc n) (CW↪ C (k +ℕ (suc n)))
    subtr k = isConnectedFunSubtr (suc n) k (CW↪ C (k +ℕ (suc n)))
                                   (isConnected-CW↪ (k +ℕ (suc n)) C)

-- -- We can merely fill n-spheres in (n+2)-connected spaces
-- module connectedSpace {A : Type ℓ} where
--   contractSphere : (n : ℕ) (HA : isConnected (suc (suc n)) A)
--     → (f : S₊ n → A)
--     →  ∃[ a ∈ A ] ((s : S₊ n) → f s ≡ a)
--   contractSphere zero HA f =
--     TR.rec squash₁
--       (λ p → ∣ (f true) , (λ { false → sym p ; true → refl}) ∣₁)
--       (Iso.fun (PathIdTruncIso _) (isContr→isProp HA ∣ f true ∣ₕ ∣ f false ∣ₕ))
--   contractSphere (suc n) HA f =
--     PT.map (λ p → (f (ptSn (suc n))) , funExt⁻ p) main-path
--     where
--     A⋆ : Pointed ℓ
--     A⋆ = A , f (ptSn (suc n))

--     π-iso : Iso (π' (suc n) A⋆) (π' (suc n) (Unit* , tt*))
--     π-iso =
--        compIso (fst (π'Gr≅πGr n A⋆))
--       (compIso (πTruncIso (suc n))
--       (compIso (invIso (fst (π'Gr≅πGr n (hLevelTrunc∙ (3 +ℕ n) A⋆))))
--                (equivToIso (π'Iso n (isoToEquiv (isContr→Iso HA isContrUnit*) , refl) .fst))))

--     contr-π : isContr (π' (suc n) A⋆)
--     contr-π = isOfHLevelRetractFromIso 0 π-iso
--              (∣ const∙ (S₊∙ (suc n)) _ ∣₂
--              , ST.elim (λ _ → isSetPathImplicit) λ f → refl)

--     main-path : ∥ f ≡ (λ _ → f (ptSn (suc n))) ∥₁
--     main-path =
--       PT.map (cong fst)
--       (Iso.fun PathIdTrunc₀Iso
--                  (isContr→isProp contr-π
--                    ∣ f , refl ∣₂ ∣ (λ _ → f (ptSn (suc n))) , refl ∣₂))

-- -- Now we are going to prove that connectedness is enough to lift a map from
-- -- stage n of the CW approximation to stage n+1
-- module connectedFunLifts {A : Type ℓ} {B : Type ℓ'}
--   (f : A → B) (n : ℕ) (Hf : isConnectedFun (suc (suc n)) f) where

--   -- contractions of spheres can be (merely) lifted along connected maps
--   contractSphere : (g : S₊ n → A) (b : B)
--     → (diskB : (s : S₊ n) → f (g s) ≡ b)
--     → ∥ Σ[ a ∈ A ] (Σ[ Ha ∈ f a ≡ b ] (Σ[ diskA ∈ ((s : S₊ n) → g s ≡ a) ]
--            ((s : S₊ n) → diskB s ≡ (cong f (diskA s) ∙ Ha)))) ∥₁
--   contractSphere g b diskB = PT.map aux (connectedSpace.contractSphere n (Hf b) (λ s → (g s , diskB s)))
--     where
--       aux : (Σ[ a ∈ fiber f b ] ((s : S₊ n) → (g s , diskB s) ≡ a)) →
--             Σ[ a ∈ A ] (Σ[ Ha ∈ f a ≡ b ] (Σ[ diskA ∈ ((s : S₊ n) → g s ≡ a) ]
--               ((s : S₊ n) → diskB s ≡ (cong f (diskA s) ∙ Ha))))
--       aux ((a , Ha) , c) = a , Ha , (λ s → fst (pathFiber f b (c s)))
--                          , (λ s → snd (pathFiber f b (c s)))

--   -- this also works for a finite amount of sphere contractions by Finite Choice
--   contractSpheres : (m : ℕ) (g : Fin m → S₊ n → A)
--     → (b : (k : Fin m) → B)
--     → (diskB : (k : Fin m) → (s : S₊ n) → f (g k s) ≡ b k)
--     → ∥ (Σ[ a ∈ (Fin m → A) ] ((k : Fin m) → Σ[ Ha ∈ f (a k) ≡ b k ]
--             (Σ[ diskA ∈ ((s : S₊ n) → g k s ≡ a k) ]
--             ((s : S₊ n) → diskB k s ≡ (cong f (diskA s) ∙ Ha))))) ∥₁
--   contractSpheres m g b diskB = invEq (_ , satAC∃Fin m (λ _ → A)
--     (λ k a → (Σ[ Ha ∈ f a ≡ b k ] (Σ[ diskA ∈ ((s : S₊ n) → g k s ≡ a) ]
--       ((s : S₊ n) → diskB k s ≡ (cong f (diskA s) ∙ Ha))))))
--     (λ k → contractSphere (g k) (b k) (diskB k))

--   -- this allows us to lift a map out of a pushout with spheres
--   module _ (X : Type ℓ'') (g : X → A) (m : ℕ) (α : Fin m × S₊ n → X)
--     (h : Pushout α fst → B) (comm : (x : X) → f (g x) ≡ h (inl x)) where

--     module _ (spheresContr : (Σ[ a ∈ (Fin m → A) ] ((k : Fin m) → Σ[ Ha ∈ f (a k) ≡ h (inr k) ]
--       (Σ[ diskA ∈ ((s : S₊ n) → g (α (k , s)) ≡ a k) ]
--       ((s : S₊ n) → comm (α (k , s)) ∙ (cong h (push (k , s))) ≡ (cong f (diskA s) ∙ Ha)))))) where

--       centerA : Fin m → A
--       centerA = fst spheresContr

--       HcenterA : (k : Fin m) → f (centerA k) ≡ h (inr k)
--       HcenterA = λ k → fst (snd spheresContr k)

--       diskA : (k : Fin m) → (s : S₊ n) → g (α (k , s)) ≡ centerA k
--       diskA = λ k → fst (snd (snd spheresContr k))

--       HdiskA : (k : Fin m) → (s : S₊ n) → comm (α (k , s)) ∙ (cong h (push (k , s))) ≡ (cong f (diskA k s) ∙' (HcenterA k))
--       HdiskA = λ k s → (snd (snd (snd spheresContr k)) s) ∙ (compPath≡compPath' (cong f (diskA k s)) (HcenterA k))

--       liftPushout-fun : Pushout α fst → A
--       liftPushout-fun (inl x) = g x
--       liftPushout-fun (inr a) = centerA a
--       liftPushout-fun (push (a , s) i) = diskA a s i

--       liftPushout-H1 : (x : X) → (g x ≡ liftPushout-fun (inl x))
--       liftPushout-H1 x = refl

--       liftPushout-H2 : (x : Pushout α fst) → f (liftPushout-fun x) ≡ h x
--       liftPushout-H2 (inl x) = comm x
--       liftPushout-H2 (inr a) = HcenterA a
--       liftPushout-H2 (push (a , s) i) j =
--         hcomp (λ k → λ { (i = i0) → compPath-filler (comm (α (a , s))) (cong h (push (a , s))) (~ k) j
--                        ; (i = i1) → compPath'-filler (cong f (diskA a s)) (HcenterA a) (~ k) j
--                        ; (j = i0) → f (diskA a s (i ∧ k))
--                        ; (j = i1) → h (push (a , s) (i ∨ (~ k))) })
--               (HdiskA a s i j)

--       -- pasting the two commutativity triangles gives the commutativity of the outer square
--       -- unused for now, probably useful later
--       liftPushout-H12 : (x : X) → comm x ≡ (cong f (liftPushout-H1 x) ∙ liftPushout-H2 (inl x))
--       liftPushout-H12 x = lUnit (comm x)

--       liftPushout-aux : Σ[ lift ∈ (Pushout α fst → A) ]
--         ((x : X) → g x ≡ lift (inl x)) × ((x : Pushout α fst) → f (lift x) ≡ h x)
--       liftPushout-aux = liftPushout-fun , liftPushout-H1 , liftPushout-H2

--     liftPushout : ∃[ lift ∈ (Pushout α fst → A) ]
--       ((x : X) → g x ≡ lift (inl x)) × ((x : Pushout α fst) → f (lift x) ≡ h x)
--     liftPushout = PT.map liftPushout-aux
--       (contractSpheres m (λ a s → g (α (a , s)))
--                          (λ k → h (inr k))
--                          (λ k s → comm (α (k , s)) ∙ cong h (push (k , s))))

--   -- which in turn, allows us to lift maps from a CW stage to the next one
--   module _ (C : CWskel ℓ'') (g : fst C (suc n) → A) where
--     An = snd C .fst
--     α = snd C .snd .fst
--     e₊ = snd C .snd .snd .snd

--     lifting-prop : (Y : Type ℓ'') (E : Y ≃ Pushout (α (suc n)) fst) → Type _
--     lifting-prop Y E = (h : Y → B) (comm : (x : fst C (suc n)) → f (g x) ≡ h (invEq E (inl x)))
--       → ∃[ lift ∈ (Y → A) ] ((x : fst C (suc n)) → g x ≡ lift (invEq E (inl x)))
--                             × ((x : Y) → f (lift x) ≡ h x)

--     liftCW : (h : fst C (suc (suc n)) → B)
--       (comm : (x : fst C (suc n)) → f (g x) ≡ h (CW↪ C (suc n) x))
--       → ∃[ lift ∈ (fst C (suc (suc n)) → A) ] ((x : fst C (suc n)) → g x ≡ lift (CW↪ C (suc n) x))
--                                         × ((x : fst C (suc (suc n))) → f (lift x) ≡ h x)
--     liftCW = EquivJ lifting-prop (liftPushout (fst C (suc n)) g (An (suc n)) (α (suc n))) (e₊ (suc n))

-- Cellular approximation
satAC∃Fin-C0 : (C : CWskel ℓ) → satAC∃ ℓ' ℓ'' (fst C 1)
satAC∃Fin-C0 {ℓ} {ℓ'} C =
  subst (satAC∃ _ _)
  (ua (compEquiv (invEquiv LiftEquiv) (invEquiv (CW₁-discrete C))))
    λ T c → isoToIsEquiv (iso _
      (λ f → PT.map (λ p → (λ { (lift x) → p .fst x})
                            , λ { (lift x) → p .snd x})
              (invEq (_ , t (T ∘ lift) (c ∘ lift)) (f ∘ lift)))
      (λ _ → (isPropΠ λ _ → squash₁) _ _)
      λ _ → squash₁ _ _)
  where
  open import Cubical.Foundations.Equiv
  asd = Lift
  t = InductiveFinSatAC∃ (snd C .fst 0)

module _ (C : CWskel ℓ) (D : CWskel ℓ') (f : realise C → realise D) where
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
          → fₙ (fsuc n) .fst (CW↪ C (fst n) c) ≡ CW↪ D (fst n) (fₙ (injectSuc n) .fst c))
  approx zero = ∣ (λ { (zero , p)
    → (λ x → ⊥.rec (CW₀-empty C x))
     , λ x → ⊥.rec (CW₀-empty C x)})
     , (λ {()}) ∣₁

  approx (suc zero) =
      PT.map (λ a1 →
        (λ { (zero , p) → (λ x → ⊥.rec (CW₀-empty C x))
                          , λ x → ⊥.rec (CW₀-empty C x)
           ; (suc zero , p) → a1})
           , λ {(zero , p) c → ⊥.rec (CW₀-empty C c)})
    approx₁
  approx (suc (suc m)) =
      PT.rec
      squash₁
      (λ {(p , f')
      → PT.rec squash₁ (λ r
        → PT.map (λ ind → FST p f' r ind
                          , SND p f' r ind)
          (mere-fib-f-coh (p flast .fst)
            r (p (suc m , <ᵗsucm) .snd)))
            (fst-lem (p flast .fst)
                     (p flast .snd))})
      (approx (suc m))
    where
    open CWskel-fields C
    F↓-big-ty : (n : ℕ) → Type _
    F↓-big-ty n = (c : fst C n) → Σ[ x ∈ fst D n ] incl x ≡ f (incl c)

    fst-lem : (fm : fst C (suc m) → fst D (suc m))
      → ((c : fst C (suc m)) → incl (fm c) ≡ f (incl c))
      → ∥ ((x : A (suc m)) (y : S₊ m) →
                       CW↪ D (suc m) (fm (α (suc m) (x , y)))
                     ≡ CW↪ D (suc m) (fm (α (suc m) (x , ptSn m)))) ∥₁
    fst-lem fm fh =
      invEq propTrunc≃Trunc1
       (invEq (_ , InductiveFinSatAC 1 (CWskel-fields.card C (suc m)) _) λ a →
         fst propTrunc≃Trunc1
           (sphereToTrunc m λ y →
             TR.map fst (isConnectedCong _ _ (isConnected-CW↪∞ (suc (suc m)) D)
                     (sym (push _)
                     ∙ (fh (CWskel-fields.α C (suc m) (a , y))
                     ∙ cong f (push _
                            ∙ cong incl (cong (invEq (CWskel-fields.e C (suc m)))
                               (push (a , y) ∙ sym (push (a , ptSn m))))
                            ∙ sym (push _))
                     ∙ sym (fh (CWskel-fields.α C (suc m) (a , ptSn m))))
                     ∙ push _) .fst)))
    module _ (fm : fst C (suc m) → fst D (suc m))
             (fm-coh : (x : A (suc m)) (y : S₊ m) →
                       CW↪ D (suc m) (fm (α (suc m) (x , y)))
                     ≡ CW↪ D (suc m) (fm (α (suc m) (x , ptSn m))))
             where
      F↓ : fst C (suc (suc m)) → fst D (suc (suc m))
      F↓ = CWskel-elim C (suc m) (CW↪ D (suc m) ∘ fm) (λ x → CW↪ D (suc m) (fm (α (suc m) (x , ptSn m))))
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
          (invEq (_ , InductiveFinSatAC 1 (card (suc m)) _)
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
        F↓-big = CWskel-elim C (suc m) (fib-f-l ind) (fib-f-r ind) ind2

        F↓' : (c : fst C (suc m)) → F↓-big (CW↪ C (suc m) c) ≡ fib-f-l ind c
        F↓' = CWskel-elim-inl C (suc m) (fib-f-l ind) (fib-f-r ind) ind2

        F↓'-gen-coh : (c : fst C (suc m))
          → F↓-big (CW↪ C (suc m) c) .fst
          ≡ CW↪ D (suc m) (fm c)
        F↓'-gen-coh c = cong fst (F↓' c)

    module _ (p : (n : Fin (suc (suc m)))
        → Σ[ h ∈ (fst C (fst n) → fst D (fst n)) ]
            ((c : fst C (fst n)) → incl (h c) ≡ f (incl c)))
      (f' : (n : Fin (suc m)) (c : fst C (fst n))
         → p (fsuc n) .fst (CW↪ C (fst n) c) ≡
            CW↪ D (fst n) (p (injectSuc n) .fst c))
      (r : (n : A (suc m)) (y : S₊ m) →
            CW↪ D (suc m) (p flast .fst (α (suc m) (n , y)))
          ≡ CW↪ D (suc m) (p flast .fst (α (suc m) (n , ptSn m))))
      (ind : (n : Fin _) (y : S₊ m) →
             PathP
             (λ i →
                fib-f-incl (p flast .fst) r (p flast .snd)
                (invEq (e (suc m)) (push (n , y) i)))
             (fib-f-l (p flast .fst) r (p flast .snd)
              (α (suc m) (n , y)))
             (fib-f-r (p flast .fst) r (p flast .snd) n)) where

      FST-base : Σ[ h ∈ (fst C (suc (suc m)) → fst D (suc (suc m))) ]
          ((c : fst C (suc (suc m))) → incl (h c) ≡ f (incl c))
      fst FST-base = fst ∘ F↓-big _ _ _ ind
      snd FST-base = snd ∘ F↓-big _ _ _ ind

      GT : (n : Fin (suc (suc (suc m)))) → Type _
      GT n = Σ[ h ∈ (fst C (fst n) → fst D (fst n)) ]
          ((c : fst C (fst n)) → incl (h c) ≡ f (incl c))

      FST : (n : Fin (suc (suc (suc m)))) → GT n
      FST = elimFin FST-base p

      SND : (n : Fin (suc (suc m))) (c : fst C (fst n))
        → FST (fsuc n) .fst (CW↪ C (fst n) c)
        ≡ CW↪ D (fst n) (FST (injectSuc n) .fst c)
      SND = elimFin (λ c
        → funExt⁻ (cong fst (elimFinβ {A = GT} FST-base p .fst)) (CW↪ C (suc m) c)
        ∙ F↓'-gen-coh _ _ _ ind c
        ∙ cong (CW↪ D (suc m))
          (sym (funExt⁻ (cong fst (elimFinβ {A = GT} FST-base p .snd flast)) c)))
        λ x c
         → funExt⁻ (cong fst (elimFinβ {A = GT}
              FST-base p .snd (fsuc x))) (CW↪ C (fst x) c)
          ∙ f' x c
          ∙ cong (CW↪ D (fst x))
              (sym (funExt⁻ (cong fst
               ((elimFinβ {A = GT} FST-base p .snd) (injectSuc x))) c))


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


open import Cubical.Algebra.ChainComplex
open import Cubical.Data.FinSequence
open FinSequenceMap

finCellMap→FinSeqColim : (C : CWskel ℓ) (D : CWskel ℓ')
  {m : ℕ} → finCellMap m C D → FinSeqColim m (realiseSeq C) → FinSeqColim m (realiseSeq D) 
finCellMap→FinSeqColim C D {m = m} f (fincl n x) = fincl n (fmap f n x)
finCellMap→FinSeqColim C D {m = m} f (fpush n x i) =
  (fpush n (fmap f (injectSuc n) x) ∙ cong (fincl (fsuc n)) (fcomm f n x)) i


finCellApprox : (C : CWskel ℓ) (D : CWskel ℓ') (f : realise C → realise D) (m : ℕ) → Type (ℓ-max ℓ ℓ') 
finCellApprox C D f m =
  Σ[ ϕ ∈ finCellMap m C D ]
    (FinSeqColim→Colim m {X = realiseSeq D} ∘ finCellMap→FinSeqColim C D ϕ
       ≡ f ∘ FinSeqColim→Colim m {X = realiseSeq C})

-- realiseFinCellMap : {C : CWskel ℓ} {D : CWskel ℓ'}
--   (m : ℕ) (ϕ : finCellMap m C D)
--   → {!<!}
-- realiseFinCellMap = {!!}

-- sndField→finColim : (C : CWskel ℓ) (D : CWskel ℓ')
--   (f : realise C → realise D) (m : ℕ) (ϕ : finCellMap m C D)
--   → ((n : Fin (suc m)) (c : fst C (fst n)) → incl (fmap ϕ n c) ≡ f (incl c))
--   → (x : FinSeqColim m (realiseSeq C)) → incl (fmap ϕ {!fmap ϕ!} {!!}) ≡ f (FinSeqColim→Colim _ x)
-- sndField→finColim = {!!}

CWmap→finCellMap : (C : CWskel ℓ) (D : CWskel ℓ') (f : realise C → realise D) (m : ℕ)
  → ∥ finCellApprox C D f m ∥₁
CWmap→finCellMap C D f m =
  PT.map (λ {(g , hom)
  → (record { fmap = fst ∘ g ; fcomm = λ r x → sym (hom r x) })
   , →FinSeqColimHomotopy _ _ (g flast .snd)})
     (approx C D f m)

-- module _ (m : ℕ) (C : finCWskel ℓ m) (D : finCWskel ℓ' m)
--   (f : realise (finCWskel→CWskel m C) → realise (finCWskel→CWskel m D)) where

--   approxFinCw : ∃[ fₙ ∈ ((n : ℕ) → Σ[ f' ∈ (fst C n → fst D n) ] ((c : _) → incl (f' c) ≡ f (incl c))) ]
--                  ((n : ℕ) (c : fst C n) → fₙ (suc n) .fst (CW↪ (finCWskel→CWskel m C) n c)
--                                            ≡ CW↪ (finCWskel→CWskel m D) n (fₙ n .fst c))
--   approxFinCw =
--     PT.map (λ appr → (λ n → (f-full (fst ∘ fst appr) (snd appr) n )
--                             , f-full-coh' _ _ (snd ∘ fst appr) n)
--                             , (f-coh-full (fst ∘ fst appr) (snd appr)))
--            (approx (finCWskel→CWskel m C) (finCWskel→CWskel m D) f (suc m))
--     where
--     module _ (fbase : (n : Fin (suc (suc m))) → fst C (fst n) → fst D (fst n))
--              (fcoh : (n : Fin (suc m)) (c : fst C (fst n))
--                   → fbase (fsuc n) (CW↪ (finCWskel→CWskel m C) (fst n) c)
--                    ≡ CW↪ (finCWskel→CWskel m D) (fst n) (fbase (injectSuc n) c)) where

--       C≃ : (a : ℕ) → fst C (a +ℕ m) ≃ fst C (suc (a +ℕ m))
--       C≃ a = _ , C .snd .snd a

--       D≃ : (a : ℕ) → fst D (a +ℕ m) ≃ fst D (suc (a +ℕ m))
--       D≃ a = _ , D .snd .snd a

--       f-extend : (a : ℕ) → fst C (a +ℕ m) → fst D (a +ℕ m)
--       f-extend zero = fbase (m , (1 , refl))
--       f-extend (suc a) c = fst (D≃ a) (f-extend a (invEq (C≃ a) c))

--       f-extend-comm : (x n : ℕ) (p : x +ℕ m ≡ n) (t : fst C n)
--         → subst (fst D) (cong suc p)
--                 (f-extend (suc x)
--                   (subst (fst C) (sym (cong suc p)) (CW↪ (finCWskel→CWskel m C) n t)))
--          ≡ CW↪ (finCWskel→CWskel m D) n (subst (fst D) p (f-extend x (subst (fst C) (sym p) t)))
--       f-extend-comm x = J> λ t →
--           transportRefl _
--         ∙ cong (CW↪ (finCWskel→CWskel m D) (x +ℕ m))
--             (sym (transportRefl _
--             ∙ cong (f-extend x) (transportRefl _
--               ∙ sym (cong (invEq (C≃ x)) (transportRefl _)
--                     ∙ retEq (C≃ x) t))))

--       ≤-lem : (n : ℕ) → suc n ≤ m → suc n ≤ suc (suc m)
--       ≤-lem n x = suc (suc (fst x)) , (cong (2 +ℕ_) (snd x))

--       f-full : (n : ℕ) → fst C n → fst D n
--       f-full n with (Dichotomyℕ m n)
--       ... | inl x = subst (λ n → fst C n → fst D n) (snd x)
--                           (f-extend (fst x))
--       ... | inr x = fbase (n , ≤-lem n x)

--       f-full-coh' : (ind : (a : Fin (suc (suc m))) (c : fst (finCWskel→CWskel m C) (fst a))
--                     → incl (fbase a c) ≡ f (incl c))
--             (n : ℕ) (c : fst C n) → incl (f-full n c) ≡ f (incl c)
--       f-full-coh' ind n c with Dichotomyℕ m n
--       ... | inl (a , p) = help2 a n p c
--         where
--         lem2 : (a : ℕ) (c : fst C (a +ℕ m))
--           → incl (f-extend a c) ≡ f (incl c)
--         lem2 zero c = ind (m , 1 , refl) c
--         lem2 (suc a) c =
--             sym (push _)
--           ∙ lem2 a (invEq (C≃ a) c)
--           ∙ cong f (push (invEq (C≃ a) c)
--           ∙ cong incl (secEq (C≃ a) c))

--         help2 : (a n : ℕ) (p : a +ℕ m ≡ n) (c : fst C n)
--               → incl (subst (λ n₁ → fst C n₁ → fst D n₁) p (f-extend a) c)
--                ≡ f (incl c)
--         help2 a = J> λ c → cong incl (λ j → transportRefl (f-extend a) j c)
--                 ∙ lem2 a c
--       ... | inr x = ind (n , ≤-lem n x) c

--       f-coh-full : (n : ℕ) (c : fst C n)
--         → f-full (suc n) (CW↪ (finCWskel→CWskel m C) n c)
--          ≡ CW↪ (finCWskel→CWskel m D) n (f-full n c)
--       f-coh-full n c with (Dichotomyℕ m n) | (Dichotomyℕ m (suc n))
--       ... | inl x | inl x₁ =
--            cong (λ x₁ → subst (λ n₁ → fst C n₁ → fst D n₁) (snd x₁) (f-extend (fst x₁))
--                 (CW↪ (finCWskel→CWskel m C) n c)) (isProp≤ x₁ (suc (fst x) , cong suc (snd x)))
--          ∙ f-extend-comm _ _ (snd x) c
--       ... | inl x | inr x₁ = ⊥.rec (¬-suc-n<n (<≤-trans x₁ x))
--       ... | inr x | inl (zero , p) =
--           (λ i → transp (λ j → fst D (p (j ∨ i))) i
--                   (fbase (p i , 1 , (λ j → suc (suc (p (~ j ∧ i)))))
--                    (transp (λ j → fst C (p (~ j ∨ i))) i
--                      (CW↪ (finCWskel→CWskel m C) n c))))
--         ∙ cong (λ w → fbase (suc n , w) (CW↪ (finCWskel→CWskel m C) n c))
--                (isProp≤ _ _)
--         ∙ fcoh (n , suc (fst x) , cong suc (snd x)) c
--         ∙ cong (CW↪ (finCWskel→CWskel m D) n)
--             (cong (λ w → fbase (n , w) c) (isProp≤ _ _))
--       ... | inr x | inl (suc diff , p) = ⊥.rec (¬m<m (<≤-trans x (diff , cong predℕ p)))
--       ... | inr x | inr x₁ = cong (λ w → fbase (suc n , w) (CW↪ (finCWskel→CWskel m C) n c)) (isProp≤ _ _)
--                           ∙∙ fcoh (n , ≤-trans x (1 , refl)) c
--                           ∙∙ cong (CW↪ (finCWskel→CWskel m D) n)
--                               (cong (λ w → fbase (n , w) c) (isProp≤ _ _))


module SeqHomotopyTypes {ℓ ℓ'} {C : Sequence ℓ} {D : Sequence ℓ'} (m : ℕ)
  (f-c g-c : FinSequenceMap (Sequence→FinSequence m C) (Sequence→FinSequence m D))
  where

  f = fmap f-c
  g = fmap g-c
  f-hom = fcomm f-c
  g-hom = fcomm g-c

  cell-hom : (n : Fin (suc m)) (c : obj C (fst n)) → Type ℓ'
  cell-hom n c = Sequence.map D (f n c) ≡ Sequence.map D (g n c)

  cell-hom-coh : (n : Fin m) (c : obj C (fst n))
    → cell-hom (injectSuc n) c → cell-hom (fsuc n) (Sequence.map C c) → Type ℓ'
  cell-hom-coh n c h h' =
    Square (cong (Sequence.map D) h) h'
           (cong (Sequence.map D) (f-hom n c))
           (cong (Sequence.map D) (g-hom n c))


  h∞Type : Type _
  h∞Type = (n : Fin (suc m)) (c : obj C (fst n)) → Path (SeqColim D) (incl (f n c)) (incl (g n c))

  agrees-in-lim : (h∞ : h∞Type)  {n : Fin m}
    (x : obj C (fst n)) (h : cell-hom (injectSuc n) x) → Type ℓ'
  agrees-in-lim  h∞ {n = n} x h =
     Square (h∞ (injectSuc n) x)
            (cong incl h)
            (push (f (injectSuc n) x)) (push (g (injectSuc n) x))

  goalTypeFin : Type _
  goalTypeFin =
    Σ[ hₙ ∈ ((n : Fin (suc m)) (c : obj C (fst n)) → cell-hom n c) ]
       ((n : Fin m) (c : obj C (fst n))
         → cell-hom-coh n c
             (hₙ (injectSuc n) c)
             (hₙ (fsuc n) (Sequence.map C c)))


{-


  goalType : Type _
  goalType =
    Σ[ hₙ ∈ ((n : ℕ) (c : obj C n)
       → (cell-hom n c)) ]
            ((n : ℕ) (c : obj C n)
              → cell-hom-coh n c
                (hₙ n c) (hₙ (suc n) (Sequence.map C c)))
-}

-- homotopy in colimit → cellular homotopy
-- finCellMap→goodApprox : (C : CWskel ℓ) (D : CWskel ℓ') (f : realise C → realise D) (m : ℕ)
--   → (f-c g-c : approxTy C D f m)
--     → Σ[ h ∈ ((n : Fin (suc m)) (c : fst C (fst n))
--       → Path (realise D) (incl (fmap (fst f-c) n c)) (incl (fmap (fst g-c) n c)) ) ]
--              ((n : Fin m) (c : fst C (fst n))
--                → Square
--                    (push (fmap (fst f-c) (injectSuc n) c) ∙ cong incl (fcomm (fst f-c) n c))
--                    (push (fmap (fst g-c) (injectSuc n) c) ∙ cong incl (fcomm (fst g-c) n c))
--                    (h (injectSuc n) c)
--                    (h (fsuc n) (CW↪ C (fst n) c)))
-- fst (finCellMap→goodApprox C D f m f-c g-c) a c = snd f-c a c ∙∙ refl ∙∙ sym (snd g-c a c)
-- snd (finCellMap→goodApprox C D f m f-c g-c) n c = {!isConnected!}

module approkz {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ) (f-c g-c : finCellMap m C D)
         (h∞-lift : FinSeqColim→Colim m ∘ finCellMap→FinSeqColim C D f-c
          ≡ FinSeqColim→Colim m ∘ finCellMap→FinSeqColim C D g-c) where
  open SeqHomotopyTypes m f-c g-c
  open CWskel-fields C


  -- h∞-lift : FinSeqColim→Colim m ∘ finCellMap→FinSeqColim C D f-c
  --         ≡ FinSeqColim→Colim m ∘ finCellMap→FinSeqColim C D g-c
  -- h∞-lift = →FinSeqColimHomotopy _ _ λ s → h∞' _

  h∞ : (n : Fin (suc m)) (c : fst C (fst n))
        → Path (realise D) (incl (fmap f-c n c)) (incl (fmap g-c n c))
  h∞ n c = funExt⁻ h∞-lift (fincl n c)

  pathToCellularHomotopy₁ : (t : 1 <ᵗ suc m) (c : fst C 1) 
    → ∃[ h ∈ cell-hom (1 , t) c ]
         Square (h∞ (1 , t) c)
                (cong incl h)
                (push (f (1 , t) c))
                (push (g (1 , t) c))
  pathToCellularHomotopy₁ t c =
    TR.rec squash₁
      (λ {(d , p)
      → ∣ d
      , (λ i j
      → hcomp (λ k →
           λ {(i = i0) → doubleCompPath-filler
                            (sym (push (f (1 , t) c)))
                            (h∞ _ c)
                            (push (g (1 , t) c)) (~ k) j
            ; (i = i1) → incl (d j)
            ; (j = i0) → push (f (1 , t) c) (~ k ∨ i)
            ; (j = i1) → push (g (1 , t) c) (~ k ∨ i)})
              (p (~ i) j)) ∣₁})
    (isConnectedCong 1 (CW↪∞ D 2)
      (isConnected-CW↪∞ 2 D) h∞* .fst)
    where
    h∞* : CW↪∞ D 2 (CW↪ D 1 (f (1 , t) c)) ≡ CW↪∞ D 2 (CW↪ D 1 (g (1 , t) c))
    h∞* = sym (push (f (1 , t) c)) ∙∙ h∞ _ c ∙∙ push (g (1 , t) c)

  -- induction step
  pathToCellularHomotopy-ind : (n : Fin m)
    → (hₙ : (c : fst C (fst n)) → Σ[ h ∈ cell-hom (injectSuc n) c ]
                                     (Square (h∞ (injectSuc n) c)
                                            (cong incl h)
                                            (push (f (injectSuc n) c))
                                            (push (g (injectSuc n) c))))
    → ∃[ hₙ₊₁ ∈ ((c : fst C (suc (fst n)))
                → Σ[ h ∈ cell-hom (fsuc n) c ]
                     (Square (h∞ (fsuc n) c)
                             (cong incl h)
                             (push (f (fsuc n) c))
                             (push (g (fsuc n) c)))) ]
                    ((c : _) → cell-hom-coh n c (hₙ c .fst)
                                  (hₙ₊₁ (CW↪ C (fst n) c) .fst))
  
  pathToCellularHomotopy-ind (zero ,  q) ind =
    fst (propTrunc≃ (isoToEquiv (compIso (invIso rUnit×Iso)
      (Σ-cong-iso-snd
        λ _ → isContr→Iso isContrUnit
        ((λ x → ⊥.rec (CW₀-empty C x))
       , λ t → funExt λ x → ⊥.rec (CW₀-empty C x))))))
       (invEq propTrunc≃Trunc1
         (invEq (_ , satAC-CW₁ 1 C _)
           λ c → fst propTrunc≃Trunc1
             (pathToCellularHomotopy₁ (fsuc (zero , q) .snd) c)))
  pathToCellularHomotopy-ind (suc n' , w) ind =
    PT.map (λ q → hₙ₊₁ q , hₙ₊₁-coh q) Πfiber-cong²-hₙ₊₁-push∞
    where
    n : Fin m
    n = (suc n' , w)
    Pushout→C = invEq (e (suc n'))

    hₙ'-filler : (x : fst C (suc n')) → _
    hₙ'-filler x =
      doubleCompPath-filler
            (sym (f-hom n x))
            (ind x .fst)
            (g-hom n x)

    hₙ' : (x : fst C (suc n'))
      → f (fsuc n) (CW↪ C (suc n') x)
       ≡ g (fsuc n) (CW↪ C (suc n') x)
    hₙ' x = hₙ'-filler x i1

    -- homotopy for inl
    hₙ₊₁-inl : (x : fst C (suc n'))
      → cell-hom (fsuc n) (invEq (e (suc n')) (inl x))
    hₙ₊₁-inl x = cong (CW↪ D (suc (suc n'))) (hₙ' x)

    -- hₙ₊₁-inl coherent with h∞
    h∞-push-coh : (x : fst C (suc n'))
      → Square (h∞ (injectSuc n) x) (h∞ (fsuc n) (CW↪ C (fst n) x))
                (push (f (injectSuc n) x) ∙ (λ i₁ → incl (f-hom n x i₁)))
                (push (g (injectSuc n) x) ∙ (λ i₁ → incl (g-hom n x i₁)))
    h∞-push-coh x i j =
      hcomp (λ k
        → λ {(i = i0) → h∞-lift j (fincl (injectSuc n) x)
            ; (i = i1) → h∞-lift j (fincl (fsuc n) (CW↪ C (fst n) x))
            ; (j = i0) → cong-∙ (FinSeqColim→Colim m)
                                 (fpush n (f (injectSuc n) x))
                                 (λ i₁ → fincl (fsuc n) (f-hom n x i₁)) k i
            ; (j = i1) → cong-∙ (FinSeqColim→Colim m)
                                 (fpush n (g (injectSuc n) x))
                                 (λ i₁ → fincl (fsuc n) (g-hom n x i₁)) k i})
            (h∞-lift j (fpush n x i))

    hₙ₊₁-inl-coh : (x : fst C (fst n))
      → Square (h∞ (fsuc n) (invEq (e (fst n)) (inl x)))
                (cong incl (hₙ₊₁-inl x))
                (push (f (fsuc n) (invEq (e (fst n)) (inl x))))
                (push (g (fsuc n) (invEq (e (fst n)) (inl x))))
    hₙ₊₁-inl-coh x i j =
      hcomp (λ k
        → λ {(i = i0) → h∞ (fsuc n) (CW↪ C (fst n) x) j
            ; (i = i1) → push (hₙ' x j) k
            ; (j = i0) → push (f (fsuc n) (CW↪ C (fst n) x)) (k ∧ i)
            ; (j = i1) → push (g (fsuc n) (CW↪ C (fst n) x)) (k ∧ i)})
       (hcomp (λ k
         → λ {(i = i0) → h∞-push-coh x k j
             ; (i = i1) → incl (hₙ'-filler x k j)
             ; (j = i0) → compPath-filler'
                             (push (f (injectSuc n) x))
                             ((λ i₁ → incl (f-hom n x i₁))) (~ i) k
             ; (j = i1) → compPath-filler'
                             (push (g (injectSuc n) x))
                             ((λ i₁ → incl (g-hom n x i₁))) (~ i) k})
           (ind x .snd i j))

    module _ (x : A (suc n')) (y : S₊ n') where
      push-path-filler : I → I → Pushout (α (suc n')) fst
      push-path-filler i j =
        compPath-filler'' (push (x , y)) (sym (push (x , ptSn n'))) i j

      push-path :
        Path (Pushout (α (suc n')) fst)
             (inl (α (suc n') (x , y)))
             (inl (α (suc n') (x , ptSn n')))
      push-path j = push-path-filler i1 j

      D∞PushSquare : Type ℓ'
      D∞PushSquare =
        Square {A = realise D}
          (cong (CW↪∞ D (suc (suc (suc n'))))
            (hₙ₊₁-inl (snd C .snd .fst (suc n') (x , y))))
          (cong (CW↪∞ D (suc (suc (suc n'))))
            (hₙ₊₁-inl (snd C .snd .fst (suc n') (x , ptSn n'))))
          (λ i → incl (CW↪ D (suc (suc n'))
                        (f (fsuc n) (Pushout→C (push-path i)))))
          (λ i → incl (CW↪ D (suc (suc n'))
                        (g (fsuc n) (Pushout→C (push-path i)))))

      cong² : PathP (λ i → cell-hom (fsuc n)
                             (Pushout→C (push-path i)))
                    (hₙ₊₁-inl (α (suc n') (x , y)))
                    (hₙ₊₁-inl (α (suc n') (x , ptSn n')))
            → D∞PushSquare
      cong² p i j = incl (p i j)

      isConnected-cong² : isConnectedFun (suc n') cong²
      isConnected-cong² =
        isConnectedCong² (suc n') (CW↪∞ D (3 +ℕ n'))
          (isConnected-CW↪∞ (3 +ℕ n') D)

      hₙ₊₁-push∞ : D∞PushSquare
      hₙ₊₁-push∞ i j =
        hcomp (λ k
        → λ {(i = i0) → hₙ₊₁-inl-coh (α (suc n') (x , y)) k j
            ; (i = i1) → hₙ₊₁-inl-coh (α (suc n') (x , ptSn n')) k j
            ; (j = i0) → push (f (fsuc n) (Pushout→C (push-path i))) k
            ; (j = i1) → push (g (fsuc n) (Pushout→C (push-path i))) k})
        (hcomp (λ k
         → λ {(i = i0) → h∞-lift j (fincl (fsuc n)
                            (Pushout→C (push (x , y) (~ k))))
             ; (i = i1) → h∞-lift j (fincl (fsuc n)
                            (Pushout→C (push (x , ptSn n') (~ k))))
             ; (j = i0) → incl (f (fsuc n)
                                 (Pushout→C (push-path-filler k i)))
             ; (j = i1) → incl (g (fsuc n)
                                 (Pushout→C (push-path-filler k i)))})
         (h∞-lift j (fincl (fsuc n) (Pushout→C (inr x)))))

      fiber-cong²-hₙ₊₁-push∞ : hLevelTrunc (suc n') (fiber cong² hₙ₊₁-push∞)
      fiber-cong²-hₙ₊₁-push∞ = isConnected-cong² hₙ₊₁-push∞ .fst

      hₙ₊₁-coh∞ : (q : fiber cong² hₙ₊₁-push∞)
        → Cube (hₙ₊₁-inl-coh (α (suc n') (x , y)))
                (hₙ₊₁-inl-coh (α (suc n') (x , ptSn n')))
                (λ j k → h∞-lift k (fincl (fsuc n) (Pushout→C (push-path j))))
                (λ j k → incl (fst q j k))
                (λ j i → push (f (fsuc n) (Pushout→C (push-path j))) i)
                λ j i → push (g (fsuc n) (Pushout→C (push-path j))) i
      hₙ₊₁-coh∞ q j i k =
        hcomp (λ r
          → λ {(i = i0) → h∞-lift k (fincl (fsuc n) (Pushout→C (push-path j)))
              ; (i = i1) → q .snd (~ r) j k
              ; (j = i0) → hₙ₊₁-inl-coh (α (suc n') (x , y)) i k
              ; (j = i1) → hₙ₊₁-inl-coh (α (suc n') (x , ptSn n')) i k
              ; (k = i0) → push (f (fsuc n) (Pushout→C (push-path j))) i
              ; (k = i1) → push (g (fsuc n) (Pushout→C (push-path j))) i})
         (hcomp (λ r
           → λ {(i = i0) → h∞-lift k (fincl (fsuc n) (Pushout→C (push-path j)))
               ; (j = i0) → hₙ₊₁-inl-coh (α (suc n') (x , y)) (i ∧ r) k
               ; (j = i1) → hₙ₊₁-inl-coh (α (suc n') (x , ptSn n')) (i ∧ r) k
               ; (k = i0) → push (f (fsuc n)
                               (Pushout→C (push-path j))) (i ∧ r)
               ; (k = i1) → push (g (fsuc n)
                               (Pushout→C (push-path j))) (i ∧ r)})
          (hcomp (λ r
            → λ {(i = i0) → h∞-lift k (fincl (fsuc n) (Pushout→C (push-path-filler r j)))
                ; (j = i0) → h∞-lift k (fincl (fsuc n) (invEq (e (suc n'))
                                    (push (x , y) (~ r))))
                ; (j = i1) → h∞-lift k (fincl (fsuc n) (invEq (e (suc n'))
                                    (push (x , ptSn n') (~ r))))
                ; (k = i0) → incl (f (fsuc n)
                               (Pushout→C (push-path-filler r j)))
                ; (k = i1) → incl (g (fsuc n)
                               (Pushout→C (push-path-filler r j)))})
            (h∞-lift k (fincl (fsuc n) (Pushout→C (inr x))))))

    Πfiber-cong²-hₙ₊₁-push∞ :
      ∥ ((x : _) (y : _) → fiber (cong² x y) (hₙ₊₁-push∞ x y)) ∥₁
    Πfiber-cong²-hₙ₊₁-push∞ =
      Iso.inv propTruncTrunc1Iso
        (invEq (_ , InductiveFinSatAC 1 _ _)
        λ x → Iso.fun propTruncTrunc1Iso
                (sphereToTrunc n' (fiber-cong²-hₙ₊₁-push∞ x)))

    module _ (q : (x : Fin (fst (snd C) (suc n'))) (y : S₊ n')
                → fiber (cong² x y) (hₙ₊₁-push∞ x y)) where
      agrees : (x : fst C (suc n')) (ϕ : cell-hom (fsuc n) (CW↪ C (suc n') x))
        → Type _
      agrees x ϕ = Square (h∞ (fsuc n) (CW↪ C (suc n') x))
            (cong incl ϕ)
            (push (f (fsuc n) (CW↪ C (suc n') x)))
            (push (g (fsuc n) (CW↪ C (suc n') x)))

      main-inl : (x : fst C (suc n'))
        → Σ (cell-hom (fsuc n) (CW↪ C (suc n') x))
             (agrees x)
      main-inl x = hₙ₊₁-inl x , hₙ₊₁-inl-coh x

      main-push : (x : A (suc n')) (y : S₊ n')
        → PathP (λ i → Σ[ ϕ ∈ (cell-hom (fsuc n) (Pushout→C (push-path x y i))) ]
                 (Square (h∞ (fsuc n) (Pushout→C (push-path x y i)))
                                (λ j → incl (ϕ j))
                                (push (f (fsuc n) (Pushout→C (push-path x y i))))
                                (push (g (fsuc n) (Pushout→C (push-path x y i))))))
                 (main-inl (α (suc n') (x , y)))
                 (main-inl (α (suc n') (x , ptSn n')))
      main-push x y = ΣPathP (fst (q x y) , hₙ₊₁-coh∞ x y (q x y))

      hₙ₊₁ : (c : fst C (fst (fsuc n)))
        → Σ[ ϕ ∈ (cell-hom (fsuc n) c) ]
            Square (h∞ (fsuc n) c)
            (cong incl ϕ)
            (push (f (fsuc n) c))
            (push (g (fsuc n) c))
      hₙ₊₁ = CWskel-elim' C n' main-inl main-push

      hₙ₊₁-coh-pre : (c : fst C (suc n')) →
        Square (cong (CW↪ D (suc (suc n'))) (ind c .fst))
               (hₙ₊₁-inl c)
               (cong (CW↪ D (suc (suc n'))) (f-hom n c))
               (cong (CW↪ D (suc (suc n'))) (g-hom n c))
      hₙ₊₁-coh-pre c i j = CW↪ D (suc (suc n')) (hₙ'-filler c i j)

      hₙ₊₁-coh : (c : fst C (suc n')) →
        Square (cong (CW↪ D (suc (suc n'))) (ind c .fst))
               (hₙ₊₁ (CW↪ C (suc n') c) .fst)
               (cong (CW↪ D (suc (suc n'))) (f-hom n c))
               (cong (CW↪ D (suc (suc n'))) (g-hom n c))
      hₙ₊₁-coh c = hₙ₊₁-coh-pre c
        ▷ λ i → CWskel-elim'-inl C n'
                  {B = λ c → Σ[ ϕ ∈ cell-hom (fsuc n) c ]
                    Square (h∞ (fsuc n) c)  (cong incl ϕ)
                      (push (f (fsuc n) c)) (push (g (fsuc n) c))}
                  main-inl main-push c (~ i) .fst

-- finiteCellHom-rel

fsuc-agree : {m : ℕ} (n : Fin m)
  → Path (Fin (suc (suc m))) (fsuc (injectSuc n)) (injectSuc (fsuc n))
fsuc-agree = λ _ → Σ≡Prop (λ _ → isProp<ᵗ) refl

finCellMapLower : {C : CWskel ℓ} {D : CWskel ℓ'} {m : ℕ}
  (f : finCellMap (suc m) C D) → finCellMap m C D
fmap (finCellMapLower {m = m} f) n = fmap f (injectSuc n)
fcomm (finCellMapLower {C = C} {D = D} {m = suc m} f) n x = fcomm f (injectSuc n) x


pathToCellularHomotopy-main :
  {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ) (f-c g-c : finCellMap m C D)
  (h∞-lift : FinSeqColim→Colim m ∘ finCellMap→FinSeqColim C D f-c
          ≡ FinSeqColim→Colim m ∘ finCellMap→FinSeqColim C D g-c)
  → ∥ finiteCellHom-rel m f-c g-c (approkz.h∞ m f-c g-c h∞-lift) ∥₁
pathToCellularHomotopy-main {C = C} zero f-c g-c h∞' =
  ∣ (record { hom = λ {(zero , p) x → ⊥.rec (CW₀-empty C x)}
            ; coh = λ {()} })
            , (λ { (zero , p) x → ⊥.rec (CW₀-empty C x)}) ∣₁
pathToCellularHomotopy-main {C = C} {D = D} (suc zero) f-c g-c h∞' =
  PT.map (λ {(d , h) → (record { hom = λ {(zero , p) x → ⊥.rec (CW₀-empty C x)
                    ; (suc zero , p) → d}
            ; coh = λ {(zero , p) → λ x → ⊥.rec (CW₀-empty C x)} })
            , (λ {(zero , p) x → ⊥.rec (CW₀-empty C x)
                ; (suc zero , tt) → h})}) (invEq (_ , satAC∃Fin-C0 C _ _) k)
  where
  k : (c : _) → _
  k c = (approkz.pathToCellularHomotopy₁ (suc zero) f-c g-c
                 h∞' tt c)
pathToCellularHomotopy-main {C = C} {D = D} (suc (suc m)) f-c g-c h∞' =
  PT.rec squash₁
    (λ ind → PT.map
      (λ {(f , p) →
       (record { hom = main-hom ind f p
               ; coh = main-coh ind f p })
               , ∞coh ind f p})
      (pathToCellularHomotopy-ind flast
        λ c → (finiteCellHom.hom (ind .fst) flast c)
            , (ind .snd flast c)))
    (pathToCellularHomotopy-main {C = C} {D = D} (suc m)
          (finCellMapLower f-c)
          (finCellMapLower g-c)
          h')
  where
  open approkz _ f-c g-c h∞'
  finSeqColim↑ : ∀ {ℓ} {X : Sequence ℓ} {m : ℕ} → FinSeqColim m X → FinSeqColim (suc m) X
  finSeqColim↑ (fincl n x) = fincl (injectSuc n) x
  finSeqColim↑ {m = suc m} (fpush n x i) = fpush (injectSuc n) x i

  h' : FinSeqColim→Colim (suc m) ∘
      finCellMap→FinSeqColim C D (finCellMapLower f-c)
      ≡
      FinSeqColim→Colim (suc m) ∘
      finCellMap→FinSeqColim C D (finCellMapLower g-c)
  h' = funExt λ { (fincl n x) j → h∞' j (fincl (injectSuc n) x)
                ; (fpush n x i) j → h∞' j (fpush (injectSuc n) x i)}

  open SeqHomotopyTypes

  module _
    (ind : finiteCellHom-rel (suc m)
            (finCellMapLower f-c) (finCellMapLower g-c)
              ((approkz.h∞ (suc m) (finCellMapLower f-c) (finCellMapLower g-c) h')))
    (f : (c : fst C (suc (suc m))) →
        Σ[ h ∈ (cell-hom (suc (suc m)) f-c g-c flast c) ]
        (Square (h∞ flast c) (cong incl h)
           (push (fmap f-c flast c)) (push (fmap g-c flast c))))
    (fp : (c : fst C (suc m)) →
      cell-hom-coh (suc (suc m)) f-c g-c flast c
      (finiteCellHom.hom (ind .fst) flast c)
      (f (CW↪ C (suc m) c) .fst)) where

    main-hom-typ : (n : Fin (suc (suc (suc m))))
      → Type _
    main-hom-typ n =
      (x : C .fst (fst n))
        → CW↪ D (fst n) (f-c .fmap n x)
         ≡ CW↪ D (fst n) (g-c .fmap n x)

    main-hom : (n : Fin (suc (suc (suc m)))) → main-hom-typ n
    main-hom = elimFin (fst ∘ f) (finiteCellHom.hom (fst ind))

    main-homβ = elimFinβ {A = main-hom-typ} (fst ∘ f) (finiteCellHom.hom (fst ind))

    main-coh : (n : Fin (suc (suc m))) (c : C .fst (fst n))
      → Square
        (cong (CW↪ D (suc (fst n)))
         (main-hom (injectSuc n) c))
        (main-hom (fsuc n)
         (CW↪ C (fst n) c))
        (cong (CW↪ D (suc (fst n))) (fcomm f-c n c))
        (cong (CW↪ D (suc (fst n))) (fcomm g-c n c))
    main-coh =
      elimFin
        (λ c → cong (cong (CW↪ D (suc (suc m))))
                     (funExt⁻ (main-homβ .snd flast) c)
              ◁ fp c
              ▷ sym (funExt⁻ (main-homβ .fst) (CW↪ C (suc m) c)))
        λ n c
         → cong (cong (CW↪ D (suc (fst n))))
             (funExt⁻ (main-homβ .snd (injectSuc n)) c)
          ◁ finiteCellHom.coh (fst ind) n c
          ▷ sym (funExt⁻ (main-homβ .snd (fsuc n)) (CW↪ C (fst n) c))

    ∞coh : (n : Fin (suc (suc (suc m)))) (x : fst C (fst n))
        → Square (h∞ n x) (λ i → incl (main-hom n x i))
                  (push (f-c .fmap n x)) (push (g-c .fmap n x))
    ∞coh = elimFin
      (λ c → f c .snd ▷ λ i j → incl (main-homβ .fst (~ i) c j))
      λ n c → ind .snd n c ▷ λ i j → incl (main-homβ .snd n (~ i) c j)

 -- pathToCellularHomotopy-ind

{-
  PT.rec {!!} (λ ind →
     ∣ (record { hom = {!!}
     ; coh = {!!} }) , {!!} ∣₁)
    (pathToCellularHomotopy-main m
      (finCellMapLower f-c) (finCellMapLower g-c) λ s → h∞' (injectSuc s))
  where
  module _ (ind : finiteCellHom-rel m (finCellMapLower f-c)
      (finCellMapLower g-c)
      (approkz.h∞ m (finCellMapLower f-c) (finCellMapLower g-c)
       (h∞' (injectSuc flast)))) where

    ind* = approkz.pathToCellularHomotopy-ind (suc m) f-c g-c (h∞' flast)
            flast λ c → {!!}

    ham : (n : Fin (suc (suc m))) (x : C .fst (fst n)) →
        CW↪ D (fst n) (f-c .fmap n x) ≡ CW↪ D (fst n) (g-c .fmap n x)
    ham (n , zero , p) = {!!}
    ham (n , suc diff , p) x =
         {!!}
      ∙∙ finiteCellHom.hom (ind .fst) (n , diff , cong predℕ p) x
      ∙∙ {!!} -- finiteCellHom.hom {!ind .fst!} {!!} 
-}  

  -- -- main theorem
  -- pathToCellularHomotopy-main : (n : Fin m)
  --   → ∃[ hₙ₊₁ ∈ ((c : fst C (suc (fst n)))
  --               → Σ[ h ∈ cell-hom (fsuc n) c ]
  --                    (Square (h∞ (fsuc n) c)
  --                            (cong incl h)
  --                            (push (f (fsuc n) c))
  --                            (push (g (fsuc n) c)))) ]
  --                   ((c : _) → cell-hom-coh n c (hₙ c .fst)
  --                                 (hₙ₊₁ (CW↪ C (fst n) c) .fst))
  -- pathToCellularHomotopy-main = ?
  
--   pathToCellularHomotopy-main {m = zero} = ∣ hom₀ , (λ n → ⊥.rec (¬Fin0 n)) ∣₁
--     where
--     hom₀ : (n : Fin 1) (c : fst C (fst n)) → Σ (cell-hom (fst n) c) (agrees-in-lim h∞ c)
--     hom₀ (zero , p) c = ⊥.rec (CW₀-empty C c)
--     hom₀ (suc n , p) =
--       ⊥.rec (snotz (sym (+-suc (fst (pred-≤-pred p)) n)
--                   ∙ pred-≤-pred p .snd))
--   pathToCellularHomotopy {m = suc zero} =
--     TR.rec squash₁
--       (λ hom → ∣ hom
--       , (λ { (zero , p) c → ⊥.rec (CW₀-empty C c)
--            ; (suc n , p) → ⊥.rec (¬-<-zero (pred-≤-pred p))}) ∣₁)
--       (invEq (_ , InductiveFinSatAC 1 _ _) hom₁)
--     where
--     hom₁ : (n : Fin 2)
--       → hLevelTrunc 1 ((c : fst C (fst n))
--                      → Σ (cell-hom (fst n) c) (agrees-in-lim h∞ c))
--     hom₁ (zero , p) = ∣ (λ c → ⊥.rec (CW₀-empty C c)) ∣
--     hom₁ (suc zero , p) =
--       PT.rec (isOfHLevelTrunc 1)
--       (λ {(f , p) → ∣ (λ c → f c , p c) ∣ₕ})
--         (invEq (_ , satAC∃Fin-C0 C (cell-hom 1) (agrees-in-lim h∞))
--                pathToCellularHomotopy₁)
--     hom₁ (suc (suc n) , p) =
--       ⊥.rec (¬-<-zero (pred-≤-pred (pred-≤-pred p)))
--   pathToCellularHomotopy {m = suc (suc m)} =
--     PT.rec squash₁
--       (λ {(h , h-coh) → PT.rec squash₁
--              (λ f → ∣ hom h h-coh (fst f) (snd f)
--                     , hom-coh h h-coh (fst f) (snd f) ∣₁)
--       (pathToCellularHomotopy-ind _ (h flast))})
--       (pathToCellularHomotopy {m = suc m})
--     where
--     module _ (h : (n : Fin (suc (suc m))) (c : fst C (fst n))
--                 → Σ (cell-hom (fst n) c) (agrees-in-lim h∞ c))
--              (h-coh : (n : Fin (suc m)) (c : fst C (fst n))
--                     → cell-hom-coh (fst n) c
--                          (h (injectSuc n) c .fst)
--                          (h (fsuc n) (CW↪ C (fst n) c) .fst))
--              (h-max : (c : fst C (suc (suc m)))
--                    → Σ (cell-hom (suc (suc m)) c) (agrees-in-lim h∞ c))
--              (h-max-coh : (c : fst C (suc m)) →
--                           cell-hom-coh (suc m) c
--                             (h flast c .fst)
--                             (h-max (CW↪ C (suc m) c) .fst))
--       where
--       h-help : {n : ℕ} {x : _} {p : _} {q : _} → h (n , p) x .fst ≡ h (n , q) x .fst
--       h-help {n = n} {x} {p} {q} i = h (n , isProp≤ p q i) x .fst

--       hom : (n : Fin (suc (suc (suc m)))) (c : fst C (fst n))
--            → Σ (cell-hom (fst n) c) (agrees-in-lim h∞ c)
--       hom (n , zero , p) =
--         subst (λ n → (c : fst C n) → Σ (cell-hom n c) (agrees-in-lim h∞ c))
--               (cong predℕ (sym p)) h-max
--       hom (n , suc diff , p) = h (n , diff , cong predℕ p)

--       hom₀-refl : {p : _} → hom (_ , zero , p) ≡ h-max
--       hom₀-refl {p = p} =
--         (λ j → subst (λ n → (c : fst C n)
--                    → Σ (cell-hom n c) (agrees-in-lim h∞ c))
--                      (isSetℕ _ _ (sym (cong predℕ p)) refl j)
--                      h-max)
--         ∙ transportRefl h-max

--       hom-coh : (n : Fin (suc (suc m))) (c : fst C (fst n)) →
--                    cell-hom-coh (fst n) c
--                      (hom (injectSuc n) c .fst)
--                      (hom (fsuc n) (CW↪ C (fst n) c) .fst)
--       hom-coh (n , zero , p) =
--         transport (λ j → (c : fst C (predℕ (p (~ j))))
--                → cell-hom-coh (predℕ (p (~ j))) c
--                     (hom (injectSuc (predℕ (p (~ j)) , zero , p-coh j)) c .fst)
--                     (hom (fsuc (predℕ (p (~ j)) , zero , p-coh j))
--                       (CW↪ C (predℕ (p (~ j))) c) .fst))
--            (λ c → cong (cong (CW↪ D (suc (suc m)))) h-help
--                 ◁ h-max-coh c
--                 ▷ cong fst (funExt⁻ (sym (hom₀-refl)) (CW↪ C (suc m) c)))
--         where
--         p-coh : PathP (λ j → suc (predℕ (p (~ j))) ≡ suc (suc m)) refl p
--         p-coh = isProp→PathP (λ i → isSetℕ _ _) _ p

--       hom-coh (n , suc diff , p) c =
--           cong (cong (CW↪ D (suc n))) h-help
--         ◁ h-coh (n , diff , cong predℕ p) c
--         ▷ h-help

-- module _ (m : ℕ) {C : finCWskel ℓ m} {D : finCWskel ℓ' m}
--   (f-c g-c : cellMap (finCWskel→CWskel m C) (finCWskel→CWskel m D))
--   (h∞ : realiseCellMap f-c ≡ realiseCellMap g-c) where
--   open SeqHomotopyTypes f-c g-c
--   C' = finCWskel→CWskel m C
--   D' = finCWskel→CWskel m D

--   open CWskel-fields C'

--   private
--     GoalTy =
--       Σ[ hₙ ∈ ((n : ℕ) (c : fst C' n) → cell-hom n c) ]
--            ((n : ℕ) (c : fst C' n)
--              → cell-hom-coh n c
--                   (hₙ n c)
--                   (hₙ (suc n) (CW↪ C' n c)))

--   pathToCellularHomotopyFin :
--      ∃[ hₙ ∈ ((n : ℕ) (c : fst C' n) → cell-hom n c) ]
--          ((n : ℕ) (c : fst C' n)
--            → cell-hom-coh n c
--                 (hₙ n c)
--                 (hₙ (suc n) (CW↪ C' n c)))
--   pathToCellularHomotopyFin =
--     PT.map (λ p → main₁ p , main₂ p)
--       (pathToCellularHomotopy f-c g-c h∞ {m = suc m})
--     where
--     module _ (ind : Σ
--       ((c : Fin (suc (suc m))) (n : fst (finCWskel→CWskel m C) (fst c)) →
--        Σ (cell-hom (fst c) n) (agrees-in-lim h∞ n))
--       (λ hₙ →
--          (n : Fin (suc m)) (c : fst (finCWskel→CWskel m C) (fst n)) →
--          cell-hom-coh (fst n) c (hₙ (injectSuc n) c .fst)
--          (hₙ (fsuc n) (CW↪ (finCWskel→CWskel m C) (fst n) c) .fst)))
--       where
--       open import Cubical.Foundations.Equiv.HalfAdjoint
--       cEq : (a : ℕ) → fst C' (a +ℕ suc m) ≃ fst C' (suc (a +ℕ suc m))
--       cEq a = CW↪ (fst C , fst (C .snd)) (a +ℕ suc m)
--             , transport (λ i → isEquiv (CW↪ (fst C , fst (C .snd)) (+-suc a m (~ i))))
--               (C .snd .snd (suc a))

--       cEq' : (a : ℕ) → HAEquiv (fst C' (a +ℕ suc m)) (fst C' (suc (a +ℕ suc m)))
--       cEq' a = iso→HAEquiv (equivToIso (cEq a))
--       open isHAEquiv renaming (g to haInv)

--       baz : (a : ℕ) → (c : fst C' (a +ℕ suc m)) → cell-hom (a +ℕ suc m) c
--       baz zero c = fst ind (suc m , 0 , refl) c .fst
--       baz (suc a) c =
--         cong (CW↪ (finCWskel→CWskel m D) (suc (a +ℕ suc m))
--              ∘ SequenceMap.map f-c (suc (a +ℕ suc m)))
--              (sym (rinv (cEq' a .snd) c))
--         ∙∙ cong (CW↪ (finCWskel→CWskel m D) (suc (a +ℕ suc m)))
--                 (sym (SequenceMap.comm f-c (a +ℕ suc m) (haInv (cEq' a .snd) c))
--              ∙∙ baz a (haInv (cEq' a .snd) c)
--              ∙∙ SequenceMap.comm g-c (a +ℕ suc m) (haInv (cEq' a .snd) c))
--         ∙∙ cong (CW↪ (finCWskel→CWskel m D) (suc (a +ℕ suc m))
--              ∘ SequenceMap.map g-c (suc (a +ℕ suc m)))
--              (rinv (cEq' a .snd) c) -- (linv (cEq' a) c)

--       main₁ : (n : ℕ) (c : fst C' n) → cell-hom n c
--       main₁ n with (Dichotomyℕ (suc m) n)
--       ... | inl (a , b) = subst (λ n → (c : fst C' n) → cell-hom n c) b (baz a)
--       ... | inr x = λ c → fst ind (n , <-trans x (0 , refl)) c .fst

--       main₂* : (x1 n : ℕ) (c : fst C' (x1 +ℕ suc m))
--         → cell-hom-coh (x1 +ℕ suc m) c (baz x1 c) (baz (suc x1) (CW↪ C' (x1 +ℕ suc m) c))
--       main₂* x1 n c i j =
--         hcomp (λ k → λ {(i = i0) → CW↪ (finCWskel→CWskel m D) (suc (x1 +ℕ suc m)) (baz x1 (linv (cEq' x1 .snd) c k) j)
--                        ; (j = i0) → CW↪ (finCWskel→CWskel m D) (suc (x1 +ℕ suc m)) (help' i k)
--                        ; (j = i1) → CW↪ (finCWskel→CWskel m D) (suc (x1 +ℕ suc m)) (help i k)})
--           (CW↪ (finCWskel→CWskel m D) (suc (x1 +ℕ suc m))
--             (hcomp (λ k → λ {(i = i0) → baz x1 (haInv (cEq' x1 .snd) (fst (cEq' x1) c)) j
--                             ; (j = i0) → SequenceMap.comm f-c (x1 +ℕ suc m)
--                                             (haInv (cEq' x1 .snd) (fst (cEq' x1) c)) (i ∧ k)
--                             ; (j = i1) → SequenceMap.comm g-c (x1 +ℕ suc m)
--                                             (haInv (cEq' x1 .snd) (fst (cEq' x1) c)) (i ∧ k)})
--                    (baz x1 (haInv (cEq' x1 .snd) (fst (cEq' x1) c)) j)))
--           where
--           help' : Square (cong (CW↪ (finCWskel→CWskel m D) (x1 +ℕ suc m))
--                                (cong (f (x1 +ℕ suc m)) (linv (cEq' x1 .snd) c)))
--                          (cong (f (suc (x1 +ℕ suc m)))
--                          (rinv (cEq' x1 .snd) (CW↪ C' (x1 +ℕ suc m) c)))
--                          (f-hom (x1 +ℕ suc m) (haInv (cEq' x1 .snd) (fst (cEq' x1) c)))
--                          (SequenceMap.comm f-c (x1 +ℕ suc m) c)
--           help' = (λ i j → f-hom (x1 +ℕ suc m) (linv (cEq' x1 .snd) c j) i)
--                 ▷ cong (cong (f (suc (x1 +ℕ suc m)))) (com (cEq' x1 .snd) c)

--           help : Square (cong (CW↪ (finCWskel→CWskel m D) (x1 +ℕ suc m) ∘ SequenceMap.map g-c (x1 +ℕ suc m))
--                         (linv (cEq' x1 .snd) c))
--                    (cong (SequenceMap.map g-c (suc (x1 +ℕ suc m)))
--                      (rinv (cEq' x1 .snd) (CW↪ C' (x1 +ℕ suc m) c)))
--                    (SequenceMap.comm g-c (x1 +ℕ suc m)
--                      (haInv (cEq' x1 .snd) (CW↪ C' (x1 +ℕ suc m) c)))
--                    (SequenceMap.comm g-c (x1 +ℕ suc m) c)
--           help = ((λ i j → g-hom (x1 +ℕ suc m) (linv (cEq' x1 .snd) c j) i))
--                ▷ cong (cong (g (suc (x1 +ℕ suc m)))) (com (cEq' x1 .snd) c)

--       main₂-inl : (x1 n : ℕ) (p : x1 +ℕ suc m ≡ n) (x₁ : suc m ≤ suc n) (c : fst C' n)
--         → cell-hom-coh n c
--             (subst (λ n → (c : fst C' n) → cell-hom n c) p (baz x1) c)
--             (subst (λ n → (c : fst C' n) → cell-hom n c) (snd x₁) (baz (fst x₁))
--                    (CW↪ (finCWskel→CWskel m C) n c))
--       main₂-inl x1 =
--         J> λ r c → subst2 (cell-hom-coh (x1 +ℕ suc m) c)
--           (λ j → transportRefl (baz x1) (~ j) c)
--           (cong (λ path → subst (λ n → (c₁ : fst C' n) → cell-hom n c₁) path (baz (fst r))
--                  (CW↪ (finCWskel→CWskel m C) (x1 +ℕ suc m) c))
--                  (isSetℕ _ _ (cong (_+ℕ suc m) (inj-+m {n = suc x1} (snd r))) (snd r)))
--           (main₂-inl' (fst r) (sym (inj-+m {n = suc x1} (snd r))) c)
--         where
--         main₂-inl' : (r1 : ℕ) (r2 : suc x1 ≡ r1) (c : fst C' (x1 +ℕ suc m))
--           → cell-hom-coh (x1 +ℕ suc m) c (baz x1 c)
--               (subst (λ n → (c₁ : fst C' n) → cell-hom n c₁)
--                (λ i → r2 (~ i) +ℕ suc m) (baz r1)
--                (CW↪ (finCWskel→CWskel m C) (x1 +ℕ suc m) c))
--         main₂-inl' = J> λ c
--           → subst (cell-hom-coh (x1 +ℕ suc m) c (baz x1 c))
--                   (λ j → transportRefl (baz (suc x1)) (~ j)
--                            (CW↪ (finCWskel→CWskel m C) (x1 +ℕ suc m) c))
--                   (main₂* x1 m c)

--       main₂ : (n : ℕ) (c : fst C' n) →
--         cell-hom-coh n c (main₁ n c) (main₁ (suc n) (CW↪ C' n c))
--       main₂ n with (Dichotomyℕ (suc m) n) | Dichotomyℕ (suc m) (suc n)
--       ... | inl x | inl x₁ = main₂-inl (fst x) n (snd x) x₁
--       ... | inl x | inr x₁ = ⊥.rec (¬m<m (<-trans x (pred-≤-pred x₁)))
--       ... | inr x | inl (zero , x₁) = λ c → snd ind (n , x) c
--         ▷ (lem n (cong predℕ x₁) c _
--         ∙ cong (λ w → subst (λ n₁ → (c₁ : fst C' n₁) → cell-hom n₁ c₁) w
--                         (λ c₁ → fst ind (suc m , 0 , (λ _ → suc (suc m))) c₁ .fst)
--                         (snd (snd (snd (snd (fst (snd C)))) n) .equiv-proof (inl c) .fst .fst))
--                (isSetℕ _ _ (cong suc (cong predℕ x₁)) x₁))
--         where
--         lem : (n : ℕ) (p : m ≡ n) (c : fst C n) (w : _)
--           → fst ind (suc n , w) (CW↪ C' n c) .fst
--            ≡ subst (λ n₂ → (c₁ : fst C' n₂) → cell-hom n₂ c₁)
--                    (cong suc p) (λ c → ind .fst (suc m , 0 , refl) c .fst)
--                    (CW↪ C' n c)
--         lem = J> λ c w → cong (λ w → fst ind (suc m , w) (CW↪ C' m c) .fst) (isProp≤ _ _)
--           ∙ λ j → transportRefl (λ (c₁ : fst C' (suc m)) → ind .fst (suc m , 0 , refl) c₁ .fst) (~ j) (CW↪ C' m c)
--       ... | inr x | inl (suc diff , x₁) =
--         ⊥.rec (⊥.rec (¬m<m (≤<-trans x (diff , +-suc diff (suc m) ∙ x₁))))
--       ... | inr x | inr x₁ = λ c → snd ind (n , x) c
--         ▷ cong (λ p → fst ind (suc n , p) (CW↪ (finCWskel→CWskel m C) n c) .fst) (isProp≤ _ _)


pathToCellularHomotopy :
  {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ) (f-c g-c : finCellMap m C D)
  → ((x : fst C m) → Path (realise D) (incl (fmap f-c flast x)) (incl (fmap g-c flast x)))
  → ∥ finiteCellHom m f-c g-c ∥₁
pathToCellularHomotopy {C} {D} m f-c g-c h =
  PT.map fst
    (pathToCellularHomotopy-main m f-c g-c
      (→FinSeqColimHomotopy _ _ h))

-- module _ (m : ℕ) (C D : CWskel ℓ) (f : realise C → realise D) where
--   finMap→cellMap : ∥ finCellMap m C D ∥₂
--   finMap→cellMap =
--     elim→Set (λ _ → squash₂)
--     (∣_∣₂ ∘ fst)
--     {!λ !}
--     (CWmap→finCellMap C D f m)
--   {- elim→Set {P = λ _ → ∥ cellMap (finCWskel→CWskel m C) (finCWskel→CWskel m D) ∥₂}
--                               (λ _ → squash₂)
--                               ∣_∣₂
--                               {!!}
--                               (finMap→cellMap₁ m C D f)
-- -}
