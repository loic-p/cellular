{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.SFT where

open import Cubical.CW.Subcomplex

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.Connected
open import Cubical.CW.Homology.Base
open import Cubical.CW.Approximation
open import Cubical.CW.ChainComplex
open import Cubical.Axiom.Choice

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.FinSequence
open import Cubical.Data.Int
open import Cubical.Data.Unit

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/s_)
open import Cubical.HITs.Wedge

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties
open import Cubical.Homotopy.Connected

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Abelianization.Properties as Abi
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.AbGroup.FinitePresentation

open import Cubical.Relation.Nullary

open import Cubical.CW.Instances.Sn
open import Cubical.CW.Homology.Groups.Sn

open import Cubical.Homotopy.Group.PiAbCofibFinSphereBouquetMap
open import Cubical.Homotopy.Group.PiCofibFinSphereBouquetMap
open import Cubical.HITs.Bouquet
open import Cubical.HITs.FreeGroup.Base

open import Cubical.HITs.Bouquet
open import Cubical.HITs.FreeGroup.Base


open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as TR
open import Cubical.CW.Properties
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.Subgroup

-- open import Cubical.CW.HurewiczTheorem

open import Cubical.CW.Instances.Pushout

open import Cubical.CW.Instances.Unit
open import Cubical.CW.Instances.Empty
open import Cubical.CW.Instances.Sigma
open import Cubical.CW.Instances.Susp
open import Cubical.CW.Instances.Join


private
  variable
    ℓ : Level


-- "Obstruction theory".
preLiftFromNDimFinCW : {Y Z : Type ℓ} (n : ℕ) (X : CWskel ℓ)
  → (f : Y → Z)
  → isConnectedFun n f
  → (g : fst X n → Z)
  → ∃[ l ∈ (fst X n → Y) ] (f ∘ l ≡ g)
preLiftFromNDimFinCW zero X f isc g =
  ∣ (λ x → ⊥.rec (X .snd .snd .snd .fst x))
    , (funExt (λ x → ⊥.rec (X .snd .snd .snd .fst x))) ∣₁
preLiftFromNDimFinCW {Y = Y} {Z} (suc n) X f isc =
  subst (λ X → (g : X → Z) → ∃[ l ∈ (X → Y) ] (f ∘ l ≡ g))
        (ua (invEquiv (X .snd .snd .snd .snd n)))
        (λ g → PT.rec squash₁ (uncurry (main g))
          (preLiftFromNDimFinCW n X f (isConnectedFunSubtr n 1 f isc) (g ∘ inl)))
  where
  α = X .snd .snd .fst n
  Xₙ₊₁ = Pushout α fst

  module _ (g : Xₙ₊₁ → Z) (l : fst X n → Y) (lcomm : f ∘ l ≡ g ∘ inl) where
    P : Xₙ₊₁ → Type _
    P x = fiber f (g x)

    lem : (n' : ℕ) → n ≡ n' → (x : Fin (fst (X .snd) n))
      → ∃[ s ∈ P (inr x) ]
           (∥ (((t : S⁻ n)
           → s ≡ ((l (α (x , t))) , (funExt⁻ lcomm (α (x , t)) ∙ cong g (push (x , t)))))) ∥₁)
    lem zero p x = TR.rec squash₁
      (λ a → ∣ a , ∣ (λ x → ⊥.rec (subst S⁻ p x)) ∣₁ ∣₁)
      (subst (λ n → isConnectedFun (suc n) f) p isc
             (g (inr x)) .fst)
    lem (suc n') p x =
      PT.map (λ F → (F ⋆S i0) , ∣ F ∣₁)
      (sphereToTrunc n {A = λ t →
      Path (P (inr x))
            (l (α (x , ⋆S)) , (funExt⁻ lcomm (α (x , ⋆S)) ∙ cong g (push (x , ⋆S))))
            ((l (α (x , t))) , (funExt⁻ lcomm (α (x , t)) ∙ cong g (push (x , t)))) }
           λ x → isConnectedPath n (isc _) _ _ .fst)
      where
      ⋆S : S⁻ n
      ⋆S = subst S⁻ (sym p) (ptSn n')

    lemImproved : (x : Fin (fst (X .snd) n))
      → hLevelTrunc 1 (Σ[ s ∈ P (inr x) ]
           ((((t : S⁻ n)
           → s ≡ ((l (α (x , t))) , (funExt⁻ lcomm (α (x , t)) ∙ cong g (push (x , t))))))))
    lemImproved x = PT.rec (isOfHLevelTrunc 1)
      (uncurry (λ pinr → PT.rec (isOfHLevelTrunc 1)
                                 (λ w → ∣ pinr , w ∣ₕ)))
      (lem n refl x)

    main : ∃[ l ∈ (Xₙ₊₁ → Y) ] (f ∘ l ≡ g)
    main = TR.rec squash₁ (λ F
      → ∣ (λ { (inl x) → l x
              ; (inr x) → F x .fst .fst
              ; (push (x , a) i) → F x .snd a (~ i) .fst})
            , funExt (λ { (inl x) → funExt⁻ lcomm x
                        ; (inr x) → F x .fst .snd
                        ; (push (x , a) i) j
                          → hcomp (λ k → λ {(i = i0) → compPath-filler
                                                          (funExt⁻ lcomm (α (x , a)))
                                                          (cong g (push (x , a))) (~ k) j
                                           ; (i = i1) → F x .fst .snd j
                                           ; (j = i0) → f (F x .snd a (~ i) .fst)
                                           ; (j = i1) → g (push (x , a) (i ∨ ~ k))})
                                  (F x .snd a (~ i) .snd j)}) ∣₁)
           (invEq (_ , InductiveFinSatAC 1 _ _) lemImproved)

-- open FinitePresentation
-- isFPπ'CofibFinSphereBouquetMap :  {n m k : ℕ} (α : FinSphereBouquetMap∙ m k (suc n))
--   → FinitePresentation (Group→AbGroup (π'Gr (suc n) (cofib (fst α) , inl tt))
--                                        (π'-comm n))
-- nGens (isFPπ'CofibFinSphereBouquetMap {n = n} {m = m} {k = k} α) = k
-- nRels (isFPπ'CofibFinSphereBouquetMap {n = n} {m = m} {k = k} α) = m
-- rels (isFPπ'CofibFinSphereBouquetMap {n = n} {m = m} {k = k} α) = bouquetDegree (fst α)
-- fpiso (isFPπ'CofibFinSphereBouquetMap {n = n} {m = m} {k = k} α) =
--   π'CofibFinSphereBouquetMap≅ℤ[]/BouquetDegree α

-- Proof that πₙ₊₂(X) is FP when X is (n+1)-connected
-- first: a proof of the result with some additional explicit assumptions
-- (which we later get for free up to propositional truncation)
-- module isFinitelyPresented-π'connectedCW-lemmas
--   (X : Pointed ℓ-zero) (n : ℕ)
--   (X' : isConnectedCW (1 +ℕ n) (typ X))
--   (isConX' : isConnected 2 (X' .fst .fst (4 +ℕ n)))
--   (x : X' .fst .fst (4 +ℕ n))
--   (x≡ : X' .snd .fst (CW↪∞ (connectedCWskel→CWskel (fst X')) (4 +ℕ n) x)
--           ≡ snd X)
--   where
--   private
--     Xˢᵏᵉˡ : CWskel _
--     Xˢᵏᵉˡ = connectedCWskel→CWskel (fst X')

--     e∞ = X' .snd

--     X₄₊ₙ∙ : Pointed _
--     fst X₄₊ₙ∙ = X' .fst .fst (4 +ℕ n)
--     snd X₄₊ₙ∙ = x

--   open CWskel-fields Xˢᵏᵉˡ

--   firstEquiv : GroupEquiv (π'Gr (suc n) X₄₊ₙ∙) (π'Gr (suc n) X)
--   firstEquiv =
--      (connectedFun→π'Equiv (suc n)
--        (fst e∞ ∘ CW↪∞ Xˢᵏᵉˡ (4 +ℕ n) , x≡)
--        (isConnectedComp (fst e∞) (CW↪∞ Xˢᵏᵉˡ (4 +ℕ n)) _
--          (isEquiv→isConnected _ (snd e∞) (4 +ℕ n))
--          (isConnected-CW↪∞ (4 +ℕ n) Xˢᵏᵉˡ)))

--   isFP-π'X₄₊ₙ : isFinitelyPresented (Group→AbGroup (π'Gr (suc n) X₄₊ₙ∙)
--                                     (π'-comm n))
--   isFP-π'X₄₊ₙ = PT.rec squash₁
--     (λ {(α , e) → PT.map
--       (λ pp → subst FinitePresentation
--                       (cong (λ X → Group→AbGroup (π'Gr (suc n) X) (π'-comm n))
--                      (ΣPathP ((sym (cong fst e)) , pp)))
--                      (hasFPπ'CofibFinSphereBouquetMap α))
--       (lem α (cong fst e))})
--      (connectedCW≃CofibFinSphereBouquetMap (suc n) (fst X)
--         X' (subCW (4 +ℕ n) (fst X , Xˢᵏᵉˡ , invEquiv e∞) .snd))
--       where
--       lem : (α : FinSphereBouquetMap∙
--                    (card (suc (suc (suc n)))) (card (suc (suc n)))
--                    (suc n))
--              (e : fst X₄₊ₙ∙ ≡ cofib (fst α))
--         → ∥ PathP (λ i → e (~ i)) (inl tt) x ∥₁
--       lem α e = TR.rec squash₁ ∣_∣₁ (isConnectedPathP _ isConX' _ _ .fst)

--   isFPX : isFinitelyPresented (Group→AbGroup (π'Gr (suc n) X) (π'-comm n))
--   isFPX =
--     PT.map (λ fp → subst FinitePresentation (AbGroupPath _ _ .fst firstEquiv) fp)
--            isFP-π'X₄₊ₙ

-- -- Main result
-- isFinitelyPresented-π'connectedCW : (X : Pointed ℓ-zero)
--   (cwX : isCW (fst X)) (n : ℕ) (cX : isConnected (3 +ℕ n) (typ X))
--   → isFinitelyPresented (Group→AbGroup (π'Gr (suc n) X) (π'-comm n))
-- isFinitelyPresented-π'connectedCW X =
--   PT.rec (isPropΠ2 (λ _ _ → squash₁)) λ cwX n cX →
--   PT.rec squash₁ (λ a →
--   PT.rec squash₁ (λ b →
--   PT.rec squash₁ (λ c →
--   PT.rec squash₁ (isFPX X n a b c)
--     (TR.rec (isProp→isOfHLevelSuc (suc n) squash₁) ∣_∣₁
--             (isConnectedPath _ cX _ _ .fst)))
--     (TR.rec (isOfHLevelSuc 1 squash₁) ∣_∣₁ (b .fst)))
--     ∣ connectedFunPresConnected 2
--        {f = fst (snd a) ∘ CW↪∞ (connectedCWskel→CWskel (fst a)) (4 +ℕ n)}
--          (isConnectedSubtr' (suc n) 2 cX)
--          (isConnectedComp (fst (snd a)) _ _
--            (isEquiv→isConnected _ (snd (snd a)) 2)
--          λ b → isConnectedSubtr' (suc (suc n)) 2
--                  ((isConnected-CW↪∞ (4 +ℕ n)
--                    (connectedCWskel→CWskel (fst a))) b)) ∣₁)
--     (makeConnectedCW (1 +ℕ n) cwX cX)
--   where
--   open isFinitelyPresented-π'connectedCW-lemmas

-- open import Cubical.Data.Sum as ⊎
-- -- elimination principle for pushouts
-- module _ {ℓ' : Level} (P : Type → Type ℓ') (P1 : P Unit) (P0 : P ⊥)
--          (Ppush : (A B C : Type) (f : A → B) (g : A → C)
--                 → P A → P B → P C → P (Pushout f g)) where
--   private
--    PFin1 : P (Fin 1)
--    PFin1 = subst P (isoToPath Iso-Unit-Fin1) P1

--    P⊎ : {B C : Type} → P B → P C → P (B ⊎ C)
--    P⊎ {B = B} {C} pB pC =
--      subst P (isoToPath PushoutEmptyDomainIso)
--              (Ppush ⊥ B C (λ ()) (λ ()) P0 pB pC)

--    PFin : (n : ℕ) → P (Fin n)
--    PFin zero =
--      subst P (ua (propBiimpl→Equiv isProp⊥ (λ x → ⊥.rec (¬Fin0 x)) (λ()) ¬Fin0))
--              P0
--    PFin (suc n) = subst P (sym (isoToPath Iso-Fin-Unit⊎Fin)) (P⊎ P1 (PFin n))

--    PS : (n : ℕ) → P (S⁻ n)
--    PS zero = P0
--    PS (suc zero) = subst P (isoToPath (invIso Iso-Bool-Fin2)) (PFin 2)
--    PS (suc (suc n)) =
--      subst P (isoToPath (compIso PushoutSuspIsoSusp (invIso (IsoSucSphereSusp n))))
--        (Ppush (S₊ n) Unit Unit _ _ (PS (suc n)) P1 P1)


--    PFin×S : (n m : ℕ) → P (Fin n × S⁻ m)
--    PFin×S zero m = subst P (ua (uninhabEquiv (λ()) (λ x → ¬Fin0 (fst x)))) P0
--    PFin×S (suc n) m =
--      subst P (isoToPath (compIso (compIso (⊎Iso (invIso rUnit×Iso) Σ-swap-Iso)
--                         (compIso (invIso ×DistR⊎Iso) Σ-swap-Iso))
--                         (Σ-cong-iso-fst (invIso Iso-Fin-Unit⊎Fin))))
--              (P⊎ (PS m) (PFin×S n m))

--    PCWskel : (B : CWskel ℓ-zero) → (n : ℕ) → P (fst B n)
--    PCWskel B zero = subst P (ua (uninhabEquiv (λ()) (CW₀-empty B))) P0
--    PCWskel B (suc n) =
--      subst P (ua (invEquiv (B .snd .snd .snd .snd n)))
--              (Ppush _ _ _ _ _ (PFin×S _ _) (PCWskel B n) (PFin _))

--   elimPropFinCWFun : (B : Type) → hasFinCWskel B → P B
--   elimPropFinCWFun B fCWB =
--     subst P (ua (compEquiv (isoToEquiv (realiseFin _ (fCWB .snd .fst)))
--             (invEquiv (fCWB .snd .snd))))
--             (PCWskel (finCWskel→CWskel _ (fCWB .snd .fst)) (fCWB .fst))

--   -- main result
--   elimPropFinCW : (B : finCW ℓ-zero) → isProp (P (fst B)) → P (fst B)
--   elimPropFinCW (B , Bstr) isp = PT.rec isp (elimPropFinCWFun B) Bstr

-- isFinCWΣ : (A : finCW ℓ-zero) (B : fst A → finCW ℓ-zero)
--   → isFinCW (Σ (fst A) (fst ∘ B))
-- isFinCWΣ A = elimPropFinCW
--    (λ A → (B : A → finCW ℓ-zero) → isFinCW (Σ A (fst ∘ B)))
--    (λ B → subst isFinCW (sym (ua (ΣUnit (fst ∘ B)))) (snd (B tt)))
--    (λ _ → subst isFinCW (ua (invEquiv (ΣEmpty _))) ∣ hasFinCWskel⊥ ∣₁)
--    (λ A0 A1 A2 f g p q r B
--      → subst isFinCW (ua (invEquiv (ΣPushout≃PushoutΣ f g (fst ∘ B))))
--              (isFinCWPushout
--                (_ , p (λ x → B (inl (f x)))) (_ , q λ x → B (inl x))
--                (_ , r λ a → B (inr a)) _ _))
--    A (isPropΠ λ _ → squash₁)

-- isFinCW× : (A B : finCW ℓ-zero) → isFinCW (fst A × fst B)
-- isFinCW× A B = isFinCWΣ A (λ _ → B)

-- open import Cubical.HITs.Join
-- isFinCWJoinPushout : (A B : finCW ℓ-zero) → isFinCW (joinPushout (fst A) (fst B))
-- isFinCWJoinPushout A B = isFinCWPushout (_ , (isFinCW× A B)) A B fst snd

-- isFinCWJoin : (A B : finCW ℓ-zero) → isFinCW (join (fst A) (fst B))
-- isFinCWJoin A B =
--   subst isFinCW (joinPushout≡join (fst A) (fst B)) (isFinCWJoinPushout A B)

-- isFinCWSusp : (A : finCW ℓ-zero) → isFinCW (Susp (fst A))
-- isFinCWSusp A =
--   subst isFinCW PushoutSusp≡Susp
--     (isFinCWPushout A finCWUnit finCWUnit _ _)

-- isFinCWSusp^' : (A : finCW ℓ-zero) (n : ℕ) → isFinCW (Susp^' n (fst A))
-- isFinCWSusp^' A zero = snd A
-- isFinCWSusp^' A (suc n) = isFinCWSusp (_ , isFinCWSusp^' A n)

-- isFinCWSusp^ : (A : finCW ℓ-zero) (n : ℕ) → isFinCW (Susp^ n (fst A))
-- isFinCWSusp^ A n = subst isFinCW (Susp^'≡Susp^ n) (isFinCWSusp^' A n)

open import Cubical.CW.Subcomplex
hasNDimFinCW : ℕ → Type ℓ → Type (ℓ-suc ℓ)
hasNDimFinCW {ℓ = ℓ} n X = Σ[ X' ∈ finCWskel ℓ n ] X ≃ realise (finCWskel→CWskel n X')

isNDimFinCW : ℕ → Type ℓ → Type (ℓ-suc ℓ)
isNDimFinCW n X = ∥ hasNDimFinCW n X ∥₁

mapFromNSkel : (X : Type ℓ) (hX : isFinCW X) (n : ℕ)
  → ∃[ Y ∈ Type ℓ ] Σ[ hY ∈ isNDimFinCW n Y ] Σ[ f ∈ (Y → X) ] isConnectedFun n f
mapFromNSkel X = PT.rec (isPropΠ (λ _ → squash₁))
  λ {(dim , Xstr) → λ n
    → ∣ Xstr .fst .fst n
     , ∣ ((subComplex (finCWskel→CWskel dim (Xstr .fst)) n .fst)
       , ((subComplex (finCWskel→CWskel dim (Xstr .fst)) n .snd)
       , (subComplexYieldsFinCWskel (finCWskel→CWskel dim (Xstr .fst)) n .snd)))
       , (isoToEquiv (realiseSubComplex n (Xstr .fst .fst , Xstr .fst .snd .fst))) ∣₁
     , subst (λ X → Σ (Xstr .fst .fst n → X) (isConnectedFun n))
             (ua (invEquiv (Xstr .snd)))
             ((CW↪∞ ((Xstr .fst .fst) , (Xstr .fst .snd .fst)) n)
             , (isConnected-CW↪∞ n ((Xstr .fst .fst) , (Xstr .fst .snd .fst)))) ∣₁}

liftFromNDimFinCW : (n : ℕ) {Y Z : Type ℓ}
  (f : Y → Z) (X : Type ℓ) (hX : isNDimFinCW n X)
  (hf : isConnectedFun n f) (g : X → Z)
  → ∃[ l ∈ (X → Y) ] (f ∘ l ≡ g)
liftFromNDimFinCW n {Y} {Z} f X =
  PT.rec (isPropΠ2 (λ _ _ → squash₁))
   λ Xstr cf
     → subst (λ X → (g : X → Z) → ∃-syntax (X → Y) (λ l → f ∘ l ≡ g))
              (ua (compEquiv (isoToEquiv (realiseFin n (Xstr .fst))) (invEquiv (Xstr .snd))))
              (preLiftFromNDimFinCW n
                (Xstr .fst .fst , Xstr .fst .snd .fst) f cf)
