{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.SphereBouquetCofibHomotopy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed


open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.Connected
open import Cubical.CW.Homology
open import Cubical.CW.Subcomplex


open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
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
open import Cubical.HITs.SetTruncation as ST


open import Cubical.Homotopy.Group.Base
-- open import Cubical.Homotopy.Group.Properties

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Foundations.HLevels

open import Cubical.Algebra.AbGroup

open import Cubical.CW.Approximation

open import Cubical.Data.Empty as ⊥

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.CW.ChainComplex
open import Cubical.HITs.SetQuotients.Base renaming (_/_ to _/s_)
open import Cubical.HITs.SetQuotients.Properties as SQ
open import Cubical.Data.Int
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.Algebra.Group.Abelianization.Base

open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.HITs.Wedge


open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Hurewicz.random


open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Pushout as PO

·GroupAutomorphism : ∀ {ℓ} (G : Group ℓ) (g : fst G) → Iso (fst G) (fst G)
Iso.fun (·GroupAutomorphism G g) = GroupStr._·_ (snd G) g
Iso.inv (·GroupAutomorphism G g) = GroupStr._·_ (snd G) (GroupStr.inv (snd G) g)
Iso.rightInv (·GroupAutomorphism G g) h =
  GroupStr.·Assoc (snd G) _ _ _
  ∙ cong₂ (GroupStr._·_ (snd G)) (GroupStr.·InvR (snd G) g) refl
  ∙ GroupStr.·IdL (snd G) h
Iso.leftInv (·GroupAutomorphism G g) h =
  GroupStr.·Assoc (snd G) _ _ _
  ∙ cong₂ (GroupStr._·_ (snd G)) (GroupStr.·InvL (snd G) g) refl
  ∙ GroupStr.·IdL (snd G) h

·GroupAutomorphismR : ∀ {ℓ} (G : Group ℓ) (g : fst G) → Iso (fst G) (fst G)
Iso.fun (·GroupAutomorphismR G g) x = GroupStr._·_ (snd G) x g
Iso.inv (·GroupAutomorphismR G g) x = GroupStr._·_ (snd G) x (GroupStr.inv (snd G) g)
Iso.rightInv (·GroupAutomorphismR G g) h =
  sym (GroupStr.·Assoc (snd G) _ _ _)
  ∙ cong₂ (GroupStr._·_ (snd G)) refl (GroupStr.·InvL (snd G) g) -- 
  ∙ GroupStr.·IdR (snd G) h
Iso.leftInv (·GroupAutomorphismR G g) h =
    sym (GroupStr.·Assoc (snd G) _ _ _)
  ∙ cong₂ (GroupStr._·_ (snd G)) refl (GroupStr.·InvR (snd G) g) -- 
  ∙ GroupStr.·IdR (snd G) h

open import Cubical.Algebra.Group.Subgroup
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.S1
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.HITs.FreeAbGroup.Base

open import Cubical.Algebra.Group.Free
open import Cubical.Data.List renaming ([_] to [_]L)


data S¹Bouquet {ℓ} (A : Type ℓ) : Type ℓ where
  base' : S¹Bouquet A
  loops : A → base' ≡ base'

S¹Bouquet→Pre : (n m : ℕ) → ΩS¹
S¹Bouquet→Pre n m with (n ≟ᵗ m)
... | lt x = refl
... | eq x = loop
... | gt x = refl

S¹Bouquet→ : (n : ℕ) → S¹Bouquet (Fin n) → Fin n → S¹
S¹Bouquet→ n base' s = base
S¹Bouquet→ n (loops x i) s = S¹Bouquet→Pre (fst x) (fst s) i

S¹Bouquet← : {!!}
S¹Bouquet← = {!!}

open import Cubical.HITs.FreeGroup as FG

CodeS¹Bouquet : ∀ {ℓ} (A : Type ℓ) → S¹Bouquet A → Type ℓ
CodeS¹Bouquet A base' = FreeGroup A
CodeS¹Bouquet A (loops x i) =
  isoToPath (·GroupAutomorphism (freeGroupGroup A) (η x)) i

-- decodeFun : ∀ {ℓ} {A : Type ℓ}  → List (Bool × A) → base' ≡ base'
-- decodeFun [] = refl
-- decodeFun ((false , a) ∷ x₁) = sym (loops a) ∙ decodeFun x₁
-- decodeFun ((true , a) ∷ x₁) = loops a ∙ decodeFun x₁

-- poo :  ∀ {ℓ} {A : Type ℓ}
--   (a b : List (Bool × A)) →
--       (A NormalForm.· a ⁻¹≡ε) b → decodeFun a ≡ decodeFun b
-- poo [] [] n = refl
-- poo [] ((false , r) ∷ b) NormalForm.[ ≡ε ]≡ε = {!≡ε!} ∙ {!!}
-- poo [] ((true , r) ∷ b) n = {!!}
-- poo (x ∷ a) b n = {!b!}

decodeS¹Bouquet' : ∀ {ℓ} {A : Type ℓ} → GroupHom (freeGroupGroup A) (πGr 0 (S¹Bouquet A , base'))
decodeS¹Bouquet' {A = A} = FG.rec {Group = πGr 0 (S¹Bouquet A , base')} (λ a → ∣ loops a ∣₂)

decodeS¹Bouquet : ∀ {ℓ} {A : Type ℓ} (x : S¹Bouquet A)
  → CodeS¹Bouquet A x → ∥ (base' ≡ x) ∥₂
decodeS¹Bouquet base' = decodeS¹Bouquet' .fst
decodeS¹Bouquet {A = A} (loops x i) = {!x!}
  where
  M : transport (λ i → ∥ base' ≡ loops x i ∥₂)
    ≡ Iso.fun (·GroupAutomorphismR (πGr 0 (S¹Bouquet A , base')) ∣ loops x ∣₂)
  M = funExt (ST.elim (λ _ → isSetPathImplicit) λ s
    → cong ∣_∣₂ λ j → transp (λ i₁ → base' ≡ loops x (i₁ ∨ j)) j (compPath-filler s (loops x) j))

  H1 : {!(·GroupAutomorphismR (πGr 0 (S¹Bouquet A , base')) ∣ loops x ∣₂)!}
  H1 = {!!}

  oh? : PathP (λ i → isoToPath (·GroupAutomorphism (freeGroupGroup A) (η x)) i
                   → ∥ base' ≡ loops x i ∥₂)
              (decodeS¹Bouquet' .fst) (decodeS¹Bouquet' .fst)
  oh? = toPathP (funExt λ w
    → cong (transport (λ i → ∥ base' ≡ loops x i ∥₂))
        (cong (decodeS¹Bouquet' .fst) λ _ → transport (λ i → isoToPath (·GroupAutomorphism (freeGroupGroup A) (η x)) (~ i)) w)
        ∙ {!!}
        ∙ {!!})

LoopSphereBouquet : {!!}
LoopSphereBouquet = {!!}

module spB {m k : ℕ}
  (α : SphereBouquet∙ (suc zero) (Fin m)
  →∙ SphereBouquet∙ (suc zero) (Fin k))
  (α' : Fin m → Fin k → fst (Ω (S₊∙ 1))) where
  α'' : SphereBouquet∙ (suc zero) (Fin m)
    →∙ SphereBouquet∙ (suc zero) (Fin k)
  fst α'' (inl x) = {!!}
  fst α'' (inr (s , base)) = {!!}
  fst α'' (inr (s , loop i)) = {!inr (? , sumFinGen _∙_ refl (α' s) i)!}
  fst α'' (push a i) = {!!}
  snd α'' = {!!}

  αD' : AbGroupHom (ℤ[Fin m ]) (ℤ[Fin k ])
  fst αD' F t = {!!} -- ? · (winding (sumFinGen _∙_ refl λ k → α' k t))
  snd αD' = {!!}

  ℤ/Imα' : Group₀
  ℤ/Imα' = AbGroup→Group (ℤ[Fin k ]) / {!!}

--   ℤ/Imα : Group₀
--   ℤ/Imα = AbGroup→Group (ℤ[Fin k ]) / ((imSubgroup (bouquetDegree (fst α))) , (isNormalIm _ λ _ _ → AbGroupStr.+Comm (snd ℤ[Fin k ]) _ _))

--   theIs : (t : Fin k) → ℤ/Imα .fst ≃ ℤ/Imα .fst
--   theIs t = isoToEquiv (·GroupAutomorphism ℤ/Imα [ ℤFinGenerator t ])

--   Code : SphereBouquet 1 (Fin k) → Type
--   Code (inl x) = ℤ/Imα .fst
--   Code (inr (t , base)) = ℤ/Imα .fst
--   Code (inr (t , loop i)) = ua (theIs t) i
--   Code (push a i) = ℤ/Imα .fst

--   Bah : (t : _) (x : _) (y : Code x) → fst α t ≡ x → Code x ≃ ℤ/Imα .fst
--   Bah t (inl x) y p = idEquiv _
--   Bah (inl x) (inr (s , base)) y p = substEquiv Code (sym (snd α) ∙ p ∙ sym (push s))
--   Bah (inr x) (inr (s , base)) y p = {!!}
--   Bah (push a i) (inr (s , base)) y p = {!!}
--   Bah t (inr (s , loop i)) = {!!}
--     where
--     W : (t : _) → _
--     W t = PathP (λ i → ua (theIs s) i → fst α t ≡ inr (s , loop i) → ua (theIs s) i ≃ ℤ/Imα .fst) (λ _ _ → idEquiv _) (λ _ _ → idEquiv _)

--     W∙ : W (inl tt)
--     W∙ = toPathP (funExt λ r → funExt λ o → {!!})

--     isS : (t : _) → isProp (W t)
--     isS = λ t → isOfHLevelPathP' 1 (isSetΠ2 (λ _ _ → isOfHLevel≃ 2 squash/ squash/)) _ _

--     L : (t : _) → W t
--     L = PO.elimProp _ isS (λ _ → W∙) (uncurry λ s → toPropElim (λ _ → isS _) (subst W (push s) W∙))
--   Bah t (push a i) y p = {!y!} -- idEquiv _
  
--   CodeCofib : cofib (fst α) → Type
--   CodeCofib (inl x) = ℤ/Imα .fst
--   CodeCofib (inr x) = Code x
--   CodeCofib (push (inl x) i) = {! ℤ/Imα .fst!}
--   CodeCofib (push (inr (t , y)) i) = {!y!}
--   CodeCofib (push (push a i₁) i) = {!!}

-- ΩSphere→ : {m k : ℕ}
--   (α : SphereBouquet∙ (suc zero) (Fin m)
--   →∙ SphereBouquet∙ (suc zero) (Fin k))
--   → cofib (fst α) → Type
-- ΩSphere→ α (inl x) = {!!}
-- ΩSphere→ α (inr x) = {!x -- ℤ[Fin_]!}
-- ΩSphere→ α (push a i) = {!!}

-- toCofib∙ : {n m k : ℕ}
--   (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
--   → SphereBouquet∙ (suc n) (Fin k) →∙ (cofib (fst α) , inl tt)
-- fst (toCofib∙ α) = inr
-- snd (toCofib∙ α) = (λ i → inr (snd α (~ i))) ∙ sym (push (inl tt))

-- intoCofib : (n m k : ℕ) (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
--   → (f : S₊∙ (suc n) →∙ (cofib (fst α) , inl tt))
--   → ∃[ g ∈ S₊∙ (suc n) →∙ SphereBouquet∙ (suc n) (Fin k) ]
--       f ≡ (toCofib∙ α ∘∙ g)
-- -- intoCofib n zero k α f = ∣ ((Iso.fun lem , refl) ∘∙ f)
-- --   , ΣPathP ((λ i x → Iso.leftInv lem (fst f x) (~ i))
-- --   , main _ _) ∣₁
-- --   where
-- --   lem : Iso (cofib (fst α)) (SphereBouquet (suc n) (Fin k))
-- --   Iso.fun lem (inl x) = inl tt
-- --   Iso.fun lem (inr x) = x
-- --   Iso.fun lem (push (inl x) i) = snd α (~ i)
-- --   Iso.inv lem x = inr x
-- --   Iso.rightInv lem x = refl
-- --   Iso.leftInv lem (inl x) = (λ i → inr (snd α (~ i))) ∙ sym (push (inl tt))
-- --   Iso.leftInv lem (inr x) = refl
-- --   Iso.leftInv lem (push (inl x) i) j =
-- --     compPath-filler'' (λ i → inr (snd α (~ i))) (sym (push (inl tt))) (~ i) j

-- --   main : (t : _) (sndf : _ ≡ t)
-- --     → PathP (λ i → Iso.leftInv lem t (~ i) ≡ inl tt)
-- --              (sym sndf)
-- --              ((λ i → inr (((λ i₁ → Iso.fun lem (sndf (~ i₁))) ∙ refl) i))
-- --               ∙ (λ i → inr (snd α (~ i))) ∙ (λ i → push (inl tt) (~ i)))
-- --   main = J> ((λ i j → ((λ i₁ → inr (snd α (~ i₁)))
-- --                      ∙ (sym (push (inl tt)))) (~ i ∨ j))
-- --     ▷ (lUnit _
-- --     ∙ cong₂ _∙_ (rUnit refl ∙ sym (cong-∙ inr refl refl))
-- --                 refl))
-- intoCofib n m k α f = {!!}
--   where
--   conFib : isConnected 2 (fiber (fst f) (inl tt))
--   conFib = ∣ (ptSn (suc n)) , (snd f) ∣
--          , (TR.elim (λ _ → isOfHLevelPath 2 (isOfHLevelTrunc 2) _ _)
--             (uncurry (sphereElim n (λ _ → isOfHLevelΠ (suc n)
--               λ _ → isProp→isOfHLevelSuc n (isOfHLevelTrunc 2 _ _))
--               λ y → TR.rec {!!} {!!}
--               (isConnectedPath 1
--                (isConnectedPath 2 {A = cofib (fst α)}
--                 {!!} (fst f (ptSn (suc n))) (inl tt)) (snd f) y .fst))))

--   conCofib : isConnectedFun 2 (fst f)
--   conCofib = PO.elimProp _ (λ _ → isPropIsContr)
--     (λ { tt → conFib})
--     (PO.elimProp _ (λ _ → isPropIsContr)
--       (λ { tt → subst (isConnected 2 ∘ (fiber (fst f)))
--                   (push (inl tt) ∙ (λ i → inr (snd α i))) conFib})
--       (uncurry λ k → sphereElim n (λ _ → isProp→isOfHLevelSuc n isPropIsContr)
--         (subst (isConnected 2 ∘ (fiber (fst f)))
--           ((push (inl tt) ∙ (λ i → inr (snd α i)))
--                           ∙ (λ i → inr (push k i))) conFib)))

--   conCofib' : isConnectedFun 1 (fst f)
--   conCofib' = {!!} -- PO.elimProp _ (λ _ → isPropIsContr)

--   ooh : ∥ ((k : Fin k) (x : _) → fiber (fst f) (inr x)) ∥₁
--   ooh = {!!}

--   main : ∥ ((x : S₊ (suc n)) → Σ[ s ∈ SphereBouquet (suc n) (Fin k) ]
--            (Σ[ t ∈ ((p : ptSn (suc n) ≡ x) → s ≡ inl tt) ] 
--             Σ[ h ∈ (f .fst x ≡ inr s) ]
--             (((p : ptSn (suc n) ≡ x)
--             → Square (snd f) (cong inr (t p))
--                       (cong (fst f) p ∙ h)
--                       (sym ((λ i → inr (snd α (~ i))) ∙ sym (push (inl tt)))))))) ∥₁
--   main = sphereToTrunc (suc n) λ x → PT.rec {!!}
--     (λ F → ∣ inr ({!!} , {!F!}) , {!!} ∣ₕ) ooh

--   s = inrConnected 2 (fst α) (λ _ → tt) {!approxSphereMap∙ !}
