{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Inductive.Base
open import Cubical.Data.Fin.Inductive.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.CW
open import Cubical.Data.Sequence
open import Cubical.Data.CW.ChainComplex
open import Cubical.Algebra.ChainComplex


open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp

open import Cubical.Relation.Nullary
open import Cubical.Structures.Successor

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

-- open import cw-chain-complex
-- open import ChainComplex

open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Natindexed


module subcomplex where


private
  variable
    ℓ ℓ' ℓ'' : Level



-- finite subcomplex
module _ (C : CWskel ℓ) where
  subComplexFam : (n : ℕ) (m : ℕ) → Type ℓ
  subComplexFam n m with (m ≟ᵗ n)
  ... | lt x = fst C m
  ... | eq x = fst C m
  ... | gt x = fst C n

  subComplexCard : (n : ℕ) → ℕ → ℕ
  subComplexCard n m with (m ≟ᵗ n)
  ... | lt x = snd C .fst m
  ... | eq x = 0
  ... | gt x = 0

  subComplexα : (n m : ℕ) → Fin (subComplexCard n m) × S⁻ m → subComplexFam n m
  subComplexα n m with (m ≟ᵗ n)
  ... | lt x = snd C .snd .fst m
  ... | eq x = λ x → ⊥.rec (¬Fin0 (fst x))
  ... | gt x = λ x → ⊥.rec (¬Fin0 (fst x))

  subComplex₀-empty : (n : ℕ) → ¬ subComplexFam n zero
  subComplex₀-empty n with (zero ≟ᵗ n)
  ... | lt x = CW₀-empty C
  ... | eq x = CW₀-empty C
  ... | gt x = λ _ → ¬-<-zero x

  subComplexFam≃Pushout : (n m : ℕ)
    → subComplexFam n (suc m) ≃ Pushout (subComplexα n m) fst
  subComplexFam≃Pushout n m with (m ≟ᵗ n) | ((suc m) ≟ᵗ n)
  ... | lt x | lt x₁ = snd C .snd .snd .snd m
  ... | lt x | eq x₁ = snd C .snd .snd .snd m
  ... | lt x | gt x₁ = ⊥.rec (¬-<-suc x x₁)
  ... | eq x | lt x₁ = ⊥.rec (¬m<m (subst (_< n) x (<-trans (0 , refl) x₁)))
  ... | eq x | eq x₁ = ⊥.rec (¬m<m (0 , x₁ ∙ sym x))
  ... | eq x | gt x₁ =
    compEquiv (pathToEquiv (λ i → fst C (x (~ i))))
              (isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0))
  ... | gt x | lt x₁ =
    ⊥.rec (¬-suc-n<n (<-trans (suc-≤-suc x) x₁))
  ... | gt x | eq x₁ =
    ⊥.rec (<-asym (<-trans (0 , refl) (subst (_< suc n) (sym x₁) (0 , refl))) x)
  ... | gt x | gt x₁ = isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0)

  subComplexYieldsCWskel : (n : ℕ) → yieldsCWskel (subComplexFam n)
  fst (subComplexYieldsCWskel n) = subComplexCard n
  fst (snd (subComplexYieldsCWskel n)) = subComplexα n
  fst (snd (snd (subComplexYieldsCWskel n))) = subComplex₀-empty n
  snd (snd (snd (subComplexYieldsCWskel n))) m = subComplexFam≃Pushout n m

  subComplex : (n : ℕ) → CWskel ℓ
  fst (subComplex n) = subComplexFam n
  snd (subComplex n) = subComplexYieldsCWskel n

  subComplexFin : (n m : ℕ) (p : n ≤ m)
    → isEquiv (CW↪ (subComplexFam n , subComplexYieldsCWskel n) m)
  subComplexFin n m r with (m ≟ᵗ n) | (suc m ≟ᵗ n)
  ... | lt x | p = ⊥.rec (¬m<m (≤-trans x r))
  ... | eq x | lt x₁ = ⊥.rec (¬m<m (subst (_< n) x (<-trans (0 , refl) x₁)))
  ... | eq x | eq x₁ = ⊥.rec (⊥.rec (¬m<m (0 , x₁ ∙ sym x)))
  ... | eq x | gt x₁ =
    subst isEquiv (funExt λ x → cong (help .fst)
          (retEq (isoToEquiv (PushoutEmptyFam {A = Fin 0 × fst C m}
                  (λ x₃ → ¬Fin0 (fst x₃)) ¬Fin0 {f = snd} {g = fst})) x))
                  (help .snd)
      where
      help : fst C m ≃ fst C n
      help = invEquiv (pathToEquiv (λ i → fst C (x (~ i))))
  ... | gt x | lt x₁ =
    ⊥.rec (¬-suc-n<n (<-trans (suc-≤-suc x) x₁))
  ... | gt x | eq x₁ =
    ⊥.rec (<-asym (<-trans (0 , refl) (subst (_< suc n) (sym x₁) (0 , refl))) x)
  ... | gt x | gt x₁ =
    subst isEquiv (funExt (retEq (isoToEquiv (PushoutEmptyFam {A = Fin 0 × fst C n}
                          (λ x₃ → ¬Fin0 (fst x₃)) ¬Fin0 {f = snd} {g = fst}))))
                  (idEquiv _ .snd)

  subComplexYieldsFinCWskel : (n : ℕ) → yieldsFinCWskel n (subComplexFam n)
  fst (subComplexYieldsFinCWskel n) = subComplexYieldsCWskel n
  snd (subComplexYieldsFinCWskel n) k = subComplexFin n (k +ℕ n) (k , refl)

  finSubComplex : (n : ℕ) → finCWskel ℓ n
  fst (finSubComplex n) = subComplexFam n
  snd (finSubComplex n) = subComplexYieldsFinCWskel n

  complex≃subcomplex : (n m : ℕ) → m ≤ n → fst C m ≃ subComplex n .fst m
  complex≃subcomplex n m p with (m ≟ᵗ n)
  ... | lt x = idEquiv _
  ... | eq x = idEquiv _
  ... | gt x = ⊥.rec (¬m<m (≤-trans x p))

realiseSubComplex : (n : ℕ) (C : CWskel ℓ) → Iso (fst C n) (realise (subComplex C n))
realiseSubComplex n C =
  compIso (equivToIso (complex≃subcomplex C n n (0 , refl)))
          (realiseFin n (finSubComplex C n))

module _ (C : CWskel ℓ) where
  ChainSubComplex : (n : ℕ) → snd C .fst n ≡ snd (subComplex C (suc n)) .fst n
  ChainSubComplex n with (n ≟ᵗ suc n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<m (0 , sym x))
  ... | gt x = ⊥.rec (¬-suc-n<n x)

  ≤ChainSubComplex : (n m : ℕ) → m < n → snd C .fst m ≡ snd (subComplex C n) .fst m
  ≤ChainSubComplex n m p with (m ≟ᵗ n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<m (subst (_< n) x p))
  ... | gt x = ⊥.rec (¬m<m (<-trans x p))


subChainIso : (C : CWskel ℓ) (n m : ℕ) (p : m < n)
  → AbGroupIso (CWskel-fields.ℤ[A_] C m) (CWskel-fields.ℤ[A_] (subComplex C n) m)
subChainIso C n m p with (m ≟ᵗ n)
... | lt x = idGroupIso
... | eq x = ⊥.rec (¬m<m (subst (m <_) (sym x) p))
... | gt x = ⊥.rec (¬m<m (<-trans x p))

subComplexHomology : (C : CWskel ℓ) (n m : ℕ) (p : suc (suc m) < n)
  → GroupIso (Hᶜʷ C m) (Hᶜʷ (subComplex C n) m)
subComplexHomology C n m p =
  homologyIso (m , _) _ _
    (subChainIso C n (suc (suc m)) p)
    (subChainIso C n (suc m) (<-trans (0 , refl) p))
    (subChainIso C n m (<-trans (0 , refl) (<-trans (0 , refl) p)))
    lem₁
    lem₂
  where
  lem₁ : {q : _} {r : _}
    → Iso.fun (subChainIso C n m q .fst) ∘ ∂ C m .fst
    ≡ ∂ (subComplex C n) m .fst
     ∘ Iso.fun (subChainIso C n (suc m) r .fst)
  lem₁ {q} {r} with (m ≟ᵗ n) | (suc m ≟ᵗ n) | (suc (suc m) ≟ᵗ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze< (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<m (subst (_< n) x₁ r))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<m (<-trans x₁ r))
  ... | eq x | s | t = ⊥.rec (¬-suc-n<n (subst (suc m <_) (sym x) r))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<n (<-trans r x))

  lem₂ : {q : suc m < n} {r : (suc (suc m)) < n}
    → Iso.fun (subChainIso C n (suc m) q .fst)
     ∘ ∂ C (suc m) .fst
     ≡ ∂ (subComplex C n) (suc m) .fst
     ∘ Iso.fun (subChainIso C n (suc (suc m)) r .fst)
  lem₂ {q} with (suc m ≟ᵗ n) | (suc (suc m) ≟ᵗ n) | (suc (suc (suc m)) ≟ᵗ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze< (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<m (subst (_< n) x₁ p))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<m (<-trans x₁ p))
  ... | eq x | s | t = ⊥.rec (¬m<m (subst (suc m <_) (sym x) q))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<n (<-trans p x))

open import CWHomotopy
open import fin-cw-map

open import Cubical.Foundations.Transport
restrCellMap : (C : CWskel ℓ) (D : CWskel ℓ') (f : cellMap C D) (m : ℕ)
  → cellMap (subComplex C m) (subComplex D m)
SequenceMap.map (restrCellMap C D f m) n k with (n ≟ᵗ m)
... | lt x = SequenceMap.map f n k
... | eq x = SequenceMap.map f n k
... | gt x = SequenceMap.map f m k
SequenceMap.comm (restrCellMap C D f m) n x with (suc n ≟ᵗ m) | (n ≟ᵗ m)
... | lt x₁ | lt x₂ = SequenceMap.comm f n x
... | lt x₁ | eq x₂ = rec (¬m<m (subst (_< m) x₂ (<-trans (0 , (λ _ → suc n)) x₁)))
... | lt x₁ | gt x₂ = rec (¬-suc-n<n (<-trans (suc-≤-suc x₂) x₁))
... | eq x₁ | lt x₂ = SequenceMap.comm f n x
... | eq x₁ | eq x₂ = rec (¬m<m (0 , (x₁ ∙ sym x₂)))
... | eq x₁ | gt x₂ = rec (¬-suc-n<n (subst (_< n) (sym x₁) x₂))
... | gt x₁ | lt x₂ = rec (¬-<-suc x₂ x₁)
... | gt x₁ | eq x₂ =
      transportRefl _
    ∙ substCommSlice (fst C) (fst D) (SequenceMap.map f) x₂ x
    ∙ cong (SequenceMap.map f m) (sym (transportRefl _))
... | gt x₁ | gt x₂ = refl

Hᶜʷ→finite : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
  (f : cellMap C D)
  → GroupHom (Hᶜʷ (subComplex C (3 +ℕ m)) m) (Hᶜʷ (subComplex D (3 +ℕ m)) m)
Hᶜʷ→finite C D m f = ϕ
  where
  ϕ = chainComplexMap→HomologyMap
         {C = CW-ChainComplex (subComplex C (3 +ℕ m))}
         {D = CW-ChainComplex (subComplex D (3 +ℕ m))}
         (cellMap-to-ChainComplexMap (restrCellMap C D f (3 +ℕ m)))
         (m , _)

Hᶠᶜʷ : (m : ℕ) (C : finCWskel ℓ m) (n : ℕ) → Group₀
Hᶠᶜʷ m C n = Hᶜʷ (finCWskel→CWskel m C) n


open import Cubical.HITs.PropositionalTruncation as PT
open import cw-approx2

-- module _ (k : ℕ) (n m : ℕ) {C : finCWskel ℓ n} {D : finCWskel ℓ' m}
--         (f : realise (finCWskel→CWskel n C) → realise (finCWskel→CWskel m D)) where

--   cellMap→Hᶠᶜʷ-hom : cellMap (finCWskel→CWskel n C) (finCWskel→CWskel m D) → GroupHom (Hᶠᶜʷ n C k) (Hᶠᶜʷ m D k)
--   cellMap→Hᶠᶜʷ-hom ϕ = chainComplexMap→HomologyMap (cellMap-to-ChainComplexMap ϕ) (k , _)

--   cellMap→Hᶠᶜʷ-hom-coh : (p q : Σ[ r ∈ (cellMap (finCWskel→CWskel n C) (finCWskel→CWskel m D)) ]
--                                        (realiseSequenceMap r ≡ f))
--       → cellMap→Hᶠᶜʷ-hom (fst p) ≡ cellMap→Hᶠᶜʷ-hom (fst q)
--   cellMap→Hᶠᶜʷ-hom-coh p q = PT.rec (isSetGroupHom _ _)
--       ((λ ϕ → ChainHomotopy→HomologyPath (cellMap-to-ChainComplexMap (fst p))
--                                           (cellMap-to-ChainComplexMap (fst q))
--                                           (cellHom-to-ChainHomotopy ϕ)
--                                           (k , ≠suc)))
--       (cellHomotopy₁ n m (fst p) (fst q) (snd p ∙ sym (snd q)))

--   Hᶠᶜʷ→ : GroupHom (Hᶠᶜʷ n C k) (Hᶠᶜʷ m D k)
--   Hᶠᶜʷ→ = rec→Set isSetGroupHom
--                   (cellMap→Hᶠᶜʷ-hom ∘ fst)
--                   (cellMap→Hᶠᶜʷ-hom-coh)
--                   (finMap→cellMap₁ n m C D f)


-- rewriteHᶠᶜʷ : (k : ℕ) (n m : ℕ) {C : finCWskel ℓ n} {D : finCWskel ℓ' m}
--      → (f : realise (finCWskel→CWskel n C) → realise (finCWskel→CWskel m D))
--      → (g : cellMap (finCWskel→CWskel n C) (finCWskel→CWskel m D))
--      → (realiseCellMap g ≡ f)
--      → Hᶠᶜʷ→ k n m f ≡ cellMap→Hᶠᶜʷ-hom k n m f g
-- rewriteHᶠᶜʷ k n m {C = C} {D = D} f g p = main
--   where
--   finMap→cellMap₁-path : finMap→cellMap₁ n m C D f ≡ ∣ g , p ∣₁
--   finMap→cellMap₁-path = squash₁ _ _

--   main : Hᶠᶜʷ→ k n m f ≡ cellMap→Hᶠᶜʷ-hom k n m f g
--   main = cong (rec→Set isSetGroupHom
--               (cellMap→Hᶠᶜʷ-hom k n m {C = C} {D} f ∘ fst)
--               (cellMap→Hᶠᶜʷ-hom-coh k n m {C = C} {D} f))
--               finMap→cellMap₁-path

-- cellMap-to-ChainComplexMapId : (C : CWskel ℓ)
--   → cellMap-to-ChainComplexMap {C = C} (idCellMap C) ≡ idChainMap _
-- cellMap-to-ChainComplexMapId C = ChainComplexMap≡ λ i _ → chainFunct-id C i

-- cellMap-to-ChainComplexMapComp : {C : CWskel ℓ} {D : CWskel ℓ'} {E : CWskel ℓ''}
--   (g : cellMap D E) (f : cellMap C D)
--   → cellMap-to-ChainComplexMap (composeCellMap g f)
--   ≡ compChainMap (cellMap-to-ChainComplexMap f) (cellMap-to-ChainComplexMap g)
-- cellMap-to-ChainComplexMapComp g f = ChainComplexMap≡ λ n _ → sym (chainFunct-comp g f n)

-- Hᶠᶜʷ→-id : (k : ℕ) (n : ℕ) {C : finCWskel ℓ n}
--   → Hᶠᶜʷ→ k n n {C = C} {D = C} (idfun _) ≡ idGroupHom
-- Hᶠᶜʷ→-id k n {C = C} =
--     rewriteHᶠᶜʷ k n n {C = C} (idfun _) (idCellMap _) realiseIdSequenceMap
--   ∙ (λ j → chainComplexMap→HomologyMap
--              (cellMap-to-ChainComplexMapId
--                (finCWskel→CWskel n C) j) (k , ≠suc))
--   ∙ chainComplexMap→HomologyMapId (k , ≠suc)

-- Hᶠᶜʷ→comp : (k : ℕ) (n m r : ℕ)
--   {C : finCWskel ℓ n} {D : finCWskel ℓ' m} {E : finCWskel ℓ'' r}
--   (g : realise (finCWskel→CWskel m D) → realise (finCWskel→CWskel r E))
--   (f : realise (finCWskel→CWskel n C) → realise (finCWskel→CWskel m D))
--   → Hᶠᶜʷ→ k n r {C = C} {D = E} (g ∘ f)
--    ≡ compGroupHom (Hᶠᶜʷ→ k n m f) (Hᶠᶜʷ→ k m r g)
-- Hᶠᶜʷ→comp k n m r {C = C} {D = D} {E = E} g f =
--   PT.rec2 (isSetGroupHom _ _)
--     (λ {(F , fp) (G , gp)
--    → rewriteHᶠᶜʷ k n r (g ∘ f) (composeCellMap G F)
--           (realiseCompSequenceMap G F ∙ (λ i x → gp i (fp i x)))
--     ∙ cong (λ f → chainComplexMap→HomologyMap f (k , ≠suc))
--                (cellMap-to-ChainComplexMapComp G F)
--     ∙ chainComplexMap→HomologyMapComp _ _ (k , ≠suc)
--     ∙ cong₂ compGroupHom (sym (rewriteHᶠᶜʷ k n m f F fp))
--                          (sym (rewriteHᶠᶜʷ k m r g G gp))})
--     (finMap→cellMap₁ n m C D f)
--     (finMap→cellMap₁ m r D E g)

-- Hᶠᶜʷ→≃ : (k : ℕ) (n m : ℕ) {C : finCWskel ℓ n} {D : finCWskel ℓ' m}
--   (f : realise (finCWskel→CWskel n C) ≃ realise (finCWskel→CWskel m D))
--   → GroupEquiv (Hᶠᶜʷ n C k) (Hᶠᶜʷ m D k)
-- fst (Hᶠᶜʷ→≃ k n m {C = C} {D = D} f) = isoToEquiv ϕ
--   where
--   ϕ : Iso (Hᶠᶜʷ n C k .fst) (Hᶠᶜʷ m D k .fst)
--   Iso.fun ϕ = Hᶠᶜʷ→ k n m (fst f) .fst
--   Iso.inv ϕ = Hᶠᶜʷ→ k m n (invEq f) .fst
--   Iso.rightInv ϕ =
--     funExt⁻ (cong fst (sym (Hᶠᶜʷ→comp k m n m (fst f) (invEq f))
--           ∙ cong (Hᶠᶜʷ→ k m m) (funExt (secEq f))
--           ∙ Hᶠᶜʷ→-id k m))
--   Iso.leftInv ϕ =
--     funExt⁻ (cong fst (sym (Hᶠᶜʷ→comp k n m n (invEq f) (fst f))
--           ∙ cong (Hᶠᶜʷ→ k n n) (funExt (retEq f))
--           ∙ Hᶠᶜʷ→-id k n))
-- snd (Hᶠᶜʷ→≃ k n m {C = C} {D = D} f) = Hᶠᶜʷ→ k n m (fst f) .snd

-- open import Cubical.Algebra.Group.GroupPath

-- module _ (X : Type ℓ) (n : ℕ) where
--   HᶠGr : isFinCW X → Group ℓ-zero
--   HᶠGr (m , C) = Hᶠᶜʷ m (C .fst) n

--   HᶠGr-eq : (XC YC : isFinCW X) → GroupEquiv (HᶠGr XC) (HᶠGr YC)
--   HᶠGr-eq (m , XC , e1) (k , YC , e2) =
--     Hᶠᶜʷ→≃ n m k {C = XC} {D = YC} (compEquiv (invEquiv e1) e2)

--   HᶠGr-eq-coh : (x y z : isFinCW X) →
--       fst (fst (HᶠGr-eq y z)) ∘ (fst (fst (HᶠGr-eq x y)))
--     ≡ fst (fst (HᶠGr-eq x z))
--   HᶠGr-eq-coh (m , XC , e1) (k , YC , e2) (r , ZC , e3) =
--     sym (cong fst (Hᶠᶜʷ→comp n _ _ _
--            (compEquiv (invEquiv e2) e3 .fst)
--            (compEquiv (invEquiv e1) e2 .fst)))
--     ∙ cong (fst ∘ Hᶠᶜʷ→ n m r)
--        (funExt λ y → cong (fst e3) (retEq e2 (invEquiv e1 .fst y)))

-- Hᶠ : finCW ℓ → ℕ → Group₀
-- Hᶠ (X , A) n =
--   PropTrunc→Group (HᶠGr X n)
--     (HᶠGr-eq X n)
--     (λ x y z → funExt⁻ (HᶠGr-eq-coh X n x y z))
--     A

-- module _ (X : finCW ℓ) (Y : finCW ℓ') (n : ℕ) (f : fst X → fst Y) where
--   module Hᶠ→-constr where
--     X' = fst X
--     Y' = fst Y

--     ϕ₁-fun : (XC : isFinCW X') (YC : isFinCW Y')
--       → GroupHom (Hᶠ (X' , ∣ XC ∣₁) n) (Hᶠ (Y' , ∣ YC ∣₁) n)
--     ϕ₁-fun XC YC = Hᶠᶜʷ→ n (fst XC) (fst YC)
--                     (fst (snd (snd YC)) ∘ f ∘ invEq (snd (snd XC)))

--     ϕ₁-fun-coh : (XC : isFinCW X') (YC YC' : isFinCW Y')
--       → PathP (λ i → GroupHom (Hᶠ (X' , ∣ XC ∣₁) n)
--                                 (Hᶠ (Y' , squash₁ ∣ YC ∣₁ ∣ YC' ∣₁ i) n))
--                (ϕ₁-fun XC YC) (ϕ₁-fun XC YC')
--     ϕ₁-fun-coh XC YC YC' =
--       toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
--                ((λ i x → transportRefl ((Hᶠᶜʷ→ n (fst YC) (fst YC')
--                             (fst (snd (snd YC')) ∘ invEq (snd (snd YC)))) .fst
--                               (Hᶠᶜʷ→ n (fst XC) (fst YC)
--                                (λ x₁ → fst (snd (snd YC)) (f (invEq (snd (snd XC)) x₁)))
--                                .fst (transportRefl x i))) i)
--               ∙ cong fst (sym (Hᶠᶜʷ→comp n (fst XC) (fst YC) (fst YC')
--                              (fst (snd (snd YC')) ∘ invEq (snd (snd YC)))
--                              (fst (snd (snd YC)) ∘ f ∘ invEq (snd (snd XC))))
--                       ∙ cong (Hᶠᶜʷ→ n (fst XC) (fst YC'))
--                           (funExt (λ x → cong (fst (snd (snd YC')))
--                             (retEq (snd (snd YC)) (f (invEq (snd (snd XC)) x))))))))

--     ϕ₁ : (XC : isFinCW X') (YC : ∥ isFinCW Y' ∥₁)
--       → GroupHom (Hᶠ (X' , ∣ XC ∣₁) n) (Hᶠ (Y' , YC) n)
--     ϕ₁ XC = elim→Set (λ _ → isSetGroupHom)
--               (ϕ₁-fun XC)
--               (ϕ₁-fun-coh XC)

--     ϕ₁≡ : (XC : isFinCW X') (YC : isFinCW Y') → ϕ₁ XC ∣ YC ∣₁ ≡ ϕ₁-fun XC YC
--     ϕ₁≡ XC = elim→Setβ {P = λ YC → GroupHom (Hᶠ (X' , ∣ XC ∣₁) n) (Hᶠ (Y' , YC) n)}
--               (λ _ → isSetGroupHom)
--               (ϕ₁-fun XC)
--               (ϕ₁-fun-coh XC)

--     ϕ₂ : (XC XC' : isFinCW X') (YC : ∥ isFinCW Y' ∥₁)
--       → transport (λ z → GroupHom (Hᶠ (X' , squash₁ ∣ XC ∣₁ ∣ XC' ∣₁ z) n) (Hᶠ (Y' , YC) n))
--                     (ϕ₁ XC YC) .fst
--        ≡ ϕ₁ XC' YC .fst
--     ϕ₂ XC XC' = PT.elim
--       (λ YC → isOfHLevelPath' 1 (isSetΠ (λ _ → GroupStr.is-set (snd (Hᶠ (Y' , YC) n)))) _ _)
--       λ YC → funExt
--         (λ x → transportRefl (ϕ₁ XC ∣ YC ∣₁ .fst
--                  (transport (λ j → Hᶠ (X' , squash₁ ∣ XC ∣₁ ∣ XC' ∣₁ (~ j)) n .fst) x))
--              ∙ (cong (ϕ₁ XC ∣ YC ∣₁ .fst)
--                λ i → Hᶠᶜʷ→ n (fst XC') (fst XC)
--                        (fst (snd (snd XC)) ∘ invEq (snd (snd XC'))) .fst
--                        (transportRefl x i))
--             ∙ funExt⁻ (cong fst (ϕ₁≡ XC YC))
--                (Hᶠᶜʷ→ n (fst XC') (fst XC)
--                  (fst (snd (snd XC)) ∘ invEq (snd (snd XC'))) .fst x))
--       ∙ (sym (cong fst
--          (cong (Hᶠᶜʷ→ n (fst XC') (fst YC))
--             (funExt (λ a
--               → cong (fst (snd (snd YC)) ∘ f)
--                   (sym (retEq (snd (snd XC)) (invEq (snd (snd XC')) a)))))
--         ∙ Hᶠᶜʷ→comp n (fst XC') (fst XC) (fst YC)
--            (fst (snd (snd YC)) ∘ f ∘ invEq (snd (snd XC)))
--            (fst (snd (snd XC)) ∘ invEq (snd (snd XC'))))))
--       ∙ cong fst (sym (ϕ₁≡ XC' YC))

--     ϕ : (XC : ∥ isFinCW X' ∥₁) (YC : ∥ isFinCW Y' ∥₁)
--       → GroupHom (Hᶠ (X' , XC) n) (Hᶠ (Y' , YC) n)
--     ϕ = elim→Set (λ _ → isSetΠ λ _ → isSetGroupHom)
--          ϕ₁
--          λ XC XC' → funExt λ YC → toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
--            (ϕ₂ XC XC' YC))

--   Hᶠ→ : GroupHom (Hᶠ X n) (Hᶠ Y n)
--   Hᶠ→ = Hᶠ→-constr.ϕ (X .snd) (Y .snd)

-- Hᶠ→β : {X : Type ℓ} {Y : Type ℓ'} {XC : isFinCW X} {YC : isFinCW Y}  (n : ℕ) (f : X → Y)
--   → Hᶠ→ (X , ∣ XC ∣₁) (Y , ∣ YC ∣₁) n f
--    ≡ Hᶠᶜʷ→ n _ _ (fst (snd (snd YC)) ∘ f ∘ invEq (snd (snd XC)))
-- Hᶠ→β {X = X} {Y = Y} {XC = XC} {YC} n f =
--     funExt⁻ (lem XC) ∣ YC ∣₁
--   ∙ Hᶠ→-constr.ϕ₁≡ _ _ n f XC YC
--   where
--   lem = elim→Setβ {P = λ XC → (YC : ∥ isFinCW Y ∥₁)
--                       → GroupHom (Hᶠ (X , XC) n) (Hᶠ (Y , YC) n)}
--         (λ _ → isSetΠ λ _ → isSetGroupHom)
--         (Hᶠ→-constr.ϕ₁ (X , ∣ XC ∣₁) (Y , ∣ YC ∣₁) n f)
--         λ XC XC' → funExt λ YC → toPathP (Σ≡Prop (λ _ → isPropIsGroupHom _ _)
--            (Hᶠ→-constr.ϕ₂ _ _ n f XC XC' YC))

-- Hᶠ→id : {C : finCW ℓ} (n : ℕ) → Hᶠ→ C C n (idfun _) ≡ idGroupHom
-- Hᶠ→id {C = C , XC} n =
--   PT.elim {P = λ XC → Hᶠ→ (C , XC) (C , XC) n (idfun C) ≡ idGroupHom}
--     (λ _ → isSetGroupHom _ _)
--     (λ XC → Hᶠ→β n (idfun C)
--           ∙ cong (Hᶠᶜʷ→ n (fst XC) (fst XC))
--                (funExt (secEq (snd (snd XC))))
--           ∙ Hᶠᶜʷ→-id n (fst XC)) XC

-- Hᶠ→comp : {C : finCW ℓ} {D : finCW ℓ'} {E : finCW ℓ''} (n : ℕ)
--   (g : fst D → fst E) (f : fst C → fst D)
--   → compGroupHom (Hᶠ→ C D n f) (Hᶠ→ D E n g)
--    ≡ Hᶠ→ C E n (g ∘ f)
-- Hᶠ→comp {C = C , XC} {D = D , XD} {E = E , XE} n g f =
--   PT.elim3 {P = λ XC XD XE
--     → compGroupHom (Hᶠ→ (C , XC) (D , XD) n f)
--                     (Hᶠ→ (D , XD) (E , XE) n g)
--      ≡ Hᶠ→ (C , XC) (E , XE) n (g ∘ f)}
--      (λ _ _ _ → isSetGroupHom _ _)
--      (λ XC XD XE
--      → cong₂ compGroupHom (Hᶠ→β n f) (Hᶠ→β n g)
--      ∙∙ sym (Hᶠᶜʷ→comp _ _ _ _ _ _)
--      ∙∙ cong (Hᶠᶜʷ→ n (fst XC) (fst XE))
--           (funExt (λ p → cong (fst (snd (snd XE)) ∘ g)
--             (retEq (snd (snd XD)) _)))
--       ∙ sym (Hᶠ→β n (g ∘ f)))
--      XC XD XE

-- -- Hᶜʷ→ : (C : CWskel ℓ) (D : CWskel ℓ') (f : realise C → realise D) (m : ℕ)
-- --   → GroupHom (Hᶜʷ C m) (Hᶜʷ D m)
-- -- Hᶜʷ→ C D f m =
-- --   compGroupHom ϕ₁
-- --     (compGroupHom (Hᶠᶜʷ→ m (3 +ℕ m) (3 +ℕ m) {!Hᶜʷ→finite C D m f!}) -- (Hᶜʷ→finite C D m f)
-- --       ϕ₂)
-- --   where
-- --   ϕ₁≅ : GroupIso (Hᶜʷ C m) (Hᶜʷ (subComplex C (3 +ℕ m)) m)
-- --   ϕ₁≅ = subComplexHomology C (3 +ℕ m) m (0 , refl)

-- --   ϕ₂≅ : GroupIso (Hᶜʷ D m) (Hᶜʷ (subComplex D (3 +ℕ m)) m)
-- --   ϕ₂≅ = subComplexHomology D (3 +ℕ m) m (0 , refl)

-- --   ϕ₁ : GroupHom (Hᶜʷ C m) (Hᶜʷ (subComplex C (suc (suc (suc m)))) m)
-- --   ϕ₁ = GroupIso→GroupHom ϕ₁≅

-- --   ϕ₂ : GroupHom (Hᶜʷ (subComplex D (3 +ℕ m)) m) (Hᶜʷ D m)
-- --   ϕ₂ = GroupIso→GroupHom (invGroupIso ϕ₂≅)

-- -- Hᶜʷ→id : {!Hᶠᶜʷ→!}
-- -- Hᶜʷ→id = {!!}

-- -- Hᶜʷ→comp : {!!}
-- -- Hᶜʷ→comp = {!!}

-- -- open import Cubical.HITs.SetTruncation as ST
-- -- CW→finCW : ∀ {ℓ} (n : ℕ) → CW ℓ → Group₀
-- -- CW→finCW n = uncurry λ X
-- --   → PropTrunc→Group
-- --        (λ XC → Hᶜʷ (fst XC) n)
-- --        (λ XC YC → {! -- Hᶜʷ→ (fst XC) (fst YC) ? n!})
-- --        {!!}


