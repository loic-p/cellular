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
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import prelude
open import spherebouquet
open import cw-complex
open import cw-chain-complex
open import ChainComplex

module subcomplex where

-- finite subcomplex
module _ (C : CW) where
  subComplexFam : (n : ℕ) (m : ℕ) → Type
  subComplexFam n m with (m ≟ n)
  ... | lt x = fst C m
  ... | eq x = fst C m
  ... | gt x = fst C n

  subComplexCard : (n : ℕ) → ℕ → ℕ
  subComplexCard n m with (m ≟ n)
  ... | lt x = snd C .fst m
  ... | eq x = 0
  ... | gt x = 0

  subComplexα : (n m : ℕ) → Fin (subComplexCard n m) × S⁻ m → subComplexFam n m
  subComplexα n m with (m ≟ n)
  ... | lt x = snd C .snd .fst m
  ... | eq x = λ x → ⊥.rec (¬Fin0 (fst x))
  ... | gt x = λ x → ⊥.rec (¬Fin0 (fst x))

  subComplex₀-empty : (n : ℕ) → ¬ subComplexFam n zero
  subComplex₀-empty n with (zero ≟ n)
  ... | lt x = CW₀-empty C
  ... | eq x = CW₀-empty C
  ... | gt x = λ _ → ¬-<-zero x

  subComplexFam≃Pushout : (n m : ℕ)
    → subComplexFam n (suc m) ≃ Pushout (subComplexα n m) fst
  subComplexFam≃Pushout n m with (m ≟ n) | ((suc m) ≟ n)
  ... | lt x | lt x₁ = snd C .snd .snd .snd m
  ... | lt x | eq x₁ = snd C .snd .snd .snd m
  ... | lt x | gt x₁ = ⊥.rec (¬-<-suc x x₁)
  ... | eq x | lt x₁ = ⊥.rec (¬m<m (subst (_< n) x (<-trans (0 , refl) x₁)))
  ... | eq x | eq x₁ = ⊥.rec (snot (x₁ ∙ sym x))
  ... | eq x | gt x₁ =
    compEquiv (pathToEquiv (λ i → fst C (x (~ i))))
              (isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0))
  ... | gt x | lt x₁ =
    ⊥.rec (¬-suc-n<n (<-trans (suc-≤-suc x) x₁))
  ... | gt x | eq x₁ =
    ⊥.rec (<-asym (<-trans (0 , refl) (subst (_< suc n) (sym x₁) (0 , refl))) x)
  ... | gt x | gt x₁ = isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0)

  subComplexYieldsCW : (n : ℕ) → yieldsCW (subComplexFam n)
  fst (subComplexYieldsCW n) = subComplexCard n
  fst (snd (subComplexYieldsCW n)) = subComplexα n
  fst (snd (snd (subComplexYieldsCW n))) = subComplex₀-empty n
  snd (snd (snd (subComplexYieldsCW n))) m = subComplexFam≃Pushout n m

  subComplex : (n : ℕ) → CW
  fst (subComplex n) = subComplexFam n
  snd (subComplex n) = subComplexYieldsCW n

  subComplexFin : (n m : ℕ) (p : n ≤ m)
    → isEquiv (CW↪ (subComplexFam n , subComplexYieldsCW n) m)
  subComplexFin n m r with (m ≟ n) | (suc m ≟ n)
  ... | lt x | p = ⊥.rec (¬m<m (≤-trans x r))
  ... | eq x | lt x₁ = ⊥.rec (¬m<m (subst (_< n) x (<-trans (0 , refl) x₁)))
  ... | eq x | eq x₁ = ⊥.rec (snot (x₁ ∙ sym x))
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

  subComplexYieldsFinCW : (n : ℕ) → yieldsFinCW n (subComplexFam n)
  fst (subComplexYieldsFinCW n) = subComplexYieldsCW n
  snd (subComplexYieldsFinCW n) k = subComplexFin n (k +ℕ n) (k , refl)

  finSubComplex : (n : ℕ) → finCW n
  fst (finSubComplex n) = subComplexFam n
  snd (finSubComplex n) = subComplexYieldsFinCW n

  complex≃subcomplex : (n m : ℕ) → m ≤ n → fst C m ≃ subComplex n .fst m
  complex≃subcomplex n m p with (m ≟ n)
  ... | lt x = idEquiv _
  ... | eq x = idEquiv _
  ... | gt x = ⊥.rec (¬m<m (≤-trans x p))

-- module _ (n : ℕ) (C : finCW n) where
--   open CW-fields (finCW→CW n C)
--   private
--     Cᶜʷ = finCW→CW n C

--   finCWCoe₁ : (m : ℕ) → fst C m ≃ subComplex Cᶜʷ n .fst m
--   finCWCoe₁ m with (m ≟ n)
--   ... | lt x = idEquiv _
--   ... | eq x = idEquiv _
--   ... | gt x = invEquiv (finCW≃ n C m (<-weaken x))

--   finCWCoe₂₁ : (m : ℕ)
--     → PathP (λ i → yieldsCW λ m → ua (finCWCoe₁ m) i)
--              (fst (C .snd)) (subComplexYieldsCW Cᶜʷ n)
--   fst (finCWCoe₂₁ m i) = {!!}
--   fst (snd (finCWCoe₂₁ m i)) = {!!}
--   fst (snd (snd (finCWCoe₂₁ m i))) = {!!}
--   snd (snd (snd (finCWCoe₂₁ m i))) = {!!}

--   finCWCoe₂ : (m : ℕ)
--     → PathP (λ i → yieldsFinCW n λ m → ua (finCWCoe₁ m) i)
--              (C .snd) (subComplexYieldsFinCW Cᶜʷ n)
--   finCWCoe₂ m = {!!}

realiseSubComplex : (n : ℕ) (C : CW) → Iso (fst C n) (realise (subComplex C n))
realiseSubComplex n C =
  compIso (equivToIso (complex≃subcomplex C n n (0 , refl)))
          (realiseFin n (finSubComplex C n))

module _ (C : CW) where
  ChainSubComplex : (n : ℕ) → snd C .fst n ≡ snd (subComplex C (suc n)) .fst n
  ChainSubComplex n with (n ≟ suc n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (snot (sym x))
  ... | gt x = ⊥.rec (¬-suc-n<n x)

  ≤ChainSubComplex : (n m : ℕ) → m < n → snd C .fst m ≡ snd (subComplex C n) .fst m
  ≤ChainSubComplex n m p with (m ≟ n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<m (subst (_< n) x p))
  ... | gt x = ⊥.rec (¬m<m (<-trans x p))

-- needed?

-- subComplLem : (C : CW) (n : ℕ) (m : ℕ) (p : suc m < n)
--   → PathP (λ i → (SphereBouquet (suc m) (Fin (≤ChainSubComplex C n (suc m) p i))
--                →∙ SphereBouquet (suc m) (Fin (≤ChainSubComplex C n m (suc (fst p)
--                                      , sym (+-suc (fst p) (suc m)) ∙ snd p) i))))
--            (preboundary.pre∂ C m)
--            (preboundary.pre∂ (subComplex C n) m)
-- subComplLem c n m p with (m ≟ n) | (suc m ≟ n) | (suc (suc m) ≟ n)
-- ... | lt x | lt x₁ | lt x₂ = refl
-- ... | lt x | lt x₁ | eq x₂ = refl
-- ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze< (x₁ , x₂))
-- ... | lt x | eq x₁ | r = ⊥.rec (¬m<m (subst (_< n) x₁ p))
-- ... | lt x | gt x₁ | r = ⊥.rec (¬m<m (<-trans x₁ p))
-- ... | eq x | b | r = ⊥.rec (¬-suc-n<n (subst (suc m <_) (sym x) p))
-- ... | gt x | b | r = ⊥.rec (¬-suc-n<n (<-trans p x))

subChainIso : (C : CW) (n m : ℕ) (p : m < n)
  → AbGroupIso (ℤ[A C ] m) (ℤ[A subComplex C n ] m)
subChainIso C n m p with (m ≟ n)
... | lt x = idGroupIso
... | eq x = ⊥.rec (¬m<m (subst (m <_) (sym x) p))
... | gt x = ⊥.rec (¬m<m (<-trans x p))

subComplexHomology : (C : CW) (n m : ℕ) (p : suc (suc m) < n)
  → GroupIso (Hᶜʷ C m) (Hᶜʷ (subComplex C n) m)
subComplexHomology C n m p =
  homologyIso m _ _
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
  lem₁ {q} {r} with (m ≟ n) | (suc m ≟ n) | (suc (suc m) ≟ n)
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
  lem₂ {q} with (suc m ≟ n) | (suc (suc m) ≟ n) | (suc (suc (suc m)) ≟ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze< (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<m (subst (_< n) x₁ p))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<m (<-trans x₁ p))
  ... | eq x | s | t = ⊥.rec (¬m<m (subst (suc m <_) (sym x) q))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<n (<-trans p x))

open import CWHomotopy
open import cw-map

open import Cubical.Foundations.Transport
restrCellMap : (C D : CW) (f : cellMap C D) (m : ℕ)
  → cellMap (subComplex C m) (subComplex D m)
SequenceMap.map (restrCellMap C D f m) n k with (n ≟ m)
... | lt x = SequenceMap.map f n k 
... | eq x = SequenceMap.map f n k
... | gt x = SequenceMap.map f m k
SequenceMap.comm (restrCellMap C D f m) n x with (suc n ≟ m) | (n ≟ m)
... | lt x₁ | lt x₂ = SequenceMap.comm f n x
... | lt x₁ | eq x₂ = rec (¬m<m (subst (_< m) x₂ (<-trans (0 , (λ _ → suc n)) x₁)))
... | lt x₁ | gt x₂ = rec (¬-suc-n<n (<-trans (suc-≤-suc x₂) x₁))
... | eq x₁ | lt x₂ = SequenceMap.comm f n x
... | eq x₁ | eq x₂ = rec (snot (x₁ ∙ (λ i → x₂ (~ i))))
... | eq x₁ | gt x₂ = rec (¬-suc-n<n (subst (_< n) (sym x₁) x₂))
... | gt x₁ | lt x₂ = rec (¬-<-suc x₂ x₁)
... | gt x₁ | eq x₂ =
      transportRefl _
    ∙ substCommSlice (fst C) (fst D) (SequenceMap.map f) x₂ x
    ∙ cong (SequenceMap.map f m) (sym (transportRefl _))
... | gt x₁ | gt x₂ = refl

Hᶜʷ-sub : CW → ℕ → Group₀
Hᶜʷ-sub C m = Hᶜʷ (subComplex C (3 +ℕ m)) m

Hᶜʷ→finite : (C D : CW) (m : ℕ)
  (f : cellMap C D)
  → GroupHom (Hᶜʷ-sub C m) (Hᶜʷ-sub D m)
Hᶜʷ→finite C D m f = ϕ
  where
  ϕ = chainComplexMap→HomologyMap
         {C = CW-ChainComplex (subComplex C (3 +ℕ m))}
         {D = CW-ChainComplex (subComplex D (3 +ℕ m))}
         (cellMap-to-ChainComplexMap (restrCellMap C D f (3 +ℕ m)))
         m

Hᶠᶜʷ : (m : ℕ) (C : finCW m) (n : ℕ) → Group₀
Hᶠᶜʷ m C n = Hᶜʷ (finCW→CW m C) n


open import Cubical.HITs.PropositionalTruncation as PT
open import cw-approx
module _ (m : ℕ) {C D : finCW m}
  (f g : cellMap (finCW→CW m C) (finCW→CW m D))
  (h∞ : realiseCellMap f ≡ realiseCellMap g) where

  cellHomotopy₁ : ∥ cellHom f g ∥₁
  cellHomotopy₁ = map (λ {(F , h) → record { hom = F ; coh = h }})
                      (pathToCellularHomotopyFin m f g h∞)


module _ (m : ℕ) (n : ℕ) {C D : finCW m} 
        (f : realise (finCW→CW m C) → realise (finCW→CW m D)) where

  cellMap→Hᶠᶜʷ-hom : cellMap (finCW→CW m C) (finCW→CW m D) → GroupHom (Hᶠᶜʷ m C n) (Hᶠᶜʷ m D n)
  cellMap→Hᶠᶜʷ-hom ϕ = chainComplexMap→HomologyMap (cellMap-to-ChainComplexMap ϕ) n

  cellMap→Hᶠᶜʷ-hom-coh : (p q : Σ[ r ∈ (cellMap (finCW→CW m C) (finCW→CW m D)) ]
                                (realiseSequenceMap r ≡ f))
      → _
  cellMap→Hᶠᶜʷ-hom-coh p q with (finMap→cellHom m (fst p) (fst q) (snd p ∙ sym (snd q)))
  ... | r = PT.rec (isSetGroupHom _ _)
                   (λ r → ChainHomotopy→HomologyPath  _ _ (cellHom-to-ChainHomotopy r) n) r

  Hᶠᶜʷ→ : GroupHom (Hᶠᶜʷ m C n) (Hᶠᶜʷ m D n)
  Hᶠᶜʷ→ = rec→Set isSetGroupHom
                  (cellMap→Hᶠᶜʷ-hom ∘ fst)
                  cellMap→Hᶠᶜʷ-hom-coh
                  (finMap→cellMap₁ m C D f)


rewriteHᶠᶜʷ : (m : ℕ) (n : ℕ) {C D : finCW m} 
     → (f : realise (finCW→CW m C) → realise (finCW→CW m D))
     →  (g : cellMap (finCW→CW m C) (finCW→CW m D))
     → (realiseCellMap g ≡ f)
     → Hᶠᶜʷ→ m n f ≡ cellMap→Hᶠᶜʷ-hom m n f g
rewriteHᶠᶜʷ m n {C = C} {D = D} f g p = main
  where
  finMap→cellMap₁-path : finMap→cellMap₁ m C D f ≡ ∣ g , p ∣₁
  finMap→cellMap₁-path = squash₁ _ _

  main : Hᶠᶜʷ→ m n f ≡ cellMap→Hᶠᶜʷ-hom m n f g
  main = cong (rec→Set isSetGroupHom
              (cellMap→Hᶠᶜʷ-hom m n {C = C} {D} f ∘ fst)
              (cellMap→Hᶠᶜʷ-hom-coh m n {C = C} {D} f))
              finMap→cellMap₁-path

cellMap-to-ChainComplexMapId : (C : CW) → cellMap-to-ChainComplexMap {C} (idCellMap C) ≡ idChainMap _
cellMap-to-ChainComplexMapId C = ChainComplexMap≡ (chainFunct-id C)

cellMap-to-ChainComplexMapComp : {C D E : CW} (g : cellMap D E) (f : cellMap C D)
  → cellMap-to-ChainComplexMap (composeCellMap g f)
  ≡ compChainMap (cellMap-to-ChainComplexMap f) (cellMap-to-ChainComplexMap g)
cellMap-to-ChainComplexMapComp g f = ChainComplexMap≡ λ n → sym (chainFunct-comp g f n)

Hᶠᶜʷ→-id : (m : ℕ) (n : ℕ) {C : finCW m}
  → Hᶠᶜʷ→ m n {C = C} {D = C} (idfun _) ≡ idGroupHom
Hᶠᶜʷ→-id m n {C = C} =
    rewriteHᶠᶜʷ m n {C = C} (idfun _) (idCellMap _) realiseIdSequenceMap
  ∙ cong (λ f → chainComplexMap→HomologyMap f n)
      (cellMap-to-ChainComplexMapId _)
  ∙ chainComplexMap→HomologyMapId n

Hᶠᶜʷ→comp : (m : ℕ) (n : ℕ) {C D E : finCW m}
  (g : realise (finCW→CW m D) → realise (finCW→CW m E))
  (f : realise (finCW→CW m C) → realise (finCW→CW m D))
  → Hᶠᶜʷ→ m n {C = C} {D = E} (g ∘ f)
   ≡ compGroupHom (Hᶠᶜʷ→ m n f) (Hᶠᶜʷ→ m n g)
Hᶠᶜʷ→comp m n {C = C} {D = D} {E = E} g f =
  PT.rec2 (isSetGroupHom _ _)
          (λ {(F , fp) (G , gp)
       → (rewriteHᶠᶜʷ m n (g ∘ f) (composeCellMap G F)
                      (realiseCompSequenceMap G F
                    ∙ (λ i x → gp i (fp i x)))
        ∙ cong (λ f → chainComplexMap→HomologyMap f n)
               (cellMap-to-ChainComplexMapComp G F)
        ∙ chainComplexMap→HomologyMapComp _ _ n)
        ∙ cong₂ compGroupHom (sym (rewriteHᶠᶜʷ m n f F fp))
                             (sym (rewriteHᶠᶜʷ m n g G gp))})
          (finMap→cellMap₁ m C D f)
          (finMap→cellMap₁ m D E g)

finCW↑ : (n m : ℕ) → (m ≥ n) → finCW n → finCW m
fst (finCW↑ m n p C) = fst C
fst (snd (finCW↑ m n p C)) = snd C .fst
snd (snd (finCW↑ m n p C)) k =
  subst (λ r → isEquiv (CW↪ (fst C , snd C .fst) r))
        (sym (+-assoc k (fst p) m) ∙ cong (k +ℕ_) (snd p))
        (snd C .snd (k +ℕ fst p))

-- open import Cubical.Algebra.Group.GroupPath
-- H : fincw → ℕ → Group ℓ-zero
-- H (X , A) n =
--   rec→Gpd isGroupoidGroup
--            H-gr
--            (record { link = {!!}
--                     ; coh₁ = {!!} }) A
--   where
--   isGroupoidGroup : isGroupoid (Group ℓ-zero)
--   isGroupoidGroup = {!!}

--   H-gr : isFinCW X → Group ℓ-zero
--   H-gr (m , C) = Hᶠᶜʷ m (C .fst) n

--   C↑ : {!!}
--   C↑ = {!!}

--   module _ (nc nd : ℕ) (C : finCW nc) (D : finCW nd)
--            (eC : X ≃ realise (finCW→CW nc C))
--            (eD : X ≃ realise (finCW→CW nd D))
--     where
--     Cup Dup : finCW (nc +ℕ nd)
--     Cup = finCW↑ nc (nc +ℕ nd) (nd , +-comm nd nc) C
--     Dup = finCW↑ nd (nc +ℕ nd) (nc , refl) D

--     H→ = Hᶠᶜʷ→ (nc +ℕ nd) n {C = Cup} {D = Dup} (invEq (compEquiv (invEquiv eD) eC))

--     2-Const : {!H→!} ≡ {!!} -- 2-Constant H-gr
--     2-Const =
--       (λ _ → Hᶜʷ ((C .fst) , (C .snd .fst)) n)
--       ∙ uaGroup ((H→ .fst
--                  , {!finCW↑ nc (nc +ℕ nd) (nd , +-comm nd nc) C!})
--                  , H→ .snd)
--       ∙ λ _ → Hᶜʷ ((D .fst) , (D .snd .fst)) n

-- -- Hᶜʷ→ : (C D : CW) (f : cellMap C D) (m : ℕ)
-- --   → GroupHom (Hᶜʷ C m) (Hᶜʷ D m) 
-- -- Hᶜʷ→ C D f m =
-- --   compGroupHom (GroupIso→GroupHom (subComplexHomology C (3 +ℕ m) m (0 , refl)))
-- --     (compGroupHom (Hᶜʷ→finite C D f m)
-- --       (GroupIso→GroupHom (invGroupIso (subComplexHomology D (3 +ℕ m) m (0 , refl)))))
