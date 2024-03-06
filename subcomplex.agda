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
open import Cubical.Data.CW.Map
open import Cubical.Data.CW.Homotopy
open import Cubical.Data.CW.ChainComplex
open import Cubical.Data.CW.Approximation

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

open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Natindexed

open import Cubical.Foundations.Transport

open import Cubical.Data.CW.Map
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SequentialColimit

open import Cubical.Algebra.Group.GroupPath


module subcomplex where


private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group.GroupPath

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

  subComplexFam≃Pushout : (n m : ℕ)
    → subComplexFam n (suc m) ≃ Pushout (subComplexα n m) fst
  subComplexFam≃Pushout n m with (m ≟ᵗ n) | ((suc m) ≟ᵗ n)
  ... | lt x | lt x₁ = snd C .snd .snd .snd m
  ... | lt x | eq x₁ = snd C .snd .snd .snd m
  ... | lt x | gt x₁ = ⊥.rec (¬squeeze (x , x₁))
  ... | eq x | lt x₁ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x (<ᵗ-trans <ᵗsucm x₁)))
  ... | eq x | eq x₁ = ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (x₁ ∙ sym x) <ᵗsucm))
  ... | eq x | gt x₁ =
    compEquiv (pathToEquiv (λ i → fst C (x (~ i))))
              (isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0))
  ... | gt x | lt x₁ =
    ⊥.rec (¬squeeze (x₁ , <ᵗ-trans x (<ᵗ-trans <ᵗsucm <ᵗsucm)))
  ... | gt x | eq x₁ =
    ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₁ (<ᵗ-trans x <ᵗsucm)))
  ... | gt x | gt x₁ = isoToEquiv (PushoutEmptyFam (λ x → ¬Fin0 (fst x)) ¬Fin0)

  subComplexYieldsCWskel : (n : ℕ) → yieldsCWskel (subComplexFam n)
  fst (subComplexYieldsCWskel n) = subComplexCard n
  fst (snd (subComplexYieldsCWskel n)) = subComplexα n
  fst (snd (snd (subComplexYieldsCWskel n))) = subComplex₀-empty n
  snd (snd (snd (subComplexYieldsCWskel n))) m = subComplexFam≃Pushout n m

  subComplex : (n : ℕ) → CWskel ℓ
  fst (subComplex n) = subComplexFam n
  snd (subComplex n) = subComplexYieldsCWskel n

  subComplexFin : (m : ℕ) (n : Fin (suc m))
    → isEquiv (CW↪ (subComplexFam (fst n) , subComplexYieldsCWskel (fst n)) m)
  subComplexFin m (n , r) with (m ≟ᵗ n) | (suc m ≟ᵗ n)
  ... | lt x | p = ⊥.rec (¬squeeze (x , r))
  ... | eq x | lt x₁ =
    ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x (<ᵗ-trans <ᵗsucm x₁)))
  ... | eq x | eq x₁ = ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (x₁ ∙ sym x) <ᵗsucm))
  ... | eq x | gt x₁ =
    subst isEquiv (funExt λ x → cong (help .fst)
          (retEq (isoToEquiv (PushoutEmptyFam {A = Fin 0 × fst C m}
                  (λ x₃ → ¬Fin0 (fst x₃)) ¬Fin0 {f = snd} {g = fst})) x))
                  (help .snd)
      where
      help : fst C m ≃ fst C n
      help = invEquiv (pathToEquiv (λ i → fst C (x (~ i))))
  ... | gt x | lt x₁ =
    ⊥.rec (¬squeeze (x₁ , <ᵗ-trans x (<ᵗ-trans <ᵗsucm <ᵗsucm)))
  ... | gt x | eq x₁ =
    ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₁ r))
  ... | gt x | gt x₁ =
    subst isEquiv (funExt (retEq (isoToEquiv (PushoutEmptyFam {A = Fin 0 × fst C n}
                          (λ x₃ → ¬Fin0 (fst x₃)) ¬Fin0 {f = snd} {g = fst}))))
                  (idEquiv _ .snd)

  <ᵗ-+ : {n k : ℕ} → n <ᵗ suc (k +ℕ n)
  <ᵗ-+ {n = zero} {k} = tt
  <ᵗ-+ {n = suc n} {k} =
    subst (n <ᵗ_) (sym (+-suc k n)) (<ᵗ-+ {n = n} {k})

  subComplexYieldsFinCWskel : (n : ℕ) → yieldsFinCWskel n (subComplexFam n)
  fst (subComplexYieldsFinCWskel n) = subComplexYieldsCWskel n
  snd (subComplexYieldsFinCWskel n) k = subComplexFin (k +ℕ n) (n , <ᵗ-+)

  finSubComplex : (n : ℕ) → finCWskel ℓ n
  fst (finSubComplex n) = subComplexFam n
  snd (finSubComplex n) = subComplexYieldsFinCWskel n

  complex≃subcomplex : (n : ℕ) (m : Fin (suc n))
    → fst C (fst m) ≃ subComplex n .fst (fst m)
  complex≃subcomplex n (m , p) with (m ≟ᵗ n)
  ... | lt x = idEquiv _
  ... | eq x = idEquiv _
  ... | gt x = ⊥.rec (¬squeeze (x , p))

realiseSubComplex : (n : ℕ) (C : CWskel ℓ) → Iso (fst C n) (realise (subComplex C n))
realiseSubComplex n C =
  compIso (equivToIso (complex≃subcomplex C n flast))
          (realiseFin n (finSubComplex C n))

module _ (C : CWskel ℓ) where
  ChainSubComplex : (n : ℕ) → snd C .fst n ≡ snd (subComplex C (suc n)) .fst n
  ChainSubComplex n with (n ≟ᵗ suc n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) (sym x) <ᵗsucm))
  ... | gt x = ⊥.rec (¬-suc-n<ᵗn x)

  ≤ChainSubComplex : (n : ℕ) (m : Fin n)
    → snd C .fst (fst m) ≡ snd (subComplex C n) .fst (fst m)
  ≤ChainSubComplex n (m , p) with (m ≟ᵗ n)
  ... | lt x = refl
  ... | eq x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x p))
  ... | gt x = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))

subChainIso : (C : CWskel ℓ) (n : ℕ) (m : Fin n)
  → AbGroupIso (CWskel-fields.ℤ[A_] C (fst m)) (CWskel-fields.ℤ[A_] (subComplex C n) (fst m))
subChainIso C n (m , p) with (m ≟ᵗ n)
... | lt x = idGroupIso
... | eq x = ⊥.rec (¬m<ᵗm (subst (m <ᵗ_) (sym x) p))
... | gt x = ⊥.rec (¬m<ᵗm (<ᵗ-trans x p))

subComplexHomology : (C : CWskel ℓ) (n m : ℕ) (p : suc (suc m) <ᵗ n)
  → GroupIso (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ (subComplex C n) m)
subComplexHomology C n m p =
  homologyIso m _ _
    (subChainIso C n (suc (suc m) , p))
    (subChainIso C n (suc m , <ᵗ-trans <ᵗsucm p))
    (subChainIso C n (m , <ᵗ-trans <ᵗsucm (<ᵗ-trans <ᵗsucm p)))
    lem₁
    lem₂
  where
  lem₁ : {q : _} {r : _}
    → Iso.fun (subChainIso C n (m , q) .fst) ∘ ∂ C m .fst
    ≡ ∂ (subComplex C n) m .fst
     ∘ Iso.fun (subChainIso C n (suc m , r) .fst)
  lem₁ {q} {r} with (m ≟ᵗ n) | (suc m ≟ᵗ n) | (suc (suc m) ≟ᵗ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ r))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ r))
  ... | eq x | s | t = ⊥.rec (¬-suc-n<ᵗn (subst (suc m <ᵗ_) (sym x) r))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans r x))

  lem₂ : {q : suc m <ᵗ n} {r : (suc (suc m)) <ᵗ n}
    → Iso.fun (subChainIso C n (suc m , q) .fst)
     ∘ ∂ C (suc m) .fst
     ≡ ∂ (subComplex C n) (suc m) .fst
     ∘ Iso.fun (subChainIso C n (suc (suc m) , r) .fst)
  lem₂ {q} with (suc m ≟ᵗ n) | (suc (suc m) ≟ᵗ n) | (suc (suc (suc m)) ≟ᵗ n)
  ... | lt x | lt x₁ | lt x₂ = refl
  ... | lt x | lt x₁ | eq x₂ = refl
  ... | lt x | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (x₁ , x₂))
  ... | lt x | eq x₁ | t = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ p))
  ... | lt x | gt x₁ | t = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ p))
  ... | eq x | s | t = ⊥.rec (¬m<ᵗm (subst (suc m <ᵗ_) (sym x) q))
  ... | gt x | s | t = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans p x))


-- restrCellMap : (C : CWskel ℓ) (D : CWskel ℓ') (f : cellMap C D) (m : ℕ)
--   → cellMap (subComplex C m) (subComplex D m)
-- SequenceMap.map (restrCellMap C D f m) n k with (n ≟ᵗ m)
-- ... | lt x = SequenceMap.map f n k
-- ... | eq x = SequenceMap.map f n k
-- ... | gt x = SequenceMap.map f m k
-- SequenceMap.comm (restrCellMap C D f m) n x with (suc n ≟ᵗ m) | (n ≟ᵗ m)
-- ... | lt x₁ | lt x₂ = SequenceMap.comm f n x
-- ... | lt x₁ | eq x₂ = rec (¬m<ᵗm (subst (_<ᵗ m) x₂ (<ᵗ-trans (0 , (λ _ → suc n)) x₁)))
-- ... | lt x₁ | gt x₂ = rec (¬-suc-n<ᵗn (<ᵗ-trans (suc-≤-suc x₂) x₁))
-- ... | eq x₁ | lt x₂ = SequenceMap.comm f n x
-- ... | eq x₁ | eq x₂ = rec (¬m<ᵗm (0 , (x₁ ∙ sym x₂)))
-- ... | eq x₁ | gt x₂ = rec (¬-suc-n<ᵗn (subst (_<ᵗ n) (sym x₁) x₂))
-- ... | gt x₁ | lt x₂ = rec (¬-<ᵗ-suc x₂ x₁)
-- ... | gt x₁ | eq x₂ =
--       transportRefl _
--     ∙ substCommSlice (fst C) (fst D) (SequenceMap.map f) x₂ x
--     ∙ cong (SequenceMap.map f m) (sym (transportRefl _))
-- ... | gt x₁ | gt x₂ = refl


Hˢᵏᵉˡ→-pre : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
  (f : finCellMap (suc (suc (suc m))) C D)
  → GroupHom (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ D m)
Hˢᵏᵉˡ→-pre C D m f = finCellMap→HomologyMap m f


private
  preHˢᵏᵉˡ→ : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
    → (f : realise C → realise D)
    → ∥ finCellApprox C D f (suc (suc (suc m))) ∥₁
    → GroupHom (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ D m)
  preHˢᵏᵉˡ→ C D m f =
    rec→Set isSetGroupHom
    (λ f → Hˢᵏᵉˡ→-pre C D m (f .fst))
    main
    where
    main : 2-Constant (λ f₁ → Hˢᵏᵉˡ→-pre C D m (f₁ .fst))
    main f g = PT.rec (isSetGroupHom _ _)
      (λ q → finChainHomotopy→HomologyPath _ _
        (cellHom-to-ChainHomotopy _ q) flast)
      (pathToCellularHomotopy _ (fst f) (fst g)
        λ x → funExt⁻ (snd f ∙ sym (snd g)) (fincl flast x))

Hˢᵏᵉˡ→ : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (f : realise C → realise D)
  → GroupHom (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ D m)
Hˢᵏᵉˡ→ {C = C} {D} m f =
  preHˢᵏᵉˡ→ C D m f
    (CWmap→finCellMap C D f (suc (suc (suc m))))

opaque
  Hˢᵏᵉˡ→β : (C : CWskel ℓ) (D : CWskel ℓ') (m : ℕ)
    {f : realise C → realise D}
    (ϕ : finCellApprox C D f (suc (suc (suc m))))
    → Hˢᵏᵉˡ→ {C = C} {D} m f ≡ Hˢᵏᵉˡ→-pre C D m (ϕ .fst)
  Hˢᵏᵉˡ→β C D m {f = f} ϕ =
    cong (preHˢᵏᵉˡ→ C D m f) (squash₁ _ ∣ ϕ ∣₁)

Hˢᵏᵉˡ→id : (m : ℕ) {C : CWskel ℓ}
  → Hˢᵏᵉˡ→ {C = C} m (idfun _) ≡ idGroupHom
Hˢᵏᵉˡ→id m {C = C} =
  Hˢᵏᵉˡ→β C C m {idfun _} (idFinCellApprox (suc (suc (suc m))))
  ∙ finCellMap→HomologyMapId _

Hˢᵏᵉˡ→comp : (m : ℕ)
  {C : CWskel ℓ} {D : CWskel ℓ'} {E : CWskel ℓ''}
  (g : realise D → realise E)
  (f : realise C → realise D)
  → Hˢᵏᵉˡ→ m (g ∘ f)
  ≡ compGroupHom (Hˢᵏᵉˡ→ m f) (Hˢᵏᵉˡ→ m g)
Hˢᵏᵉˡ→comp m {C = C} {D = D} {E = E} g f =
  PT.rec2 (isSetGroupHom _ _)
    main
    (CWmap→finCellMap C D f (suc (suc (suc m))))
    (CWmap→finCellMap D E g (suc (suc (suc m))))
  where
  module _  (F : finCellApprox C D f (suc (suc (suc m))))
            (G : finCellApprox D E g (suc (suc (suc m))))
    where
    comps : finCellApprox C E (g ∘ f) (suc (suc (suc m)))
    comps = compFinCellApprox _ {g = g} {f} G F

    eq1 : Hˢᵏᵉˡ→ m (g ∘ f)
        ≡ Hˢᵏᵉˡ→-pre C E m (composeFinCellMap _ (fst G) (fst F))
    eq1 = Hˢᵏᵉˡ→β C E m {g ∘ f} comps

    eq2 : compGroupHom (Hˢᵏᵉˡ→ m f) (Hˢᵏᵉˡ→ m g)
        ≡ compGroupHom (Hˢᵏᵉˡ→-pre C D m (fst F)) (Hˢᵏᵉˡ→-pre D E m (fst G))
    eq2 = cong₂ compGroupHom (Hˢᵏᵉˡ→β C D m {f = f} F) (Hˢᵏᵉˡ→β D E m {f = g} G)

    main : Hˢᵏᵉˡ→ m (g ∘ f) ≡ compGroupHom (Hˢᵏᵉˡ→ m f) (Hˢᵏᵉˡ→ m g)
    main = eq1 ∙∙ finCellMap→HomologyMapComp _ _ _ ∙∙ sym eq2


Hˢᵏᵉˡ→Iso : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (e : realise C ≃ realise D) → GroupIso (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ D m)
Iso.fun (fst (Hˢᵏᵉˡ→Iso m e)) = fst (Hˢᵏᵉˡ→ m (fst e))
Iso.inv (fst (Hˢᵏᵉˡ→Iso m e)) = fst (Hˢᵏᵉˡ→ m (invEq e))
Iso.rightInv (fst (Hˢᵏᵉˡ→Iso m e)) =
  funExt⁻ (cong fst (sym (Hˢᵏᵉˡ→comp m (fst e) (invEq e))
       ∙∙ cong (Hˢᵏᵉˡ→ m) (funExt (secEq e))
       ∙∙ Hˢᵏᵉˡ→id m))
Iso.leftInv (fst (Hˢᵏᵉˡ→Iso m e)) =
  funExt⁻ (cong fst (sym (Hˢᵏᵉˡ→comp m (invEq e) (fst e))
       ∙∙ cong (Hˢᵏᵉˡ→ m) (funExt (retEq e))
       ∙∙ Hˢᵏᵉˡ→id m))
snd (Hˢᵏᵉˡ→Iso m e) = snd (Hˢᵏᵉˡ→ m (fst e))

Hˢᵏᵉˡ→Equiv : {C : CWskel ℓ} {D : CWskel ℓ'} (m : ℕ)
  (e : realise C ≃ realise D) → GroupEquiv (Hˢᵏᵉˡ C m) (Hˢᵏᵉˡ D m)
Hˢᵏᵉˡ→Equiv m e = GroupIso→GroupEquiv (Hˢᵏᵉˡ→Iso m e)

Hᶜʷ : ∀ (C : CW ℓ) (n : ℕ) → Group₀
Hᶜʷ (C , CWstr) n =
  PropTrunc→Group
      (λ Cskel → Hˢᵏᵉˡ (Cskel .fst) n)
      (λ Cskel Dskel → Hˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Cskel)) (snd Dskel)))
      coh
      CWstr
  where
  coh : (Cskel Dskel Eskel : isCW C) (t : fst (Hˢᵏᵉˡ (Cskel .fst) n))
    → fst (fst (Hˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Dskel)) (snd Eskel))))
         (fst (fst (Hˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Cskel)) (snd Dskel)))) t)
    ≡ fst (fst (Hˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd Cskel)) (snd Eskel)))) t
  coh (C' , e) (D , f) (E , h) =
    funExt⁻ (cong fst
          (sym (Hˢᵏᵉˡ→comp n (fst (compEquiv (invEquiv f) h))
                           (fst (compEquiv (invEquiv e) f)))
          ∙ cong (Hˢᵏᵉˡ→ n) (funExt λ x → cong (fst h) (retEq f _))))



private
  module _ {C : Type ℓ} {D : Type ℓ'} (f : C → D) (n : ℕ) where
    right : (cwC : isCW C) (cwD1 : isCW D) (cwD2 : isCW D)
      → PathP (λ i → GroupHom (Hᶜʷ (C , ∣ cwC ∣₁) n)
                         (Hᶜʷ (D , squash₁ ∣ cwD1 ∣₁ ∣ cwD2 ∣₁ i) n))
        (Hˢᵏᵉˡ→ n (λ x → fst (snd cwD1) (f (invEq (snd cwC) x))))
        (Hˢᵏᵉˡ→ n (λ x → fst (snd cwD2) (f (invEq (snd cwC) x))))
    right cwC cwD1 cwD2 =
      PathPGroupHomₗ _
        (cong (Hˢᵏᵉˡ→ n) (funExt (λ s
          → cong (fst (snd cwD2)) (sym (retEq (snd cwD1) _))))
        ∙ Hˢᵏᵉˡ→comp n _ _)

    left : (cwC1 : isCW C) (cwC2 : isCW C) (cwD : isCW D)
      → PathP (λ i → GroupHom (Hᶜʷ (C , squash₁ ∣ cwC1 ∣₁ ∣ cwC2 ∣₁ i) n)
                                  (Hᶜʷ (D , ∣ cwD ∣₁) n))
                 (Hˢᵏᵉˡ→ n (λ x → fst (snd cwD) (f (invEq (snd cwC1) x))))
                 (Hˢᵏᵉˡ→ n (λ x → fst (snd cwD) (f (invEq (snd cwC2) x))))
    left cwC1 cwC2 cwD =
      PathPGroupHomᵣ (Hˢᵏᵉˡ→Equiv n (compEquiv (invEquiv (snd cwC1)) (snd cwC2)))
            (sym (Hˢᵏᵉˡ→comp n (λ x → fst (snd cwD) (f (invEq (snd cwC2) x)))
                             (compEquiv (invEquiv (snd cwC1)) (snd cwC2) .fst))
           ∙ cong (Hˢᵏᵉˡ→ n) (funExt (λ x
              → cong (fst (snd cwD) ∘ f)
                  (retEq (snd cwC2) _))))

    left-right : (x y : isCW C) (v w : isCW D) →
      SquareP
      (λ i j →
         GroupHom (Hᶜʷ (C , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) n)
         (Hᶜʷ (D , squash₁ ∣ v ∣₁ ∣ w ∣₁ j) n))
      (right x v w) (right y v w) (left x y v) (left x y w)
    left-right _ _ _ _ = isSet→SquareP
       (λ _ _ → isSetGroupHom) _ _ _ _

    Hᶜʷ→pre : (cwC : ∥ isCW C ∥₁) (cwD : ∥ isCW D ∥₁)
      → GroupHom (Hᶜʷ (C , cwC) n) (Hᶜʷ (D , cwD) n)
    Hᶜʷ→pre =
      elim2→Set (λ _ _ → isSetGroupHom)
        (λ cwC cwD → Hˢᵏᵉˡ→ n (fst (snd cwD) ∘ f ∘ invEq (snd cwC)))
        left right
        (λ _ _ _ _ → isSet→SquareP
         (λ _ _ → isSetGroupHom) _ _ _ _)

Hᶜʷ→ : {C : CW ℓ} {D : CW ℓ'} (n : ℕ) (f : C →ᶜʷ D)
    → GroupHom (Hᶜʷ C n) (Hᶜʷ D n)
Hᶜʷ→ {C = C , cwC} {D = D , cwD} n f = Hᶜʷ→pre f n cwC cwD

Hᶜʷ→id : {C : CW ℓ} (n : ℕ)
    → Hᶜʷ→ {C = C} {C} n (idfun (fst C))
     ≡ idGroupHom
Hᶜʷ→id {C = C , cwC} n =
  PT.elim {P = λ cwC
    → Hᶜʷ→ {C = C , cwC} {C , cwC} n (idfun C) ≡ idGroupHom}
    (λ _ → isSetGroupHom _ _)
    (λ cwC* → cong (Hˢᵏᵉˡ→ n) (funExt (secEq (snd cwC*)))
              ∙ Hˢᵏᵉˡ→id n) cwC

Hᶜʷ→comp : {C : CW ℓ} {D : CW ℓ'} {E : CW ℓ''} (n : ℕ)
      (g : D →ᶜʷ E) (f : C →ᶜʷ D)
    → Hᶜʷ→ {C = C} {E} n (g ∘ f)
     ≡ compGroupHom (Hᶜʷ→ {C = C} {D} n f) (Hᶜʷ→ {C = D} {E} n g)
Hᶜʷ→comp {C = C , cwC} {D = D , cwD} {E = E , cwE} n g f =
  PT.elim3 {P = λ cwC cwD cwE
    → Hᶜʷ→ {C = C , cwC} {E , cwE} n (g ∘ f)
     ≡ compGroupHom (Hᶜʷ→ {C = C , cwC} {D , cwD} n f)
                    (Hᶜʷ→ {C = D , cwD} {E , cwE} n g)}
     (λ _ _ _ → isSetGroupHom _ _)
     (λ cwC cwD cwE
       → cong (Hˢᵏᵉˡ→ n) (funExt (λ x → cong (fst (snd cwE) ∘ g)
                          (sym (retEq (snd cwD) _))))
       ∙ Hˢᵏᵉˡ→comp n _ _)
     cwC cwD cwE

Hᶜʷ→Iso : {C : CW ℓ} {D : CW ℓ'} (m : ℕ)
  (e : fst C ≃ fst D) → GroupIso (Hᶜʷ C m) (Hᶜʷ D m)
Iso.fun (fst (Hᶜʷ→Iso m e)) = fst (Hᶜʷ→ m (fst e))
Iso.inv (fst (Hᶜʷ→Iso m e)) = fst (Hᶜʷ→ m (invEq e))
Iso.rightInv (fst (Hᶜʷ→Iso m e)) =
  funExt⁻ (cong fst (sym (Hᶜʷ→comp m (fst e) (invEq e))
       ∙∙ cong (Hᶜʷ→ m) (funExt (secEq e))
       ∙∙ Hᶜʷ→id m))
Iso.leftInv (fst (Hᶜʷ→Iso m e)) =
  funExt⁻ (cong fst (sym (Hᶜʷ→comp m (invEq e) (fst e))
       ∙∙ cong (Hᶜʷ→ m) (funExt (retEq e))
       ∙∙ Hᶜʷ→id m))
snd (Hᶜʷ→Iso m e) = snd (Hᶜʷ→ m (fst e))

Hᶜʷ→Equiv : {C : CW ℓ} {D : CW ℓ'} (m : ℕ)
  (e : fst C ≃ fst D) → GroupEquiv (Hᶜʷ C m) (Hᶜʷ D m)
Hᶜʷ→Equiv m e = GroupIso→GroupEquiv (Hᶜʷ→Iso m e)
