{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.Map where

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
open import Hurewicz.SubcomplexNew
open import Hurewicz.random

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
open import Cubical.Algebra.Group.Abelianization.Properties as Abi --rec


diff<ᵗ : {n m : ℕ} → n <ᵗ m → Σ[ k ∈ ℕ ] k +ℕ n ≡ m
diff<ᵗ {n = n} p = suc (<ᵗ→< p .fst) , sym (+-suc _ n) ∙ <ᵗ→< p .snd

diff<ᵗ' : {n m : ℕ} → n <ᵗ suc m → Σ[ k ∈ ℕ ] k +ℕ n ≡ m
diff<ᵗ' {n = n} p = <ᵗ→< p .fst , cong predℕ (sym (+-suc (fst (<ᵗ→< p)) n) ∙ <ᵗ→< p .snd)

CW↑ : ∀ {ℓ} (C : CWskel ℓ) (n m : ℕ) → n <ᵗ m → fst C n → fst C m
CW↑ C n m x = subst (fst C) (snd (diff<ᵗ x))
             ∘ CW↪Iterate C n (diff<ᵗ x .fst)

CW↑< : ∀ {ℓ} (C : CWskel ℓ) (n m : ℕ) → n <ᵗ suc m → fst C n → fst C m
CW↑< C n m x = subst (fst C) (snd (diff<ᵗ' x))
             ∘ CW↪Iterate C n (diff<ᵗ' x .fst)

{-
cellMap→finCellMap : ∀ {ℓ ℓ'} (m : ℕ) {C : CWskel ℓ} {D : CWskel ℓ'} (ϕ : cellMap C D) → finCellMap m C D
FinSequenceMap.fmap (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.map ϕ x
FinSequenceMap.fcomm (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.comm ϕ x


FinSequenceMapId : ∀ {ℓ ℓ'} {n : ℕ} {S1 : FinSequence n ℓ} {S2 : FinSequence n ℓ'}
  → {f g : FinSequenceMap S1 S2}
  → (p : (x : Fin (suc n)) (a : _) → FinSequenceMap.fmap f x a ≡ FinSequenceMap.fmap g x a)
  → ((x : Fin n) (a : FinSequence.fobj S1 (injectSuc x))
        → Square (FinSequenceMap.fcomm f x a) (FinSequenceMap.fcomm g x a)
                  (cong (FinSequence.fmap S2)
                  (p (injectSuc x) a))
                  (p (fsuc x) (FinSequence.fmap S1 a)))
  → f ≡ g
FinSequenceMap.fmap (FinSequenceMapId p q i) a b = p a b i
FinSequenceMap.fcomm (FinSequenceMapId p q i) a b = q a b i

finCellMapSubComplexMap : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  → (m : Fin (suc n)) → fst C (fst m) → subComplexFam C n (fst m)
finCellMapSubComplexMap C n m with (fst m ≟ᵗ n)
... | lt x = λ x → x
... | eq x = λ x → x
... | gt x = ⊥.rec (¬squeeze (snd m , x))

finCellMapSubComplexComm : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (m : Fin n)
      (x : FinSequence.fobj (realiseFinSeq n C) (injectSuc m)) →
      FinSequence.fmap (realiseFinSeq n (subComplex C n)) {n = m}
        (finCellMapSubComplexMap C n (injectSuc m) x)
      ≡
      finCellMapSubComplexMap C n (fsuc m)
      (FinSequence.fmap (realiseFinSeq n C) x)
finCellMapSubComplexComm C n m with (fst m ≟ᵗ n) | (suc (fst m) ≟ᵗ n)
... | lt x | lt x₁ = λ _ → refl
... | lt x | eq x₁ = λ _ → refl
... | lt x | gt x₁ = ⊥.rec (¬squeeze (x , x₁))
... | eq x | lt x₁ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x (<ᵗ-trans <ᵗsucm x₁)))
... | eq x | eq x₁ = ⊥.rec
       (¬m<ᵗm (subst (_<ᵗ_ (fst m)) (x₁ ∙ (λ i → x (~ i))) <ᵗsucm))
... | eq x | gt x₁ = ⊥.rec (¬squeeze (snd (fsuc m) , x₁))
... | gt x | q = ⊥.rec (¬squeeze (snd (injectSuc m) , x))

finCellMapSubComplex : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → finCellMap n C (subComplex C n)
FinSequenceMap.fmap (finCellMapSubComplex C n) = finCellMapSubComplexMap C n
FinSequenceMap.fcomm (finCellMapSubComplex C n) = finCellMapSubComplexComm C n

finCellMapSubComplexMapComp : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  → (m : Fin (suc n)) (x : fst C (fst m))
    → SequenceMap.map (subComplex→Full C n) (fst m) (finCellMapSubComplexMap C n m x) ≡ x
finCellMapSubComplexMapComp C n m x with (fst m ≟ᵗ n)
... | lt x₁ = refl
... | eq x₁ = refl
... | gt x₁ = ⊥.rec (¬squeeze (snd m , x₁))

finCellMapSubComplexMapComm : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  (x : Fin n) (a : fst C (fst x)) →
      Square
      ((SequenceMap.comm (subComplex→Full C n) (fst x))
       (finCellMapSubComplexMap C n (injectSuc x) a)
       ∙
       (λ i →
          (SequenceMap.map (subComplex→Full C n) (suc (fst x)))
          (finCellMapSubComplexComm C n x a i)))
      refl
      (cong (λ x₁ → CW↪ C (fst x) x₁)
       (finCellMapSubComplexMapComp C n (injectSuc x) a))
      (finCellMapSubComplexMapComp C n (fsuc x) (CW↪ C (fst x) a))
finCellMapSubComplexMapComm C n x a with (fst x ≟ᵗ n) | (suc (fst x) ≟ᵗ n)
finCellMapSubComplexMapComm C (suc n) x a | lt x₁ | lt x₂ = sym (rUnit _)
finCellMapSubComplexMapComm C (suc n) x a | lt x₁ | eq x₂ = sym (rUnit _)
... | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (snd (fsuc x) , x₂))
... | eq x₁ | lt x₂ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ (<ᵗ-trans <ᵗsucm x₂))) 
... | eq x₁ | eq x₂ = ⊥.rec
          (¬m<ᵗm (subst (_<ᵗ_ (fst x)) (x₂ ∙ (λ i₁ → x₁ (~ i₁))) <ᵗsucm))
... | eq x₁ | gt x₂ = ⊥.rec (¬squeeze (snd (fsuc x) , x₂))
... | gt x₁ | q = ⊥.rec (¬squeeze (snd (injectSuc x) , x₁))

finCellMapSubComplexComp : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  → composeFinCellMap n (cellMap→finCellMap n (subComplex→Full C n)) (finCellMapSubComplex C n)
   ≡ idFinCellMap n _
finCellMapSubComplexComp C n =
  FinSequenceMapId (finCellMapSubComplexMapComp C n)
                   (finCellMapSubComplexMapComm C n)

finCellMapSubComplexComp' : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  → composeFinCellMap n (finCellMapSubComplex C n) (cellMap→finCellMap n (subComplex→Full C n))
   ≡ idFinCellMap n _
finCellMapSubComplexComp' C n =
  FinSequenceMapId (finCellMapSubComplexMapComp' C n)
                   (finCellMapSubComplexMapCoh' C n)
  where
  finCellMapSubComplexMapComp' : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
    → (m : Fin (suc n)) (x : _)
      → finCellMapSubComplexMap C n m (SequenceMap.map (subComplex→Full C n) (fst m) x) ≡ x
  finCellMapSubComplexMapComp' C n m x with (fst m ≟ᵗ n)
  ... | lt x₁ = refl
  ... | eq x₁ = refl
  ... | gt x₁ = ⊥.rec (¬squeeze (snd m , x₁))

  finCellMapSubComplexMapCoh' : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (x : Fin n) (a : subComplexFam C n (fst x)) →
      Square
      (finCellMapSubComplexComm C n x
       ((SequenceMap.map (subComplex→Full C n) (fst x)) a)
       ∙
       (λ i →
          finCellMapSubComplexMap C n (fsuc x)
          ((SequenceMap.comm (subComplex→Full C n) (fst x))
           a i)))
      refl
      (cong (λ x₁ → CW↪ (subComplex C n) (fst x) x₁)
       (finCellMapSubComplexMapComp' C n (injectSuc x) a))
      (finCellMapSubComplexMapComp' C n (fsuc x)
       (CW↪ (subComplex C n) (fst x) a))
  finCellMapSubComplexMapCoh' C n x a with (fst x ≟ᵗ n) | (suc (fst x) ≟ᵗ n)
  finCellMapSubComplexMapCoh' C (suc n) x a | lt x₁ | lt x₂ = sym (rUnit _)
  finCellMapSubComplexMapCoh' C (suc n) x a | lt x₁ | eq x₂ = sym (rUnit _)
  ... | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (snd (fsuc x) , x₂))
  ... | eq x₁ | lt x₂ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ (<ᵗ-trans <ᵗsucm x₂))) 
  ... | eq x₁ | eq x₂ = ⊥.rec
            (¬m<ᵗm (subst (_<ᵗ_ (fst x)) (x₂ ∙ (λ i₁ → x₁ (~ i₁))) <ᵗsucm))
  ... | eq x₁ | gt x₂ = ⊥.rec (¬squeeze (snd (fsuc x) , x₂))
  ... | gt x₁ | q = ⊥.rec (¬squeeze (snd (injectSuc x) , x₁))

subComplex→GrIso : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  → GroupIso (Hˢᵏᵉˡ (subComplex C (suc (suc (suc n)))) n) (Hˢᵏᵉˡ C n)
Iso.fun (fst (subComplex→GrIso C n)) =
  finCellMap→HomologyMap n
    (cellMap→finCellMap (suc (suc (suc n)))
      (subComplex→Full C (suc (suc (suc n))))) .fst
Iso.inv (fst (subComplex→GrIso C n)) = finCellMap→HomologyMap n (finCellMapSubComplex C (suc (suc (suc n)))) .fst
Iso.rightInv (fst (subComplex→GrIso C n)) =
  funExt⁻ (cong fst (sym (finCellMap→HomologyMapComp n
             (cellMap→finCellMap (suc (suc (suc n)))
               (subComplex→Full C (suc (suc (suc n)))))
             (finCellMapSubComplex C (suc (suc (suc n)))))
           ∙ cong (finCellMap→HomologyMap n) (finCellMapSubComplexComp C (suc (suc (suc n))))
           ∙ finCellMap→HomologyMapId n))
Iso.leftInv (fst (subComplex→GrIso C n)) =
  funExt⁻ (cong fst (sym (finCellMap→HomologyMapComp n
             (finCellMapSubComplex C (suc (suc (suc n))))
             (cellMap→finCellMap (suc (suc (suc n)))
               (subComplex→Full C (suc (suc (suc n))))))
           ∙ cong (finCellMap→HomologyMap n) (finCellMapSubComplexComp' C (suc (suc (suc n))))
           ∙ finCellMap→HomologyMapId n))
snd (subComplex→GrIso C n) =
  finCellMap→HomologyMap n
    (cellMap→finCellMap (suc (suc (suc n)))
      (subComplex→Full C (suc (suc (suc n))))) .snd
-- (cong fst (sym (finCellMap→HomologyMapComp n g⁻ g)) ∙ {!!})) {!!}) -- 
  where
  g⁻ : finCellMap (suc (suc (suc n))) (subComplex C (suc (suc (suc n)))) C
  g⁻ = (cellMap→finCellMap (suc (suc (suc n))) (subComplex→Full C (suc (suc (suc n)))))

  g : finCellMap (suc (suc (suc n))) C (subComplex C (suc (suc (suc n))))
  FinSequenceMap.fmap g (o , s) with (o ≟ᵗ (suc (suc (suc n))))
  ... | lt x = idfun _
  ... | eq x = idfun _
  ... | gt x = ⊥.rec (¬squeeze (s , x))
  FinSequenceMap.fcomm g (o , s) c with (o ≟ᵗ suc (suc n)) | (o ≟ᵗ suc (suc (suc n)))
  ... | lt x | lt x₁ = refl
  ... | lt x | eq x₁ = ⊥.rec (¬m<ᵗm (subst (o <ᵗ_) (sym x₁) s))
  ... | lt x | gt x₁ = ⊥.rec (¬m<ᵗm (<ᵗ-trans s x₁))
  ... | eq x | lt x₁ = refl
  ... | eq x | eq x₁ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) x (subst (o <ᵗ_) (sym x₁ ∙ x) s)))
  ... | eq x | gt x₁ = ⊥.rec (¬m<ᵗm (<ᵗ-trans s x₁))
  ... | gt x | b = ⊥.rec (¬squeeze (s , x))

realiseSubComplexFunPre : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → fst C n → subComplexFam C n n
realiseSubComplexFunPre C n x with (n ≟ᵗ n)
... | lt x₁ = x
... | eq x₁ = x
... | gt x₁ = x

realiseSubComplexFunPreInv : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → subComplexFam C n n → fst C n
realiseSubComplexFunPreInv C n x with (n ≟ᵗ n)
... | lt x₁ = x
... | eq x₁ = x
... | gt x₁ = x

isEqrealiseSubComplexPre : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → isEquiv (realiseSubComplexFunPre C n)
isEqrealiseSubComplexPre C n  with (n ≟ᵗ n)
... | lt x = idIsEquiv _
... | eq x = idIsEquiv _
... | gt x = idIsEquiv _

realiseSubComplexFun : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → fst C n → realise (subComplex C n)
realiseSubComplexFun C n t = incl {n = n} (realiseSubComplexFunPre C n t)

realiseSubComplexFun←' : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → realise (subComplex C n) → fst C n
realiseSubComplexFun←' C n = Iso.inv (realiseSubComplex n C)


finCellApproxRealiseCellMap : ∀ {ℓ ℓ'} {C : CWskel ℓ} {D : CWskel ℓ'}
  (f : cellMap C D) (n : ℕ) → finCellApprox C D (realiseCellMap f) n
fst (finCellApproxRealiseCellMap f n) = cellMap→finCellMap n f
snd (finCellApproxRealiseCellMap f n) = →FinSeqColimHomotopy _ _ λ _ → refl

funCharac? : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  → (CW↪∞ C n ∘ invEq (isoToEquiv (realiseSubComplex n C)))
   ≡ realiseCellMap (subComplex→Full C n)
funCharac? C n = funExt λ x
  → better (Iso.inv (realiseSubComplex n C) x)
   ∙ cong (realiseCellMap (subComplex→Full C n))
       (Iso.rightInv (realiseSubComplex n C) x)
  where
  lem : (n : ℕ) (x : _)
    → x ≡ SequenceMap.map (subComplex→Full C n) n
            (complex≃subcomplex' C n n <ᵗsucm (n ≟ᵗ n) .fst x)
  lem n x  with (n ≟ᵗ n)
  ... | lt x₁ = refl
  ... | eq x₁ = refl
  ... | gt x₁ = ⊥.rec (¬squeeze (x₁ , <ᵗsucm))

  better : (x : _) → CW↪∞ C n x
    ≡ realiseCellMap (subComplex→Full C n)
        (Iso.fun (realiseSubComplex n C) x)
  better x = cong (incl {n = n}) (lem n x)

∃HomologyEquivalentSubStructure :
     ∀ {ℓ} (C : CWexplicit ℓ) (n : ℕ)
  → Σ[ C' ∈ CW ℓ ] Σ[ ι ∈ (fst C' → fst C) ] isEquiv (Hᶜʷ→ {C = C'} {D = fst C , ∣ snd C ∣₁} n ι .fst)
fst (fst (∃HomologyEquivalentSubStructure (C∞ , C , e) n)) = fst C (suc (suc (suc n)))
snd (fst (∃HomologyEquivalentSubStructure (C∞ , C , e) n)) =
  ∣ (subComplex C (suc (suc (suc n)))) , isoToEquiv (realiseSubComplex ((suc (suc (suc n)))) C) ∣₁
fst (snd (∃HomologyEquivalentSubStructure (C∞ , C , e) n)) = invEq e ∘ CW↪∞ C (suc (suc (suc n)))
snd (snd (∃HomologyEquivalentSubStructure (C∞ , C , e) n)) =
  subst isEquiv (cong fst (sym (Hᶜʷ→comp
    {C = fst C (suc (suc (suc n))) , ∣ (subComplex C (suc (suc (suc n))))
                             , isoToEquiv (realiseSubComplex ((suc (suc (suc n)))) C) ∣₁}
    {D = realise C , ∣ C , (idEquiv (realise C)) ∣₁}
    {E = C∞ , ∣ C , e ∣₁} n (invEq e) (CW↪∞ C (suc (suc (suc n)))))))
     (compEquiv (_ , main)
       (Hᶜʷ→Equiv {C = (realise C) , ∣ C , (idEquiv (realise C)) ∣₁}
                   {D = C∞ , ∣ C , e ∣₁} n (invEquiv e) .fst) .snd)
  where
  T : (n : ℕ) → finCellApprox (subComplex C n) C (CW↪∞ C n ∘ Iso.inv (realiseSubComplex n C)) n
  fst (T n) = finCellApproxRealiseCellMap (subComplex→Full C n) n .fst
  snd (T n) = finCellApproxRealiseCellMap (subComplex→Full C n) n .snd
            ∙ funExt λ x → funExt⁻ (sym (funCharac? C n)) (FinSeqColim→Colim n x)

  ww = SeqColim
  main : isEquiv (fst (Hᶜʷ→ {C = fst C (suc (suc (suc n))) , _} n (CW↪∞ C (suc (suc (suc n))))))
  main = subst isEquiv (cong fst (sym (Hˢᵏᵉˡ→β _ _ n (T (suc (suc (suc n)))))))
               (isoToIsEquiv (fst (subComplex→GrIso C n)))

-}

-- todo : fix univ levels
groupHom→AbelianisationGroupHom : ∀ {ℓ} {A : Group ℓ} {B : Group ℓ}
  → (ϕ : GroupHom A B)
  → ((x y : fst B) → GroupStr._·_ (snd B) x y ≡ GroupStr._·_ (snd B) y x)
  → GroupHom (AbGroup→Group (AbelianizationAbGroup A))
              B
fst (groupHom→AbelianisationGroupHom {B = B} ϕ commB) =
  Abi.rec _ (GroupStr.is-set (snd B)) (ϕ .fst)
            λ a b c → IsGroupHom.pres· (ϕ .snd) _ _
            ∙ cong₂ (GroupStr._·_ (snd B)) refl
                    (IsGroupHom.pres· (ϕ .snd) _ _
                   ∙ commB _ _
                   ∙ sym (IsGroupHom.pres· (ϕ .snd) _ _))
            ∙ sym (IsGroupHom.pres· (ϕ .snd) _ _)
snd (groupHom→AbelianisationGroupHom {B = B} ϕ commB) =
  makeIsGroupHom (Abi.elimProp2 _
    (λ _ _ → GroupStr.is-set (snd B) _ _)
    λ a b → IsGroupHom.pres· (ϕ .snd) _ _)

isInducedAbelianisationGroupEquiv : ∀ {ℓ} (A : Group ℓ) (B : Group ℓ)
  → ((x y : fst B) → GroupStr._·_ (snd B) x y ≡ GroupStr._·_ (snd B) y x)
  → (f : fst A → fst B)
  → Type ℓ
isInducedAbelianisationGroupEquiv A B iscomm f =
  Σ[ ishom ∈ IsGroupHom (snd A) f (snd B) ]
    isEquiv (fst (groupHom→AbelianisationGroupHom (f , ishom) iscomm))

isPropIsInducedAbelianisationGroupEquiv : ∀ {ℓ} {A : Group ℓ} {B : Group ℓ}
  → {isc : (x y : fst B) → GroupStr._·_ (snd B) x y ≡ GroupStr._·_ (snd B) y x}
  → {f : fst A → fst B} → isProp (isInducedAbelianisationGroupEquiv A B isc f)
isPropIsInducedAbelianisationGroupEquiv =
  isPropΣ (isPropIsGroupHom _ _) λ _ → isPropIsEquiv _

open import Hurewicz.SnNew
-- todo: update universe level after fixing it in abelianisaion file
module _ where
  preHurewiczMap : {n : ℕ} (X : CW ℓ-zero) (x : fst X) (f : S₊∙ (suc n) →∙ (fst X , x))
    → GroupHom (Hᶜʷ (Sᶜʷ (suc n)) n) (Hᶜʷ X n)
  preHurewiczMap {n = n} X x f = Hᶜʷ→ {C = Sᶜʷ (suc n)} {D = X} n (fst f)

  HurewiczMapUntrunc :  {n : ℕ} (X : CW ℓ-zero) (x : fst X)
    (f : S₊∙ (suc n) →∙ (fst X , x)) → Hᶜʷ X n .fst
  HurewiczMapUntrunc {n = n} X x f = preHurewiczMap X x f .fst (genHₙSⁿ n)

  HurewiczMap : {n : ℕ} (X : CW ℓ-zero) (x : fst X)
    → π' (suc n) (fst X , x)
    → fst (Hᶜʷ X n)
  HurewiczMap X x = ST.rec (GroupStr.is-set (snd (Hᶜʷ X _))) (HurewiczMapUntrunc X x)

  open import Cubical.Homotopy.Connected
  open import Cubical.HITs.Truncation as TR
  open import Cubical.CW.Properties
  
  
  HurewiczMapHom :  {n : ℕ} (X : CW ℓ-zero) (x : fst X) (f g : π' (suc n) (fst X , x))
    → isConnected 2 (fst X)
     → HurewiczMap X x (·π' n f g)
      ≡ GroupStr._·_ (snd (Hᶜʷ X n))
          (HurewiczMap X x f) (HurewiczMap X x g)
  HurewiczMapHom {n = n} = uncurry λ X → PT.elim
    (λ x → isPropΠ4 λ _ _ _ _ → GroupStr.is-set (snd (Hᶜʷ (X , x) n)) _ _)
    (uncurry λ Xsk → EquivJ (λ X y → (x : X) (f g : π' (suc n) (X , x)) →
      isConnected 2 X →
      HurewiczMap (X , ∣ Xsk , y ∣₁) x (·π' n f g) ≡
      (snd (Hᶜʷ (X , ∣ Xsk , y ∣₁) n) GroupStr.·
       HurewiczMap (X , ∣ Xsk , y ∣₁) x f)
      (HurewiczMap (X , ∣ Xsk , y ∣₁) x g))
      (λ x → TR.rec (isPropΠ3 (λ _ _ _ → squash/ _ _))
        (uncurry λ x₀ → resch Xsk x x₀ x)
        (isConnected-CW↪∞ 1 Xsk x .fst)))
    where
    module _ (Xsk : CWskel ℓ-zero) (x : realise Xsk) where
      ∥x₀∥ : hLevelTrunc 1 (Xsk .fst 1)
      ∥x₀∥ = TR.map fst (isConnected-CW↪∞ 1 Xsk x .fst)

      X' : CW ℓ-zero
      X' = realise Xsk , ∣ Xsk , idEquiv (realise Xsk) ∣₁


      resch : (x₁ : fst Xsk 1) (x : realise Xsk) (y : CW↪∞ Xsk 1 x₁ ≡ x)
        (f g : π' (suc n) (realise Xsk , x))
        → isConnected 2 (realise Xsk)
        → HurewiczMap X' x (·π' n f g)
        ≡ GroupStr._·_ (snd (Hᶜʷ X' n))
           (HurewiczMap X' x f) (HurewiczMap X' x g)
      resch x₀ = J> ST.elim2 (λ _ _ → isSetΠ λ _ → isProp→isSet (squash/ _ _))
        λ f g t → PT.rec2 (squash/ _ _)
          (λ {(f' , fp) (g' , gp) → lem f' g' f fp g gp})
          (approxSphereMap∙ Xsk x₀ n f)
          (approxSphereMap∙ Xsk x₀ n g)
       where
       X∙ : Pointed₀
       X∙ = fst Xsk (suc (suc n)) , CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)

       X* : (n : ℕ) → Pointed₀
       X* n = fst Xsk (suc (suc n)) , CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)

       GoalTy : (f g : S₊∙ (suc n) →∙ (realise Xsk , CW↪∞ Xsk 1 x₀)) → Type _
       GoalTy f g =
         HurewiczMap X' (CW↪∞ Xsk 1 x₀) (·π' n ∣ f ∣₂ ∣ g ∣₂)
             ≡ GroupStr._·_ (snd (Hᶜʷ X' n))
               (HurewiczMap X' (CW↪∞ Xsk 1 x₀) ∣ f ∣₂)
               (HurewiczMap X' (CW↪∞ Xsk 1 x₀) ∣ g ∣₂)
       module _ (f' g' : S₊∙ (suc n) →∙ X∙) where
         multCellMap : finCellApprox (Sˢᵏᵉˡ (suc n)) Xsk (fst (∙Π (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g')) ∘
           invEq (isCWSphere (suc n) .snd))
                        (suc (suc (suc n)))
         multCellMap =  betterFinCellApproxS Xsk (suc n) x₀ (∙Π f' g') (∙Π (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g'))
                            (λ x → funExt⁻ (cong fst (∙Π∘∙ n f' g' (incl∙ Xsk x₀))) x ∙ refl) (suc (suc (suc n)))

         open import Cubical.HITs.SphereBouquet.Degree

         G : (n : ℕ) → _
         G n = BouquetFuns.CTB (suc n) (CWskel-fields.card Xsk (suc n))
                                 (CWskel-fields.α Xsk (suc n))
                                 (CWskel-fields.e Xsk (suc n))


         fEq : (n : ℕ) (f' : S₊∙ (suc n) →∙ X* n) (q : _) (x : _) (a : _)
           → f' .fst ((invEq (SαEqGen (suc n) (suc n) (eq x) q) ∘ inl) a) ≡ CWskel∙ Xsk x₀ (suc n)
         fEq n f' (lt x₁) x a = snd f'
         fEq n f' (eq x₁) x a = ⊥.rec (¬m<ᵗm (subst (_<ᵗ_ (suc n)) ((sym x₁) ∙ cong predℕ x) <ᵗsucm)) -- 
         fEq n f' (gt x₁) x a = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ_ (suc (suc n))) (λ i → predℕ ( (x i))) x₁)) -- 

         alt : (n : ℕ) (f : S₊∙ (suc n) →∙ X* n) (p : _) (q : _)
           → cofib (invEq (SαEqGen (suc n) (suc n) p q) ∘ inl) → cofibCW (suc n) Xsk
         alt n f p q (inl x) = inl x
         alt n f (lt x₁) q (inr x) = inl tt
         alt n f (eq x₁) p (inr x) = inr (f .fst x)
         alt n f (gt x₁) q (inr x) = inl tt
         alt n f (lt x) q (push a i) = inl tt
         alt n f (eq x) q (push a i) = (push (CWskel∙ Xsk x₀ n) ∙ λ i → inr (fEq n f q x a (~ i))) i
         alt n f (gt x) q (push a i) = inl tt

-- G n (alt n f' p q
         F : (n : ℕ) (f : S₊∙ (suc n) →∙ X* n) (p : _) (q : _) (x : _) → _
         F n f' p q x =  G n (alt n f' p q (BouquetFuns.BTC (suc n)
                                  (ScardGen (suc n) (suc n) p)
                                  (SαGen (suc n) (suc n) p q)
                                  (SαEqGen (suc n) (suc n) p q)
                                  x))

         module _ (f' : S₊∙ (suc n) →∙ X∙) (Q : _) where
           private
             fbet = (betterFinCellApproxS Xsk (suc n) x₀ f'
                 (incl∙ Xsk x₀ ∘∙ f') Q (suc (suc (suc n))))

           alt≡inr : (x : _)
             → prefunctoriality.fn+1/fn (suc (suc (suc n))) (fbet .fst) (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) (inr x)
             ≡ alt n f' (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n)) (inr x)
           alt≡inr x with (n ≟ᵗ n)
           ... | lt x₁ = ⊥.rec (¬m<ᵗm x₁)
           ... | eq x₁ = λ i → inr ((cong (λ p → subst (fst Xsk) p (fst f' x))
             (cong sym (isSetℕ _ _ (cong suc (cong suc x₁)) refl))
             ∙ transportRefl (fst f' x)) i)
           ... | gt x₁ = ⊥.rec (¬m<ᵗm x₁)

           alt≡push : (a : _) → Square refl (alt≡inr (CW↪ (Sˢᵏᵉˡ (suc n)) (suc n) a))
             (push (makeFinSequenceMapGen Xsk (suc n) x₀ (fst f') (snd f') (suc n) (Trichotomyᵗ-suc (n ≟ᵗ suc n)) a)
               ∙ (λ i → inr (makeFinSequenceMapComm Xsk (suc n) x₀ (fst f') (snd f') (suc n)
                               (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n)) a (~ i))))
             (cong (alt n f' (Trichotomyᵗ-suc (Trichotomyᵗ-suc (n ≟ᵗ n))) (Trichotomyᵗ-suc (n ≟ᵗ suc n))) (push a))
           alt≡push a with (n ≟ᵗ n)
           ... | lt x = ⊥.rec (¬m<ᵗm x)
           ... | eq x = flipSquare (help (cong suc (cong suc x)) (sym (isSetℕ _ _ _ _)))
             where
             open import Cubical.Foundations.Path
             cool : makeFinSequenceMapGen∙ Xsk _ x₀ (fst f') (snd f') (suc n) (eq refl)
                  ≡ transportRefl _ ∙ snd f'
             cool = cong₂ _∙_ (λ j i → subst (fst Xsk) (isSet→isGroupoid isSetℕ _ _ _ _ (isSetℕ (suc (suc n)) _ refl refl) refl j i)
                              (snd f' i)) (transportRefl _)
                  ∙ λ i → (λ j → transportRefl (snd f' (j ∧ ~ i)) (j ∧ i))
                         ∙ λ j → transportRefl (snd f' (~ i ∨ j)) (i ∨ j)

             help : (w : suc (suc n) ≡ suc (suc n)) (t : refl ≡ w)
               → Square ((push (makeFinSequenceMapGen Xsk (suc n) x₀ (fst f') (snd f') (suc n) (Trichotomyᵗ-suc (n ≟ᵗ suc n)) a)
                         ∙ (λ i → inr (makeFinSequenceMapComm Xsk (suc n) x₀ (fst f') (snd f') (suc n)
                                         (eq w) (suc n ≟ᵗ suc (suc n)) a (~ i)))))
                          (λ i → alt n f' (eq w)
                            (Trichotomyᵗ-suc (n ≟ᵗ suc n)) (push a i))
                          (λ _ → inl tt)
                          λ i → inr ((cong (λ p → subst (fst Xsk) p (fst f' (invEq (SαEqGen (suc n) (suc n) (eq w)
                                           (Trichotomyᵗ-suc (n ≟ᵗ suc n))) (inl a))))
                                     (sym (cong sym t)) ∙ transportRefl _) i)
             help with (n ≟ᵗ suc n)
             ... | lt w =
               J> (cong₂ _∙_ refl ((λ j i → inr ((lUnit (cool j) (~ j)) (~ i)))
                                              ∙ cong sym (cong-∙ inr (transportRefl _)
                                                         (snd f'))
                                              ∙ symDistr _ _)
                        ∙ assoc _ _ _)
                        ◁ flipSquare (flipSquare (symP (compPath-filler
                                     (push (CWskel∙ Xsk x₀ n)
                                     ∙ (λ i₁ → inr (snd f' (~ i₁))))
                                     (sym (transportRefl (inr (f' .snd i0))))))
                        ▷ λ j i → inr (lUnit (transportRefl (fst f' (ptSn (suc n)))) j i))
             ... | eq x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) x <ᵗsucm))
             ... | gt x = ⊥.rec (¬-suc-n<ᵗn x)
           ... | gt x = ⊥.rec (¬m<ᵗm x)

           alt≡ : (x : _) → prefunctoriality.fn+1/fn (suc (suc (suc n))) (fbet .fst) (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) x
                          ≡ alt n f' (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n)) x
           alt≡ (inl x) = refl
           alt≡ (inr x) = alt≡inr x
           alt≡ (push a i) = alt≡push a i

           bouquetFunct≡ : prefunctoriality.bouquetFunct (suc (suc (suc n))) (fbet .fst) (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm)
                         ≡ F n f' (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n))
           bouquetFunct≡ = funExt (λ x → cong (G n) (alt≡ _))
    

         fbet = (betterFinCellApproxS Xsk (suc n) x₀ f'
                        (incl∙ Xsk x₀ ∘∙ f') (λ _ → refl) (suc (suc (suc n))))
         gbet = (betterFinCellApproxS Xsk (suc n) x₀ g'
                        (incl∙ Xsk x₀ ∘∙ g') (λ _ → refl) (suc (suc (suc n))))


         -- anId : (n m : ℕ) (p : _) (q : _) (t : _)
         --   → cong (invEq (SαEqGen (suc n) (suc m) (eq (cong (suc ∘ suc) (sym p))) (lt q))) (λ i → inr (push (fzero , t) i))
         --   ≡ cong (Iso.inv (IsoSucSphereSusp n)) (merid (subst S₊ (sym p) t))
         -- anId zero = J> λ q t → {!cong (fst (SαMainEqGen (suc zero) zero (eq refl) (lt q))) loop!}
         -- anId (suc n) m p q t = {!!}

         wraplem : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) (l1 l2 : y ≡ y)
           → p ∙∙ (l1 ∙ l2) ∙∙ sym p
           ≡ (p ∙∙ l1 ∙∙ sym p) ∙ (p ∙∙ l2 ∙∙ sym p)
         wraplem = J> λ l1 l2 → sym (rUnit _) ∙ cong₂ _∙_ (rUnit l1) (rUnit l2)

         itMain : (n : ℕ) (f' g' : _) (p : _) (q : _) (x : _)
           → F n (∙Π f' g') p q x
           ≡ SphereBouquet∙Π (F n f' p q , refl)
                             (F n g' p q , refl) .fst x
         itMain n f' g' (lt x₁) q x = ⊥.rec (¬m<ᵗm x₁)
         itMain n f' g' (eq x₁) (lt x₂) (inl x) = refl
         itMain zero f' g' (eq x₁) (lt x₂) (inr (t , base)) = refl
         itMain zero f' g' (eq x₁) (lt x₂) (inr ((zero , tt) , loop i)) j = M j i -- M j i
           where
           L : (h : S₊∙ 1 →∙ X* zero)
             → cong (alt zero h (eq x₁) (lt x₂)
                                 ∘ inr ∘ invEq (SαEqGen 1 1 (eq x₁) (lt x₂)))
                                 (push (fzero , false) ∙ sym (push (fzero , true)))
             ≡ λ i → inr (fst h (loop i))
           L h = cong-∙  (alt zero h (eq x₁) (lt x₂)
                        ∘ inr ∘ invEq (SαEqGen 1 1 (eq x₁) (lt x₂)))
                          (push (fzero , false)) (sym (push (fzero , true)))
               ∙ cong₂ _∙_ (λ i j → inr (h .fst (SuspBool→S¹ (merid (subst S₊ (isSetℕ _ _ (cong (predℕ ∘ predℕ) x₁) refl i) false) j))))
                           (λ i j → inr (h .fst (SuspBool→S¹ (merid (subst S₊ (isSetℕ _ _ (cong (predℕ ∘ predℕ) x₁) refl i) true) (~ j)))))
               ∙ sym (rUnit _)
           w = cong (F zero f' (eq x₁) (lt x₂)) (sym (push fzero)) ∙ refl
           M : cong (F zero (∙Π f' g') (eq x₁) (lt x₂)) (λ i → inr (fzero , loop i))
             ≡ (sym w ∙∙ cong (F zero f' (eq x₁) (lt x₂)) (λ i → inr (fzero , loop i)) ∙∙ w)
             ∙ (sym w ∙∙ cong (F zero g' (eq x₁) (lt x₂)) (λ i → inr (fzero , loop i)) ∙∙ w)
           M = cong (cong (G zero)) (cong-∙∙ (alt zero (∙Π f' g') (eq x₁) (lt x₂)) _ _ _
                                    ∙ cong₃ _∙∙_∙∙_ (sym (rUnit (push x₀))) (L (∙Π f' g')
                                    ∙ cong-∙ inr _ _)
                                    (cong sym (sym (rUnit (push x₀))))
                                    ∙ wraplem _ _ _ _)
             ∙ (cong-∙ (G zero) _ _
             ∙ cong₂ _∙_ (cong (cong (G zero))
               λ i → compPath-filler (push x₀) (λ t → inr (sym (snd f') t)) i
                   ∙∙ (λ j → inr (doubleCompPath-filler (sym (snd f')) (cong (fst f') loop) (snd f') (~ i) j))
                   ∙∙ sym (compPath-filler (push x₀) (λ t → inr (sym (snd f') t)) i))
               λ i → (cong (G zero))
                     (compPath-filler (push x₀) (λ t → inr (sym (snd g') t)) i
                   ∙∙ (λ j → inr (doubleCompPath-filler (sym (snd g')) (cong (fst g') loop) (snd g') (~ i) j))
                   ∙∙ sym (compPath-filler (push x₀) (λ t → inr (sym (snd g') t)) i)))
             ∙ cong₂ _∙_ (sym (cong (cong (G zero)) (cong-∙∙ (alt zero f' (eq x₁) (lt x₂)) _ _ _
                                    ∙ cong₃ _∙∙_∙∙_ refl (L f') refl))
                                    ∙ rUnit (cong (F zero f' (eq x₁) (lt x₂)) (λ i → inr (fzero , loop i)))
                       ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
                         (sym (cong (cong (G zero)) (cong-∙∙ (alt zero g' (eq x₁) (lt x₂)) _ _ _
                                    ∙ cong₃ _∙∙_∙∙_ refl (L g') refl))
                         ∙ rUnit (cong (F zero g' (eq x₁) (lt x₂)) (λ i → inr (fzero , loop i)))
                       ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
         itMain (suc n) f' g' (eq x₁) (lt x₂) (inr (t , north)) = refl
         itMain (suc n) f' g' (eq x₁) (lt x₂) (inr (t , south)) = refl
         itMain (suc n) f' g' (eq x₁) (lt x₂) (inr ((zero , tt) , merid a i)) j = M j i
           where
           H : (x : _) → transport (λ i₂ → S₊ (predℕ (predℕ (x₁ i₂)))) x ≡ x
           H x = cong (λ p → transport p x) (cong (cong S₊) (isSetℕ _ _ _ refl))
               ∙ transportRefl x

           Lelem : (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) (a : _)
             → _
           Lelem h a = (push (CWskel∙ Xsk x₀ (suc n))
                    ∙∙ (λ i → inr ((sym (snd h) ∙∙ cong (fst h) (σS a) ∙∙ snd h) i))
                    ∙∙ sym (push (CWskel∙ Xsk x₀ (suc n))))

           L : (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) (a : _)
             → cong (F (suc n) h (eq x₁) (lt x₂)) (λ i → inr (fzero , merid a i))
             ≡ cong (G (suc n)) (Lelem h a)
           L h a = cong (cong (G (suc n)))
               (cong-∙∙ (alt (suc n) h (eq x₁) (lt x₂)) _ _ _
             ∙ cong₃ _∙∙_∙∙_ refl
                (cong-∙ (alt (suc n) h (eq x₁) (lt x₂)
                              ∘ inr
                              ∘ invEq (SαEqGen (suc (suc n)) (suc (suc n)) (eq x₁) (lt x₂)))
                               (push (fzero , a)) (sym (push (fzero , ptSn (suc n))))
                       ∙ cong₂ _∙_ (λ j i → inr (h .fst (merid (H a j) i)))
                                   (λ j i → inr (h .fst (merid (H (ptSn (suc n)) j) (~ i))))
                       ∙ sym (cong-∙ (λ x → inr (h .fst x)) (merid a) (sym (merid (ptSn (suc n)))))) refl
             ∙ λ i → compPath-filler (push (CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)))
                                      (λ i → inr (snd h (~ i))) (~ i)
               ∙∙ (λ j → inr (doubleCompPath-filler (sym (snd h))
                                (λ i → fst h (σS a i))
                                (snd h) i j))
               ∙∙ sym (compPath-filler (push (CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)))
                                       (λ i → inr (snd h (~ i))) (~ i)))

           L∙ : (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) → cong (F (suc n) h (eq x₁) (lt x₂))
                (λ i → inr (fzero , merid (ptSn (suc n)) i))
              ≡ refl
           L∙ h = L h (ptSn (suc n)) ∙ cong (cong (G (suc n)))
             (cong₃ _∙∙_∙∙_ refl
               ((λ j i → inr ((cong₃ _∙∙_∙∙_ refl (cong (cong (fst h)) σS∙) refl
                             ∙ ∙∙lCancel (snd h)) j i))) refl
             ∙ ∙∙lCancel _)

           L' : (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) (a : _)
             → cong (F (suc n) h (eq x₁) (lt x₂)) (λ i → inr (fzero , σS a i)) ≡ L h a i1
           L' h a = cong-∙ (λ q → F (suc n) h (eq x₁) (lt x₂) (inr (fzero , q)))
                           (merid a) (sym (merid (ptSn (suc n))))
                  ∙ cong₂ _∙_ (L h a) (cong sym (L∙ h))
                  ∙ sym (rUnit (L h a i1))

           Lelem≡ : (a : _) → Lelem (·Susp (S₊∙ (suc n)) f' g') a ≡ Lelem f' a ∙ Lelem g' a
           Lelem≡ a =
             cong₃ _∙∙_∙∙_ refl
                   (λ i j → inr ((sym (rUnit (cong (fst (·Susp (S₊∙ (suc n)) f' g')) (σS a)))
                                ∙ cong-∙ (fst (·Susp (S₊∙ (suc n)) f' g'))
                                         (merid a) (sym (merid (ptSn (suc n))))
                                ∙ cong₂ _∙_ refl (cong sym
                                  (cong₂ _∙_
                                    (cong₃ _∙∙_∙∙_ refl
                                       (cong (cong (fst f')) (rCancel (merid (ptSn (suc n))))) refl
                                      ∙ ∙∙lCancel (snd f'))
                                    (cong₃ _∙∙_∙∙_ refl
                                       (cong (cong (fst g')) (rCancel (merid (ptSn (suc n))))) refl
                                      ∙ ∙∙lCancel (snd g'))
                                  ∙ sym (rUnit refl)))
                                ∙ sym (rUnit _)) i j)) refl
             ∙ cong₃ _∙∙_∙∙_ refl (cong-∙ inr _ _) refl
             ∙ wraplem _ _ _ _

           w = cong (F (suc n) f' (eq x₁) (lt x₂)) (sym (push fzero)) ∙ refl
           M : cong (F (suc n) (∙Π f' g') (eq x₁) (lt x₂)) (λ i → inr (fzero , merid a i))
             ≡ (sym w ∙∙ cong (F (suc n) f' (eq x₁) (lt x₂)) (λ i → inr (fzero , σS a i)) ∙∙ w)
             ∙ (sym w ∙∙ cong (F (suc n) g' (eq x₁) (lt x₂)) (λ i → inr (fzero , σS a i)) ∙∙ w)
           M = ((L (∙Π f' g') a
              ∙ cong (cong (G (suc n))) (Lelem≡ a))
              ∙ cong-∙ (G (suc n)) (Lelem f' a) (Lelem g' a))
             ∙ cong₂ _∙_
                 (rUnit _ ∙ cong₃ _∙∙_∙∙_ (rUnit refl) (sym (L' f' a)) (rUnit refl))
                 (rUnit _ ∙ cong₃ _∙∙_∙∙_ (rUnit refl) (sym (L' g' a)) (rUnit refl))

         itMain zero f' g' (eq x₁) (lt x₂) (push a i) = refl
         itMain (suc n) f' g' (eq x₁) (lt x₂) (push a i) = refl
         itMain n f' g' (eq x₁) (eq x₂) x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) x₂ <ᵗsucm))
         itMain n f' g' (eq x₁) (gt x₂) x = ⊥.rec (¬-suc-n<ᵗn x₂)
         itMain n f' g' (gt x₁) q x = ⊥.rec (¬m<ᵗm x₁)

         it : (x : _) → prefunctoriality.bouquetFunct (suc (suc (suc n)))
                (multCellMap .fst) (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) x
            ≡ SphereBouquet∙Π
               (prefunctoriality.bouquetFunct (suc (suc (suc n)))
                 (fbet .fst) (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) , refl)
               (prefunctoriality.bouquetFunct (suc (suc (suc n)))
                 (gbet .fst) (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) , refl) .fst x
         it x = funExt⁻ (bouquetFunct≡ (∙Π f' g') λ _ → refl) x
           ∙ itMain n f' g' _ _ x
           ∙ λ i → SphereBouquet∙Π
                     (bouquetFunct≡ f' (λ _ → refl) (~ i) , (λ _ → inl tt))
                     (bouquetFunct≡ g' (λ _ → refl) (~ i) , (λ _ → inl tt)) .fst x

         main : GoalTy (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g')
         main = funExt⁻ (cong fst (Hˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) Xsk n multCellMap)) (genHₙSⁿ n)
              ∙ cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
                ((λ i → bouquetDegree (λ x → it x i) .fst (λ _ → pos 1))
                   ∙ funExt⁻ (cong fst (bouquetDegree+ _ _ _
                      (prefunctoriality.bouquetFunct (suc (suc (suc n)))
                        (fbet .fst) (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) , refl)
                      (prefunctoriality.bouquetFunct (suc (suc (suc n)))
                        (gbet .fst) (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) , refl)))
                      λ _ → pos 1))
              ∙ cong₂ (GroupStr._·_ (snd (Hᶜʷ X' n)))
                      (funExt⁻ (cong fst (sym (Hˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) Xsk n
                        {f = incl ∘ fst f' ∘ invEq (isCWSphere (suc n) .snd)} fbet))) (genHₙSⁿ n))
                      ((funExt⁻ (cong fst (sym (Hˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) Xsk n
                        {f = incl ∘ fst g' ∘ invEq (isCWSphere (suc n) .snd)} gbet))) (genHₙSⁿ n)))

         lem : (f : _) (fp : incl∙ Xsk x₀ ∘∙ f' ≡ f)
               (g : _) (gp : incl∙ Xsk x₀ ∘∙ g' ≡ g)
           → GoalTy f g
         lem = J> (J> main)

  HurewiczHom : {n : ℕ} (X : CW ℓ-zero) (x : fst X) (conX : isConnected 2 (fst X))
              → GroupHom (π'Gr n (fst X , x)) (Hᶜʷ X n)
  fst (HurewiczHom {n = n} X x conX) = HurewiczMap X x
  snd (HurewiczHom {n = n} X x conX) = makeIsGroupHom λ f g → HurewiczMapHom X x f g conX

HurewiczMapFunct : {n : ℕ} (X Y : CW ℓ-zero) (x : fst X) (y : fst Y)
                    (g : (fst X , x) →∙ (fst Y , y))
    → Hᶜʷ→ {C = X} {D = Y} n (fst g) .fst ∘ HurewiczMap X x
    ≡ HurewiczMap Y y ∘ π'∘∙Hom n g .fst
HurewiczMapFunct {n = n} X Y x y g =
  funExt (ST.elim (λ _ → isOfHLevelPath 2 (GroupStr.is-set (Hᶜʷ Y n .snd)) _ _)
    λ f → funExt⁻ (sym (cong fst (Hᶜʷ→comp
             {C = Sᶜʷ (suc n)} {D = X} {E = Y} n (fst g) (fst f))))
             (genHₙSⁿ n))

open import Cubical.Homotopy.Connected
open import Cubical.CW.Properties
open import Hurewicz.random
open import Cubical.HITs.Truncation as TR

-- mereBouquetPushout : ∀ {ℓ} (X : CW ℓ-zero) (n : ℕ) (x : fst X)
--   → isConnectedCW (suc n) (fst X) → {!!}
-- mereBouquetPushout = {!!}

-- isGroupEquivHurewicz : {!!}
-- isGroupEquivHurewicz = {!!}

-- -- {-
-- -- (n : ℕ) (t* : Σ[ t ∈ X' (suc (suc (suc n))) ] Xₙ→X∞ n t ≡ x)
-- --            → IsGroupHom (π'Gr n (X' (suc (suc (suc n))) , fst t*) .snd)
-- --                          (HurewiczMap (subCW n) (fst t*))
-- --                          (Hᶜʷ (subCW n) n .snd)
-- -- -}

-- -- module preHom (X : Type) (x : X) (isConn : isConnected 0 X)
-- --   (isCW : isCW X)
-- --   where
-- --   X' : ℕ → Type
-- --   X' = isCW .fst .fst

-- --   Xₙ→X∞ : (n : ℕ) → X' (suc (suc (suc n))) → X
-- --   Xₙ→X∞ n = invEq (isCW .snd) ∘ incl


-- -- module _ (X : Type) (x : X) (isConn : isConnected 0 X)
-- --   (isCW : isCW X)
-- --   where
-- --   X' : ℕ → Type
-- --   X' = isCW .fst .fst

-- --   Xₙ→X∞ : (n : ℕ) → X' (suc (suc (suc n))) → X
-- --   Xₙ→X∞ n = invEq (isCW .snd) ∘ incl

-- --   connXₙ→X∞ : (n : ℕ) → isConnectedFun (suc (suc (suc n))) (Xₙ→X∞ n)
-- --   connXₙ→X∞ n = isConnectedComp (invEq (isCW .snd)) incl (suc (suc (suc n)))
-- --                   (isEquiv→isConnected _ (snd (invEquiv (isCW .snd))) _)
-- --                   (isConnected-CW↪∞ (suc (suc (suc n))) (fst isCW))

-- --   subCW : (n : ℕ) → CW ℓ-zero
-- --   fst (subCW n) = X' (suc (suc (suc n)))
-- --   snd (subCW n) = ∣ (subComplex (fst isCW) (suc (suc (suc n))))
-- --                 , (isoToEquiv (realiseSubComplex (suc (suc (suc n))) (fst isCW))) ∣₁


-- --   -- preHurewiczHom : (n : ℕ) (t* : Σ[ t ∈ X' (suc (suc (suc n))) ] Xₙ→X∞ n t ≡ x)
-- --   --          → IsGroupHom (π'Gr n (X' (suc (suc (suc n))) , fst t*) .snd)
-- --   --                        (HurewiczMap (subCW n) (fst t*))
-- --   --                        (Hᶜʷ (subCW n) n .snd)
-- --   -- preHurewiczHom n  = {!!}



-- --   assumptionTy : {!(n : ℕ) (t* : Σ[ t ∈ X' (suc (suc (suc n))) ] Xₙ→X∞ n t ≡ x)
-- --            → IsGroupHom (π'Gr n (X' (suc (suc (suc n))) , fst t*) .snd)
-- --                          (HurewiczMap (subCW n) (fst t*))
-- --                          (Hᶜʷ (subCW n) n .snd)!}
-- --   assumptionTy = {!!}

-- --   assumption : (n : ℕ) (t* : Σ[ t ∈ X' (suc (suc (suc n))) ] Xₙ→X∞ n t ≡ x)
-- --            → IsGroupHom (π'Gr n (X' (suc (suc (suc n))) , fst t*) .snd)
-- --                          (HurewiczMap (subCW n) (fst t*))
-- --                          (Hᶜʷ (subCW n) n .snd)
-- --   assumption n (t , q) = makeIsGroupHom (ST.elim2 {!!}
-- --     λ f g → PT.rec2 {!t!}
-- --       (λ apf apg → {!apf!}
-- --                   -- ∙ cong₂ (Hᶜʷ (subCW n) n .snd .GroupStr._·_ )
-- --                   --   (sym (funExt⁻ (cong fst (Hˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n))
-- --                   --     (subComplex (fst isCW) (suc (suc (suc n)))) n {f = f' f g} apf)) (genHₙSⁿ' n))
-- --                   --   ∙ ? -- cong (fst (Hˢᵏᵉˡ→ n (f' f g))) (genHₙSⁿ≡ n)
-- --                   --   )
-- --                   --   (sym (funExt⁻ (cong fst (Hˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n))
-- --                   --     (subComplex (fst isCW) (suc (suc (suc n)))) n {f = g' f g} apg)) (genHₙSⁿ' n))
-- --                   --   ∙ ?)
-- --                  ∙ {!!}) -- cong (fst (Hˢᵏᵉˡ→ n (g' f g))) (genHₙSⁿ≡ n)))
-- --       ((CWmap→finCellMap (Sˢᵏᵉˡ (suc n))
-- --         (subComplex (fst isCW) (suc (suc (suc n)))) (f' f g)) (suc (suc (suc n))))
-- --       ((CWmap→finCellMap (Sˢᵏᵉˡ (suc n))
-- --         (subComplex (fst isCW) (suc (suc (suc n)))) (g' f g)) (suc (suc (suc n)))))
-- --     where
-- --     abstract
-- --       genHₙSⁿ' : (n₁ : ℕ) → Hˢᵏᵉˡ (Sˢᵏᵉˡ (suc n₁)) n₁ .fst
-- --       genHₙSⁿ' = genHₙSⁿ

-- --       genHₙSⁿ≡ : (n : _) → genHₙSⁿ' n ≡ genHₙSⁿ n
-- --       genHₙSⁿ≡ n = refl
-- --     module _ (f g : S₊∙ (suc n) →∙ (X' (suc (suc (suc n))) , t)) where
-- --       f' = (Iso.fun (realiseSubComplex (suc (suc (suc n))) (isCW .fst)) ∘ fst f ∘ invEq (isCWSphere (suc n) .snd))
-- --       g' = (Iso.fun (realiseSubComplex (suc (suc (suc n))) (isCW .fst)) ∘ fst g ∘ invEq (isCWSphere (suc n) .snd))
-- --       fg' = (Iso.fun (realiseSubComplex (suc (suc (suc n))) (isCW .fst)) ∘ ∙Π f g .fst ∘ invEq (isCWSphere (suc n) .snd))
-- --       module _ (apf : finCellApprox (Sˢᵏᵉˡ (suc n))
-- --              (subComplex (fst isCW) (suc (suc (suc n)))) f'
-- --              (suc (suc (suc n))))
-- --              (apg : finCellApprox (Sˢᵏᵉˡ (suc n))
-- --              (subComplex (fst isCW) (suc (suc (suc n)))) g'
-- --              (suc (suc (suc n)))) where
-- --         funTy : (k : Fin (suc (suc (suc (suc n))))) (p : _) → Type _
-- --         funTy k p = Sfam (suc n) (fst k)
-- --                  → G.subComplexFam (fst isCW) (suc (suc (suc n))) (fst k) p

-- --         apf-fun :  (k : _) (p : _) → funTy k p
-- --         apf-fun (suc k , q) p x with (k ≟ᵗ suc n )
-- --         ... | lt x₁ = {!!}
-- --         ... | eq x₁ = {!!} -- FinSequenceMap.fmap (fst apf) ({!!} , {!!}) x
-- --         ... | gt x₁ = {!!}

-- --         apfg-fun :  (k : _) (p : _) (F G : funTy k p) → funTy k p
-- --         apfg-fun (zero , q) p F G ()
-- --         apfg-fun (suc k , q) p F G with (k ≟ᵗ suc n)
-- --         ... | lt x = {!!}
-- --         apfg-fun (suc k , q) (lt x₁) F G | eq x = {!!}
-- --         apfg-fun (suc k , q) (eq x₁) F G | eq x = {!!}
-- --         apfg-fun (suc k , q) (gt x₁) F G | eq x = {!!}
-- --         apfg-fun (suc k , q) (lt x₁) F G | gt x = {!!}
-- --         apfg-fun (suc k , q) (eq x₁) F G | gt x = {!!}
-- --         apfg-fun (suc k , q) (gt x₁) F G | gt x = {!!}

-- --         apfg : finCellApprox (Sˢᵏᵉˡ (suc n))
-- --                  (subComplex (fst isCW) (suc (suc (suc n)))) fg'
-- --                  (suc (suc (suc n)))
-- --         FinSequenceMap.fmap (fst apfg) = {!!}
-- --         FinSequenceMap.fcomm (fst apfg) = {!!}
-- --         snd apfg = {!!}

-- --   trivLem : (n : ℕ)
-- --     → Hˢᵏᵉˡ→ {C = subComplex (fst isCW) (suc (suc (suc n)))}
-- --              {D = isCW .fst} n (incl ∘ Iso.inv (realiseSubComplex (suc (suc (suc n))) (fst isCW)))
-- --      ≡ Hᶜʷ→ {C = subCW n} {D = X , ∣ isCW ∣₁}  n (Xₙ→X∞ n)
-- --   trivLem n = cong (Hˢᵏᵉˡ→ {C = subComplex (fst isCW) (suc (suc (suc n)))}
-- --              {D = isCW .fst} n) (funExt λ s → sym (secEq (snd isCW) _))

-- --   main : (n : ℕ) → Σ[ t ∈ X' (suc (suc (suc n))) ] Xₙ→X∞ n t ≡ x
-- --     → IsGroupHom (snd (π'Gr n (X , x))) (HurewiczMap (X , ∣ isCW ∣₁) x) (Hᶜʷ (X , ∣ isCW ∣₁) n .snd)
-- --   main n (t , q) =
-- --     compsToHom→Hom {G₂ = Hᶜʷ (X , ∣ isCW ∣₁) n} {G₃ = Hᶜʷ (subCW n) n}
-- --       (connected→π'Equiv n (_ , q) (connXₙ→X∞ n))
-- --       (GroupIso→GroupEquiv (subComplexHomology (fst isCW) (suc (suc (suc n))) n <ᵗsucm))
-- --       (HurewiczMap (X , ∣ isCW ∣₁) x)
-- --       (subst (λ f → IsGroupHom (π'Gr n (X' (suc (suc (suc n))) , t) .snd)
-- --                     f
-- --                     (Hᶜʷ (subCW n) n .snd))
-- --              (funExt (ST.elim (λ _ → isProp→isSet (squash/ _ _))
-- --                λ f → sym (Iso.rightInv (fst (subComplexHomology (fst isCW) (suc (suc (suc n))) n <ᵗsucm)) _)
-- --                ∙ cong (Iso.fun (fst (subComplexHomology (fst isCW) (suc (suc (suc n))) n <ᵗsucm)))
-- --                  (funExt⁻ (subComplexHomologyEquiv≡ (fst isCW) (suc (suc (suc n))) n <ᵗsucm)
-- --                    (Hᶜʷ→ {C = Sᶜʷ (suc n)} {D = subCW n}
-- --                         n (fst f) .fst (genHₙSⁿ n))
-- --                  ∙ funExt⁻ (cong fst (trivLem n)) (fst (Hᶜʷ→ {C = Sᶜʷ (suc n)} {D = subCW n} n (fst f)) (genHₙSⁿ n))
-- --                  ∙ sym (funExt⁻ (cong fst (Hᶜʷ→comp {C = Sᶜʷ (suc n)} {D = subCW n} {E = X , ∣ isCW ∣₁} n (Xₙ→X∞ n) (fst f))) (genHₙSⁿ n))
-- --                  ∙ λ _ → Hᶜʷ→ {C = Sᶜʷ (suc n)} {D = X , ∣ isCW ∣₁} n (Xₙ→X∞ n ∘ fst f) .fst (genHₙSⁿ n))))
-- --              (assumption n (t , q)))


-- -- TTT : {n : ℕ} (X : CW ℓ-zero) (x : fst X)
-- --   → isConnected 0 (fst X)
-- --   → IsGroupHom (snd (π'Gr n (fst X , x))) (HurewiczMap X x) (Hᶜʷ X n .snd)
-- -- TTT {n = N} = uncurry λ X → PT.elim {!!}
-- --   λ CWX x → λ conX → compsToHom→Hom {!isConnectedIncl∞!} {!!} {!!} {!!}


Hˢᵏᵉˡ-comm : ∀ {ℓ} {n : ℕ} {X : CWskel ℓ} (x y : Hˢᵏᵉˡ X n .fst)
  → GroupStr._·_ (Hˢᵏᵉˡ X n .snd) x y ≡ GroupStr._·_ (Hˢᵏᵉˡ X n .snd) y x
Hˢᵏᵉˡ-comm = SQ.elimProp2 (λ _ _ → GroupStr.is-set (Hˢᵏᵉˡ _ _ .snd) _ _)
  λ a b → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
    (funExt λ _ → +Comm _ _))

Hᶜʷ-comm : ∀ {ℓ} {n : ℕ} (X : CW ℓ) (x y : Hᶜʷ X n .fst)
  → GroupStr._·_ (Hᶜʷ X n .snd) x y ≡ GroupStr._·_ (Hᶜʷ X n .snd) y x
Hᶜʷ-comm {n = n} = uncurry λ X
  → PT.elim (λ _ → isPropΠ2 λ _ _ → GroupStr.is-set (Hᶜʷ (X , _) n .snd) _ _)
            λ x → Hˢᵏᵉˡ-comm

HᶜʷAb : ∀ {ℓ} → CW ℓ → ℕ → AbGroup ℓ-zero
HᶜʷAb X n = Group→AbGroup (Hᶜʷ X n) (Hᶜʷ-comm X)

HurewiczHomAb : (X : CW ℓ-zero) (x : fst X) (isC : isConnected 2 (fst X))
  (n : ℕ) → AbGroupHom (AbelianizationAbGroup (π'Gr n (fst X , x))) (HᶜʷAb X n)
fst (HurewiczHomAb X x isC n) =
  Abi.rec _ (AbGroupStr.is-set (snd (HᶜʷAb X n)))
            (HurewiczHom X x isC .fst)
            ish
  where
  ish : (a b c : _) → _
  ish a b c = IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _
            ∙ cong₂ (GroupStr._·_ (Hᶜʷ X n .snd)) refl
                (IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _
                ∙ AbGroupStr.+Comm (snd (HᶜʷAb X n)) _ _
                ∙ sym (IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _))
            ∙ sym (IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _)
snd (HurewiczHomAb X x isC n) =
  makeIsGroupHom (Abi.elimProp2 _ (λ _ _ → GroupStr.is-set (snd (Hᶜʷ X n)) _ _)
    (IsGroupHom.pres· (HurewiczHom X x isC .snd)))

oooh = subComplex

subCWExplicit : ∀ {ℓ} (n : ℕ) → CWexplicit ℓ → CWexplicit ℓ
fst (subCWExplicit n (X , Xsk , e)) = Xsk .fst n
fst (snd (subCWExplicit n (X , Xsk , e))) = subComplex Xsk n
snd (snd (subCWExplicit n (X , Xsk , e))) = isoToEquiv (realiseSubComplex n Xsk)


CWexplicit→CW : ∀ {ℓ} → CWexplicit ℓ → CW ℓ
CWexplicit→CW C = fst C , ∣ snd C ∣₁

subCW : ∀ {ℓ} (n : ℕ) → CWexplicit ℓ → CW ℓ
subCW n X = CWexplicit→CW (subCWExplicit n X)

ConnectedCW : (ℓ : Level) (n : ℕ) → Type (ℓ-suc ℓ)
ConnectedCW ℓ n = Σ[ X ∈ Type ℓ ] isConnectedCW n X

ConnectedCW→CWexplicit : ∀ {ℓ} {n : ℕ} → ConnectedCW ℓ n → CWexplicit ℓ
fst (ConnectedCW→CWexplicit (X , p , con)) = X
fst (fst (snd (ConnectedCW→CWexplicit (X , (Xsk , _ , _) , con)))) = Xsk
snd (fst (snd (ConnectedCW→CWexplicit (X , (Xsk , p , _) , con)))) = p
snd (snd (ConnectedCW→CWexplicit (X , (Xsk , _ , _) , con))) = invEquiv con

ConnectedCW→CW : ∀ {ℓ} {n : ℕ} → ConnectedCW ℓ n → CW ℓ
ConnectedCW→CW X = CWexplicit→CW (ConnectedCW→CWexplicit X)

isConnected→BouquetEquiv : (n : ℕ) (X : CWexplicit ℓ-zero)
  (t : yieldsConnectedCWskel (fst (fst (snd X))) (suc (suc n)))
  (conX : isConnected (suc (suc n)) (fst X))
    → ∃[ c1 ∈ ℕ ] Σ[ c2 ∈ ℕ ]
      Σ[ α ∈ SphereBouquet∙ (suc n) (Fin c1) →∙ SphereBouquet∙ (suc n) (Fin c2) ]
        snd X .fst .fst (suc (suc (suc n)))
      ≡ cofib (fst α)
isConnected→BouquetEquiv n X t conX =
  PT.rec {!!}
    (λ p → {!!})
    (makeConnectedCW n (snd X) conX)
  where
  CWAlt : {!!}
  CWAlt = {!!}
  X' = fst (fst (snd X))
  module _  where
    H : (n : ℕ) (conX' : isConnectedCW n (fst X)) → isContr (X' (suc n))
    H zero conX' =
      subst isContr (cong Fin {!!}
                  ∙ sym (ua (CW₁-discrete (fst (snd X))))) {!!}
    H (suc n) conX' = {!!}
    {-
      subst isContr (sym (ua (X .snd .fst .snd .snd .snd .snd n)))
        ((inl {!!}) , {!!}) -- ((inl {!conX' .fst .snd .snd .snd!}) , {!!}) -- ((inl {!!}) , {!!}) -- λ { (inl x) → {!!} ; (inr x) → {!!} ; (push a i) → {!!}})
-}

PreHurewiczLemma : (n : ℕ) (X : CWexplicit ℓ-zero) (conX : isConnected 2 (fst X))
  → ((l : _) (str : _) (t : _)
    → isEquiv (HurewiczHomAb (X .snd .fst .fst (suc (suc (suc n))) , str) l t n .fst))
  → (x : fst X) → isEquiv (HurewiczHomAb  (fst X , ∣ snd X ∣₁) x conX n .fst)
PreHurewiczLemma n X conX ind' x =
  TR.rec (isPropIsEquiv _)
    (λ t → subst isEquiv (funExt {!!}) (altEquiv t .fst .snd))
    (isConnected-CW↪∞ (suc zero) (fst (snd X)) (fst (snd (snd X)) x) .fst)
  where
  SubX : CW ℓ-zero
  SubX = ((realise (subComplex (fst (snd X)) (suc (suc (suc n)))))
                      , ∣ (subComplex (fst (snd X)) (suc (suc (suc n)))) , (idEquiv _) ∣₁)

  module _ (t : fiber (CW↪∞ (fst (snd X)) (suc zero)) (fst (snd (snd X)) x)) where

    x' : fst SubX
    x' = Iso.fun (realiseSubComplex (suc (suc (suc n))) (fst (snd X)))
                 (CWskel∙ (fst (snd X)) (fst t) (suc (suc n)))

    p' : invEq (snd (snd X)) (incl (fst t)) ≡ x
    p' = cong (invEq (snd (snd X))) (snd t) ∙ retEq (snd (snd X)) x

    F₃ : _ →∙ _
    fst F₃ = Iso.inv (realiseSubComplex (suc (suc (suc n))) (fst (snd X)))
    snd F₃ = Iso.leftInv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))) _

    F∙ : (fst SubX , x') →∙ (fst X , x)
    F∙ = (invEq (snd (snd X)) , p')
      ∘∙ (incl∙ (fst (snd X)) (fst t)
      ∘∙ F₃)

    isConnF∙ : isConnectedFun (suc (suc (suc n))) (fst F∙)
    isConnF∙ = isConnectedComp (invEq (snd (snd X))) _ (suc (suc (suc n)))
      (isEquiv→isConnected _ (snd (invEquiv (snd (snd X)))) _)
      (isConnectedComp incl (F₃ .fst) (suc (suc (suc n)))
        (isConnected-CW↪∞ (suc (suc (suc n))) _)
        (isEquiv→isConnected _
          (isoToIsEquiv (invIso (realiseSubComplex (suc (suc (suc n))) (fst (snd X))))) _))

    conS' : isConnected 2 (fst (fst (snd X)) (suc (suc (suc n))))
    conS' = connectedFunPresConnected 2 (subst (isConnected 2) (ua (snd X .snd)) conX)
              λ b →  isConnectedSubtr' (suc n) 2 (isConnected-CW↪∞ (suc (suc (suc n))) (fst (snd X)) b)

    conS : isConnected 2 (fst SubX)
    conS = subst (isConnected 2) (isoToPath (realiseSubComplex (suc (suc (suc n))) (fst (snd X))))
            conS'

    H = HurewiczHomAb SubX x' conS n

    isEqH : isEquiv (fst H)
    isEqH = transport (λ i → isEquiv (fst (HurewiczHomAb (h i .fst) (h i .snd .fst) (h i .snd .snd) n)))
                      (ind' (CWskel∙ (fst (snd X)) (fst t) (suc (suc n)))
                       ∣ subComplex (fst (snd X)) (suc (suc (suc n)))
                       , isoToEquiv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))) ∣₁
                      conS')
      where
      h : Path (Σ[ X ∈ CW ℓ-zero ] (Σ[ x ∈ fst X ] isConnected 2 (fst X)))
               ((_ , ∣ subComplex (fst (snd X)) (suc (suc (suc n)))
                       , isoToEquiv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))) ∣₁)
               , ((CWskel∙ (fst (snd X)) (fst t) (suc (suc n))) , conS'))
               (SubX , (x' , conS))
      h = ΣPathP ((Σ≡Prop (λ _ → squash₁)
                 (isoToPath (realiseSubComplex (suc (suc (suc n))) (fst (snd X)))))
               , (ΣPathPProp (λ _ → isPropIsContr) (toPathP (cong incl
                 (transportRefl _)))))

    altEquiv : AbGroupEquiv (AbelianizationAbGroup (π'Gr n (fst X , x)))
                            ((HᶜʷAb (fst X , ∣ snd X ∣₁) n))
    altEquiv =
      compGroupEquiv
        (invGroupEquiv (connected→Abπ'Equiv n F∙ isConnF∙))
         (compGroupEquiv ((fst H , isEqH) , snd H)
           (subComplexHomologyEquiv (fst (snd X)) n (suc (suc (suc n))) <ᵗsucm))

    help : (a : _) → altEquiv .fst .fst a ≡ HurewiczHomAb (fst X , ∣ snd X ∣₁) x conX n .fst a
    help = Abi.elimProp _ (λ _ → squash/ _ _)
      (λ f → better _
        ∙ cong (HurewiczHomAb (fst X , ∣ snd X ∣₁) x conX n .fst)
           (secEq (fst (connected→Abπ'Equiv n F∙ isConnF∙)) (η f)))
      where
      better : (t : _)
        → Hᶜʷ→ {C = subCW (suc (suc (suc n))) X}
                 {D = realise (fst (snd X)) , ∣ (fst (snd X)) , (idEquiv _) ∣₁} n incl
                 .fst (HurewiczHomAb SubX x' conS n .fst (η t))
          ≡ HurewiczHomAb (fst X , ∣ snd X ∣₁) x conX n .fst (fst (fst (connected→Abπ'Equiv n F∙ isConnF∙)) (η t))
      better = ST.elim (λ _ → isProp→isSet (squash/ _ _))
        λ g → funExt⁻ (cong fst
            (sym (Hᶜʷ→comp {C = Sᶜʷ (suc n)}
                           {D = SubX}
                           {E = realise (fst (snd X))
                              , ∣ (fst (snd X)) , (idEquiv _) ∣₁}
                  n (incl
                  ∘ Iso.inv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))))
                  (fst g))))
                  (genHₙSⁿ n)
             ∙ λ i → Hᶜʷ→ {C = Sᶜʷ (suc n)}
                        {D = realise (fst (snd X))
                           , ∣ (fst (snd X)) , (idEquiv _) ∣₁} n
                           (λ z → secEq (snd (snd X)) (incl (F₃ .fst (fst g z))) (~ i))
                           .fst (genHₙSⁿ n)

-- PreHurewiczLemma : (n : ℕ) (X : CWexplicit ℓ-zero) (conX : isConnected 2 (fst X))
--   → ((l : _) (str : _)
--     → isEquiv (HurewiczMap {n = n} (X .snd .fst .fst (suc (suc (suc n))) , str) l))
--   → (x : fst X) → isEquiv (HurewiczMap {n = n} (fst X , ∣ snd X ∣₁) x)
-- PreHurewiczLemma n X conX ind' x =
--   TR.rec (isPropIsEquiv _)
--     (λ t → subst isEquiv (funExt (help t)) (altEquiv t .snd))
--     (isConnected-CW↪∞ (suc zero) (fst (snd X)) (fst (snd (snd X)) x) .fst)
--   where
--   SubX : CW ℓ-zero
--   SubX = ((realise (subComplex (fst (snd X)) (suc (suc (suc n)))))
--                       , ∣ (subComplex (fst (snd X)) (suc (suc (suc n)))) , (idEquiv _) ∣₁)

--   ind : ((l : _) → isEquiv (HurewiczMap {n = n} SubX (incl {n = suc zero} l)))
--   ind l = transport (λ j → isEquiv (HurewiczMap {n = n} (cool (~ j)) (k (~ j))))
--                     (ind' _ _)
--     where
--     cool : Path (CW ℓ-zero) SubX
--             ((fst (snd X) .fst (suc (suc (suc n))))
--               , ∣ subComplex (fst (snd X)) (suc (suc (suc n)))
--               , isoToEquiv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))) ∣₁)
--     cool = Σ≡Prop (λ _ → squash₁)
--       (isoToPath (invIso (realiseSubComplex (suc (suc (suc n))) (fst (snd X)))))

--     k : PathP (λ i → fst (cool i)) (incl {n = suc zero} l)
--               (transport (cong fst cool) (incl {n = suc zero} l))
--     k = toPathP refl

--   module _ (t : fiber (CW↪∞ (fst (snd X)) (suc zero)) (fst (snd (snd X)) x)) where

--     x' : fst SubX
--     x' = Iso.fun (realiseSubComplex (suc (suc (suc n))) (fst (snd X)))
--                  (CWskel∙ (fst (snd X)) (fst t) (suc (suc n)))

--     p' : invEq (snd (snd X)) (incl (fst t)) ≡ x
--     p' = cong (invEq (snd (snd X))) (snd t) ∙ retEq (snd (snd X)) x

--     F₃ : _ →∙ _
--     fst F₃ = Iso.inv (realiseSubComplex (suc (suc (suc n))) (fst (snd X)))
--     snd F₃ = Iso.leftInv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))) _

--     F∙ : (fst SubX , x') →∙ (fst X , x)
--     F∙ = (invEq (snd (snd X)) , p')
--       ∘∙ (incl∙ (fst (snd X)) (fst t)
--       ∘∙ F₃)

--     isConnF∙ : isConnectedFun (suc (suc (suc n))) (fst F∙)
--     isConnF∙ = isConnectedComp (invEq (snd (snd X))) _ (suc (suc (suc n)))
--       (isEquiv→isConnected _ (snd (invEquiv (snd (snd X)))) _)
--       (isConnectedComp incl (F₃ .fst) (suc (suc (suc n)))
--         (isConnected-CW↪∞ (suc (suc (suc n))) _)
--         (isEquiv→isConnected _
--           (isoToIsEquiv (invIso (realiseSubComplex (suc (suc (suc n))) (fst (snd X))))) _))

--     HurewiczEq = (HurewiczMap {n = n} SubX x' , subst (isEquiv ∘  HurewiczMap SubX)
--           (sym (CWskel∞∙Id  (subComplex (fst (snd X)) (suc (suc (suc n)))) (fst t) (suc (suc n)))
--           ∙ cong (incl {n = suc (suc (suc n))}) (CWskel∙SubComplex _ _ _))
--           (ind (fst t)))

--     altEquiv : π' (suc n) (fst X , x) ≃ fst (Hᶜʷ (fst X , ∣ snd X ∣₁) n)
--     altEquiv =
--       compEquiv
--       (compEquiv (invEquiv (fst (connected→π'Equiv n F∙ isConnF∙)))
--         HurewiczEq)
--       (subComplexHomologyEquiv (fst (snd X)) n (suc (suc (suc n))) <ᵗsucm .fst)

--     help : (a : _) → altEquiv .fst a ≡ HurewiczMap (fst X , ∣ snd X ∣₁) x a
--     help f = better (invEq (fst (connected→π'Equiv n F∙ isConnF∙)) f)
--         ∙ cong (HurewiczMap (fst X , ∣ snd X ∣₁) x)
--            (secEq (fst (connected→π'Equiv n F∙ isConnF∙)) f)
--       where
--       better : (t : _)
--         → Hᶜʷ→ {C = subCW (suc (suc (suc n))) X}
--                  {D = realise (fst (snd X)) , ∣ (fst (snd X)) , (idEquiv _) ∣₁} n incl
--                  .fst (HurewiczMap {n = n} SubX x' t)
--           ≡ HurewiczMap (fst X , ∣ snd X ∣₁) x (π'∘∙Hom n F∙ .fst t)
--       better = ST.elim (λ _ → isProp→isSet (squash/ _ _))
--         λ g → (funExt⁻ (cong fst
--             (sym (Hᶜʷ→comp {C = Sᶜʷ (suc n)}
--                            {D = SubX}
--                            {E = realise (fst (snd X))
--                               , ∣ (fst (snd X)) , (idEquiv _) ∣₁}
--                   n (incl
--                   ∘ Iso.inv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))))
--                   (fst g))))
--                   (genHₙSⁿ n))
--           ∙ λ i → Hᶜʷ→ {C = Sᶜʷ (suc n)}
--                         {D = realise (fst (snd X))
--                            , ∣ (fst (snd X)) , (idEquiv _) ∣₁} n
--                            (λ z → secEq (snd (snd X)) (incl (F₃ .fst (fst g z))) (~ i))
--                            .fst (genHₙSⁿ n)
open import Hurewicz.SphereBouquetCofib2
open import Hurewicz.SphereBouquetCofibHomotopy
open import Cubical.HITs.Bouquet
open import Cubical.HITs.FreeGroup.Base


HurewiczSphereBouquet' : (n m k : ℕ) 
  (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
  (t : _)
  → isEquiv (fst (HurewiczHomAb (SphereBouquet/ᶜʷ (fst α)) (inl tt) t n))
HurewiczSphereBouquet' n m k α t = {!fst (HurewiczHomAb (SphereBouquet/ᶜʷ (fst α)) (inl tt) t n)!}
  where
  pts : (p : _) → SphereBouquet/Fam* m k (fst α) (suc (suc n)) p
  pts (lt x) = tt
  pts (eq x) = inl tt
  pts (gt x) = inl tt

  thef : (p : _) → SphereBouquet (suc n) (Fin k)
                 →  (SphereBouquet/Fam* m k (fst α) (suc (suc n)) p)
  thef (lt x) = {!!} -- const∙ _ _
  thef (eq x) = {!!} -- idfun∙ _
  thef (gt x) = {!!} -- const∙ _ _
  
  module _ (f : S₊∙ (suc n) →∙ (cofib (fst α) , inl tt)) (f' : S₊∙ (suc n) →∙ SphereBouquet∙ (suc n) (Fin k))
      (f≡ : (inr , (λ i → inr (α .snd (~ i))) ∙ sym (push (inl tt))) ∘∙ f' ≡ f)
      (s1 : _) (s2 : _) (s3 : _) where
    rewriteguy : Hˢᵏᵉˡ→ {C = Sˢᵏᵉˡ (suc n)} {D = SphereBouquet/ˢᵏᵉˡ (fst α)}
                             n (fst (snd (isCWSphereBouquet/ (fst α))) ∘ fst f ∘ invEq (snd (isCWSphere (suc n))))
               ≡ {!!}
    rewriteguy = (λ _ → Hˢᵏᵉˡ→ {C = Sˢᵏᵉˡ (suc n)} {D = SphereBouquet/ˢᵏᵉˡ (fst α)}
                             n (fst (snd (isCWSphereBouquet/ (fst α))) ∘ fst f ∘ invEq (snd (isCWSphere (suc n)))))
              ∙ Hˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) (SphereBouquet/ˢᵏᵉˡ (fst α)) n
                  (betterFinCellApproxS (SphereBouquet/ˢᵏᵉˡ (fst α)) (suc n) tt
                    ((thef (Trichotomyᵗ-suc (Trichotomyᵗ-suc (n ≟ᵗ n))) ∘ fst f') , s1)
                    ((fst (snd (isCWSphereBouquet/ (fst α))) , s2) ∘∙ f) s3
                    (suc (suc (suc n))))
              ∙ {!!}
              ∙ {! bouquetDegree+!}


-- HurewiczSphereBouquet : (n m k : ℕ) 
--   (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
--   (t : _)
--   → isEquiv (fst (HurewiczHomAb (SphereBouquet/ᶜʷ (fst α)) (inl tt) t n))
-- HurewiczSphereBouquet zero m k α =
--   J (λ α _ → (t : isConnected 2 (fst (SphereBouquet/ᶜʷ (fst α)))) →
--       isEquiv (fst (HurewiczHomAb (SphereBouquet/ᶜʷ (fst α)) (inl tt) t zero)))
--                (mains (fst improveα))
--                (snd improveα)
--   where
--   abstract
--     improveα : Σ[ α' ∈ (Fin m → FreeGroup (Fin k)) ]
--                  (Iso.fun sphereBouqetMapIso (Iso.inv CharacBouquet→∙Bouquet α') ≡ α)
--     fst improveα = {!!} -- Iso.inv (compIso (invIso CharacBouquet→∙Bouquet) sphereBouqetMapIso) α 
--     snd improveα = {!!} -- Iso.rightInv (compIso (invIso CharacBouquet→∙Bouquet) sphereBouqetMapIso) α

--   module _ (α' : Fin m → FreeGroup (Fin k)) (t : _) where

--     altEquiv : AbGroupIso
--       (AbelianizationAbGroup (π'Gr zero (fst (SphereBouquet/ᶜʷ (fst (spB.αSphereBouquet α'))) , inl tt)))
--       (HᶜʷAb (SphereBouquet/ᶜʷ (fst (spB.αSphereBouquet α'))) zero)
--     altEquiv =
--       compGroupIso (spB.π'BoquetFunCofib≅Free/Imα>1 α')
--         ((invGroupIso (GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap (spB.αSphereBouquet α' .fst))))


--     main' : compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _)
--               (GroupIso→GroupHom altEquiv)
--           ≡ compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _)
--               (HurewiczHomAb (SphereBouquet/ᶜʷ (fst (spB.αSphereBouquet α'))) (inl tt) t zero)
--     main' = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
--       (funExt (ST.elim {!!}
--         λ f → {!!}
--              ∙ sym (funExt⁻ (cong fst (Hˢᵏᵉˡ→β (Sˢᵏᵉˡ 1) (fst (isCWSphereBouquet/ (fst (spB.αSphereBouquet α')))) zero {f = (fst (snd (isCWSphereBouquet/ (fst (spB.αSphereBouquet α')))) ∘ fst f ∘ invEq (snd (isCWSphere 1)))} (betterFinCellApproxS _ 1 tt {!!} (fst (snd (isCWSphereBouquet/ (fst (spB.αSphereBouquet α')))) ∘ fst f , {!!}) {!!} 3))) (genHₙSⁿ zero))
--              ∙ (λ _ → Hˢᵏᵉˡ→ {C = Sˢᵏᵉˡ 1} {D = SphereBouquet/ˢᵏᵉˡ (fst (spB.αSphereBouquet α'))}
--                              zero (fst (snd (isCWSphereBouquet/ (fst (spB.αSphereBouquet α')))) ∘ fst f ∘ invEq (snd (isCWSphere 1))) .fst (genHₙSⁿ zero))
--              ∙ {!!}
--              ∙ λ _ → preHurewiczMap (SphereBouquet/ᶜʷ (fst (spB.αSphereBouquet α'))) (inl tt) f .fst (genHₙSⁿ zero)))

--     mains : isEquiv (fst (HurewiczHomAb
--                     (SphereBouquet/ᶜʷ (fst (spB.αSphereBouquet α'))) (inl tt) t zero))
--     mains = subst isEquiv {!!} {!!}

-- HurewiczSphereBouquet (suc n) m k α t = {!!}

-- -- TEST : (n : ℕ) (X : CW ℓ-zero) (conX : isConnected (suc (suc n)) (fst X)) (x : _)
-- --   → isEquiv (HurewiczHomAb X x (isConnectedSubtr' n 2 conX) n .fst)
-- -- TEST n = uncurry λ X → PT.elim (λ _ → isPropΠ2  λ _ _ → isPropIsEquiv _)
-- --   λ cw isc → PT.rec (isPropΠ (λ _ → isPropIsEquiv _))
-- --     (λ cw' x → E X cw cw' isc x)
-- --     (makeConnectedCW n cw isc)
-- --   where
-- --   isEqTransport : (cw1 cw2 : CW ℓ-zero) (P : cw1 ≡ cw2)
-- --     (con1 : isConnected 2 (fst cw1)) (con2 : isConnected 2 (fst cw2))
-- --     (x' : fst cw1) (x : fst cw2) (PP : PathP (λ i → fst (P i)) x' x)
-- --     → isEquiv (HurewiczHomAb cw1 x' con1 n .fst)
-- --     → isEquiv (HurewiczHomAb cw2 x con2 n .fst)
-- --   isEqTransport cw1 = J> λ con1 con2 x'
-- --     → J> subst (λ c → isEquiv (HurewiczHomAb cw1 x' c n .fst)) (isPropIsContr _ _)

-- --   HA : (X : _) (cw cw' : _) → Path (CW ℓ-zero) ((X , ∣ cw ∣₁)) (X , ∣ cw' ∣₁)
-- --   HA = λ X cw cw' → Σ≡Prop (λ _ → squash₁) refl

-- --   e1 : (n m : ℕ) (l : m <ᵗ suc n) (X : Type) (cwX : isConnectedCW n X)
-- --     → isContr (fst (fst cwX) (suc m))
-- --   e1 n zero l X cwX =
-- --     subst isContr (cong Fin (sym ((snd (fst cwX)) .snd .fst))
-- --                   ∙ sym (ua (CW₁-discrete (fst (fst cwX)
-- --                                         , fst (snd (fst cwX))))))
-- --          (inhProp→isContr fzero isPropFin1)
-- --   e1 n (suc m) l X cwX =
-- --     subst isContr
-- --       (ua (compEquiv (isoToEquiv (PushoutEmptyFam
-- --         (¬Fin0 ∘ subst Fin (snd (fst cwX) .snd .snd m l) ∘ fst)
-- --         (¬Fin0 ∘ subst Fin (snd (fst cwX) .snd .snd m l))))
-- --         (invEquiv (snd (snd (snd (fst (snd (fst cwX))))) (suc m)))))
-- --       (e1 n m (<ᵗ-trans l <ᵗsucm) X cwX)

-- --   open import Cubical.Data.Unit
-- --   open import Cubical.HITs.Wedge.Base

  
-- --   e2 : (n : ℕ) (X : Type) (cwX : isConnectedCW n X)
-- --     → fst (fst cwX) (suc (suc n))
-- --     ≃ SphereBouquet (suc n) (Fin (fst (fst (snd (fst cwX))) (suc n)))
-- --   e2 n X cwX =
-- --     compEquiv
-- --       (snd (snd (snd (fst (snd (fst cwX))))) (suc n))
-- --       (compEquiv
-- --        (pushoutEquiv _ _ _ fst
-- --          (idEquiv _)
-- --          (isContr→≃Unit (e1 n n <ᵗsucm X cwX))
-- --          (idEquiv _)
-- --          (λ _ _ → tt)
-- --          (λ i x → fst x))
-- --        (compEquiv (isoToEquiv (Iso-cofibFst-⋁ (λ A → S₊∙ n)))
-- --        (pushoutEquiv _ _ _ _ (idEquiv _) (idEquiv _)
-- --          (Σ-cong-equiv-snd (λ _ → isoToEquiv (invIso (IsoSucSphereSusp n))))
-- --          (λ _ _ → tt) (λ i x → x , IsoSucSphereSusp∙ n i))))

-- --   e3 : (n : ℕ) (X : Type) (cwX : isConnectedCW n X) (str : _)
-- --     → ∃[ α ∈ SphereBouquet∙ (suc n) (Fin (fst (fst (snd (fst cwX))) (suc (suc n))))
-- --          →∙ SphereBouquet∙ (suc n) (Fin (fst (fst (snd (fst cwX))) (suc n))) ]
-- --          ((fst cwX .fst (suc (suc (suc n)))) , str) ≡ SphereBouquet/ᶜʷ  (fst α)
-- --   e3 n X cwX str = PT.rec squash₁
-- --     (λ {(x , ptz , t) → ∣ F x ptz t , Σ≡Prop (λ _ → squash₁) (isoToPath (e3' x ptz t)) ∣₁})
-- --     EX
-- --     where
-- --     open import Cubical.Axiom.Choice
-- --     open import Cubical.HITs.Wedge.Properties
-- --     CON : isConnected 2 (fst (fst cwX) (suc (suc n)))
-- --     CON = subst (isConnected 2) (ua (invEquiv (e2 n X cwX)))
-- --             (isConnectedSubtr' n 2 isConnectedSphereBouquet')

-- --     EX : ∃[ x ∈ fst (fst cwX) (suc (suc n)) ]
-- --           (((a : Fin (fst (fst (snd (fst cwX))) (suc (suc n))))
-- --          → x ≡ fst (snd (fst (snd (fst cwX)))) (suc (suc n))
-- --                  (a , ptSn (suc n)))
-- --          × (fst (e2 n X cwX) x ≡ inl tt))
-- --     EX = TR.rec (isProp→isSet squash₁)
-- --       (λ x₀ → TR.rec squash₁
-- --         (λ pts → TR.rec squash₁ (λ F → ∣ x₀ , F , pts ∣₁)
-- --           (invEq (_ , InductiveFinSatAC 1 (fst (fst (snd (fst cwX))) (suc (suc n))) _)
-- --                 λ a → isConnectedPath 1 CON _ _ .fst))
-- --         (isConnectedPath 1 (isConnectedSubtr' n 2 isConnectedSphereBouquet')
-- --           (fst (e2 n X cwX) x₀) (inl tt) .fst))
-- --       (fst CON)

-- --     module _ (x : fst (fst cwX) (suc (suc n)))
-- --              (pts : (a : Fin (fst (fst (snd (fst cwX))) (suc (suc n))))
-- --                   → x ≡ fst (snd (fst (snd (fst cwX)))) (suc (suc n)) (a , ptSn (suc n)))
-- --              (ptd : fst (e2 n X cwX) x ≡ inl tt) where
-- --       F' : SphereBouquet (suc n) (Fin (fst (fst (snd (fst cwX))) (suc (suc n))))
-- --         → fst (fst cwX) (suc (suc n))
-- --       F' (inl tt) = x
-- --       F' (inr x) = fst (snd (fst (snd (fst cwX)))) (suc (suc n)) x
-- --       F' (push a i) = pts a i

-- --       F : SphereBouquet∙ (suc n) (Fin (fst (fst (snd (fst cwX))) (suc (suc n))))
-- --        →∙ SphereBouquet∙ (suc n) (Fin (fst (fst (snd (fst cwX))) (suc n)))
-- --       fst F = fst (e2 n X cwX) ∘ F'
-- --       snd F = ptd

-- --       e3' : Iso (fst (fst cwX) (suc (suc (suc n)))) (cofib (fst F))
-- --       e3' =
-- --         compIso (equivToIso (compEquiv
-- --           (snd (snd (snd (fst (snd (fst cwX))))) (suc (suc n)))
-- --           (pushoutEquiv _ _ _ _ (idEquiv _) (e2 n X cwX) (idEquiv _)
-- --             (λ i x → fst F (inr x))
-- --             (λ i x → fst x))))
-- --         (⋁-cofib-Iso (SphereBouquet∙ (suc n)
-- --                        (Fin (fst (fst (snd (fst cwX))) (suc n)))) F)

-- --   module _ (X : Type) (cw : isCW X) (cw' : isConnectedCW n X)
-- --            (isc : isConnected (suc (suc n)) X) (x : X) where
-- --     E : isEquiv (HurewiczHomAb (X , ∣ cw ∣₁) x (isConnectedSubtr' n 2 isc) n .fst)
-- --     E = isEqTransport (X , ∣ (fst cw' .fst , fst cw' .snd .fst)
-- --                       , invEquiv (snd cw') ∣₁)
-- --                       (X , ∣ cw ∣₁)
-- --           (Σ≡Prop (λ _ → squash₁) refl)
-- --           (isConnectedSubtr' n 2 isc)
-- --           (isConnectedSubtr' n 2 isc) x x refl
-- --           (PreHurewiczLemma n (X , (fst cw' .fst , fst cw' .snd .fst) , invEquiv (snd cw'))
-- --             (isConnectedSubtr' n 2 isc)
-- --             (λ l str con' → PT.rec (isPropIsEquiv _)
-- --               (λ {(α , e) → isEqTransport _ (fst cw' .fst (suc (suc (suc n))) , str) (sym e)
-- --                               (subst (isConnected 2) (cong fst e) con')
-- --                               con'
-- --                               (transport (cong fst e) l)
-- --                               l
-- --                               (symP (toPathP refl))
-- --                               {!!}
-- --               {- isEqTransport _ (fst cw' .fst (suc (suc (suc n))) , str) (sym e)
-- --                               {!!}
-- --                               {!!}
-- --                               ?
-- --                               l
-- --                               {!!}
-- --                               {!!}
-- --                               -}
-- --                               })
-- --                 (e3 n X cw' str)) x)

-- --   module _ (X : Type) (cwX : isConnectedCW n X) where

-- -- -- HurewiczMainLemma : (n : ℕ) (X : ConnectedCW ℓ-zero (suc n))
-- -- --   → ((x : fst (fst (snd X)) (suc (suc (suc n))))
-- -- --     → isInducedAbelianisationGroupEquiv
-- -- --          (π'Gr n ((fst (fst (snd X)) (suc (suc (suc n)))) , x))
-- -- --          (Hᶜʷ (subCW (suc (suc (suc n))) (ConnectedCW→CWexplicit X)) n)
-- -- --          (Hᶜʷ-comm (subCW (suc (suc (suc n))) (ConnectedCW→CWexplicit X)))
-- -- --          (HurewiczMap (subCW (suc (suc (suc n))) (ConnectedCW→CWexplicit X)) x))
-- -- --   → (x : fst X)
-- -- --   → isInducedAbelianisationGroupEquiv
-- -- --       (π'Gr n (fst X , x)) (Hᶜʷ (ConnectedCW→CW X) n)
-- -- --         (Hᶜʷ-comm (ConnectedCW→CW X)) (HurewiczMap (ConnectedCW→CW X) x)
-- -- -- HurewiczMainLemma n (X , (Xfam , Xsk , t) , sk) indhyp x = {!Xsk!} , {!!}
-- -- --   where
-- -- --   mainEquiv : GroupEquiv (Hᶜʷ (X , ∣ (Xfam , Xsk) , invEquiv sk ∣₁) n)
-- -- --                          (AbGroup→Group (AbelianizationAbGroup (π'Gr n (X , x))))
                         
-- -- --   mainEquiv = {!!}
  
-- -- --   mainEquivCharacInv : invEq (fst mainEquiv) ≡ {!!} -- groupHom→AbelianisationGroupHom {!HurewiczMap (ConnectedCW→CW (X , (Xfam , Xsk , t) , sk)) x!} {!!} .fst -- ? ∘ 
-- -- --   mainEquivCharacInv = {!!}

-- -- -- -- HurewiczLemmas : {n : ℕ} (X : CW ℓ-zero) (x : fst X) (f : S₊∙ (suc n) →∙ (fst X , x))
-- -- -- --   → isInducedAbelianisationGroupEquiv
-- -- -- --       (π'Gr n (fst X , x)) (Hᶜʷ X n) (Hᶜʷ-comm X) (HurewiczMap X x)
-- -- -- -- HurewiczLemmas {n} =
-- -- -- --   uncurry λ X → PT.elim (λ _ →
-- -- -- --                  isPropΠ2 λ _ _ → isPropIsInducedAbelianisationGroupEquiv)
-- -- -- --    (uncurry λ Xsk → EquivJ (λ X y → (x : X) →
-- -- -- --       S₊∙ (suc n) →∙ (X , x)
-- -- -- --       → isInducedAbelianisationGroupEquiv
-- -- -- --           (π'Gr n (X , x)) (Hᶜʷ (X , ∣ Xsk , y ∣₁) n)
-- -- -- --           (Hᶜʷ-comm (X , ∣ Xsk , y ∣₁)) (HurewiczMap (X , ∣ Xsk , y ∣₁) x))
-- -- -- --     λ x f → PT.rec isPropIsInducedAbelianisationGroupEquiv
-- -- -- --             (λ apf → {!snd apf!} , {!!})
-- -- -- --              (CWmap→finCellMap (Sˢᵏᵉˡ (suc n)) Xsk
-- -- -- --              (fst f ∘ invEq (isCWSphere (suc n) .snd)) (2 +ℕ n)))
-- -- -- --   where
-- -- -- --   help : {!!}
-- -- -- --   help = {!!}
