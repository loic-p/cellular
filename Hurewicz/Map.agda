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

cellMap→finCellMap : ∀ {ℓ ℓ'} (m : ℕ) {C : CWskel ℓ} {D : CWskel ℓ'} (ϕ : cellMap C D) → finCellMap m C D
FinSequenceMap.fmap (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.map ϕ x
FinSequenceMap.fcomm (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.comm ϕ x

subComplex→ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → cellMap (subComplex C n) C
SequenceMap.map (subComplex→ C n) m with (m ≟ᵗ n)
... | lt x = idfun (fst C m)
... | eq x = idfun (fst C m)
... | gt x = CW↑ C _ _ x
SequenceMap.comm (subComplex→ C n) m with (m ≟ᵗ n) | (suc m ≟ᵗ n)
... | lt x | lt x₁ = λ _ → refl
... | lt x | eq x₁ = λ _ → refl
... | lt x | gt x₁ = ⊥.rec (¬squeeze (x , x₁))
... | eq x | lt x₁ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x (<ᵗ-trans <ᵗsucm x₁)))
... | eq x | eq x₁ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ_ m) (x₁ ∙ (λ i → x (~ i))) <ᵗsucm))
... | eq x | gt x₁ = help m n x x₁
  where
  diff<ᵗsucm : (m : ℕ) (x₁ : m <ᵗ suc m) → diff<ᵗ x₁ ≡ (1 , refl)
  diff<ᵗsucm m t = Σ≡Prop (λ _ → isSetℕ _ _) (inj-+m (diff<ᵗ t .snd))

  help : (m n : ℕ) (p : m ≡ n) (x₁ : n <ᵗ suc m)
      (x₂ : fst C m) →
      snd (snd (snd (snd (snd C))) m) .equiv-proof
      (inl (idfun (fst C m) x₂)) .fst .fst
      ≡
      CW↑ C n (suc m) x₁
      (invEq (pathToEquiv (λ i → fst C (p (~ i))))
       x₂)
  help m = J> λ t → λ x
    → sym (transportRefl _)
    ∙ (λ j → transport (λ i → fst C (diff<ᵗsucm m t (~ j) .snd i))
      (CW↪Iterate C m (diff<ᵗsucm m t (~ j) .fst) x))
    ∙ cong (CW↑ C m (suc m) t)
      λ i → transp (λ i → fst C m) (~ i) (transp (λ i → fst C m) (~ i) x)
... | gt x | lt x₁ = ⊥.rec (¬squeeze (x₁ , <ᵗ-trans x (<ᵗ-trans <ᵗsucm <ᵗsucm)))
... | gt x | eq x₁ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ_ n) x₁ (<ᵗ-trans x <ᵗsucm)))
... | gt x | gt x₁ = λ x
  → cong (invEq (snd (snd (snd (snd C))) m) ∘ inl)
          (λ _ → subst (fst C) (snd D1)
                   (CW↪Iterate C n (D1 .fst) x))
   ∙ sym (substCommSlice (fst C) (fst C ∘ suc) (CW↪ C)
         (snd D1) _)
   ∙ λ i → (subst (fst C) (snd (BAH (~ i)))
             ∘ CW↪Iterate C n (BAH (~ i) .fst)) x
  where
  D1 = diff<ᵗ x
  D2 = diff<ᵗ x₁

  BAH : D2 ≡ (suc (fst D1) , cong suc (snd D1))
  BAH = Σ≡Prop (λ _ → isSetℕ _ _)
          (cong suc (inj-+m {n = suc (fst (<ᵗ→< x))}
            (snd  (<ᵗ→< x₁) ∙ cong suc (sym (snd (<ᵗ→< x))))))

finCellApproxSubComplex→ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  → finCellApprox (subComplex C n) C {!!} {!!} -- 
finCellApproxSubComplex→ = {!!}

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
    → SequenceMap.map (subComplex→ C n) (fst m) (finCellMapSubComplexMap C n m x) ≡ x
finCellMapSubComplexMapComp C n m x with (fst m ≟ᵗ n)
... | lt x₁ = refl
... | eq x₁ = refl
... | gt x₁ = ⊥.rec (¬squeeze (snd m , x₁))

finCellMapSubComplexMapComm : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  (x : Fin n) (a : fst C (fst x)) →
      Square
      ((SequenceMap.comm (subComplex→ C n) (fst x))
       (finCellMapSubComplexMap C n (injectSuc x) a)
       ∙
       (λ i →
          (SequenceMap.map (subComplex→ C n) (suc (fst x)))
          (finCellMapSubComplexComm C n x a i)))
      refl
      (cong (λ x₁ → CW↪ C (fst x) x₁)
       (finCellMapSubComplexMapComp C n (injectSuc x) a))
      (finCellMapSubComplexMapComp C n (fsuc x) (CW↪ C (fst x) a))
finCellMapSubComplexMapComm C n x a with (fst x ≟ᵗ n) | (suc (fst x) ≟ᵗ n)
... | lt x₁ | lt x₂ = sym (rUnit _)
... | lt x₁ | eq x₂ = sym (rUnit _)
... | lt x₁ | gt x₂ = ⊥.rec (¬squeeze (snd (fsuc x) , x₂))
... | eq x₁ | lt x₂ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) x₁ (<ᵗ-trans <ᵗsucm x₂))) 
... | eq x₁ | eq x₂ = ⊥.rec
          (¬m<ᵗm (subst (_<ᵗ_ (fst x)) (x₂ ∙ (λ i₁ → x₁ (~ i₁))) <ᵗsucm))
... | eq x₁ | gt x₂ = ⊥.rec (¬squeeze (snd (fsuc x) , x₂))
... | gt x₁ | q = ⊥.rec (¬squeeze (snd (injectSuc x) , x₁))

finCellMapSubComplexComp : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  → composeFinCellMap n (cellMap→finCellMap n (subComplex→ C n)) (finCellMapSubComplex C n)
   ≡ idFinCellMap n _
finCellMapSubComplexComp C n =
  FinSequenceMapId (finCellMapSubComplexMapComp C n)
                   (finCellMapSubComplexMapComm C n)

finCellMapSubComplexComp' : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  → composeFinCellMap n (finCellMapSubComplex C n) (cellMap→finCellMap n (subComplex→ C n))
   ≡ idFinCellMap n _
finCellMapSubComplexComp' C n =
  FinSequenceMapId (finCellMapSubComplexMapComp' C n)
                   (finCellMapSubComplexMapCoh' C n)
  where
  finCellMapSubComplexMapComp' : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
    → (m : Fin (suc n)) (x : _)
      → finCellMapSubComplexMap C n m (SequenceMap.map (subComplex→ C n) (fst m) x) ≡ x
  finCellMapSubComplexMapComp' C n m x with (fst m ≟ᵗ n)
  ... | lt x₁ = refl
  ... | eq x₁ = refl
  ... | gt x₁ = ⊥.rec (¬squeeze (snd m , x₁))

  finCellMapSubComplexMapCoh' : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (x : Fin n) (a : subComplexFam C n (fst x)) →
      Square
      (finCellMapSubComplexComm C n x
       ((SequenceMap.map (subComplex→ C n) (fst x)) a)
       ∙
       (λ i →
          finCellMapSubComplexMap C n (fsuc x)
          ((SequenceMap.comm (subComplex→ C n) (fst x))
           a i)))
      refl
      (cong (λ x₁ → CW↪ (subComplex C n) (fst x) x₁)
       (finCellMapSubComplexMapComp' C n (injectSuc x) a))
      (finCellMapSubComplexMapComp' C n (fsuc x)
       (CW↪ (subComplex C n) (fst x) a))
  finCellMapSubComplexMapCoh' C n x a with (fst x ≟ᵗ n) | (suc (fst x) ≟ᵗ n)
  ... | lt x₁ | lt x₂ = sym (rUnit _)
  ... | lt x₁ | eq x₂ = sym (rUnit _)
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
      (subComplex→ C (suc (suc (suc n))))) .fst
Iso.inv (fst (subComplex→GrIso C n)) = finCellMap→HomologyMap n (finCellMapSubComplex C (suc (suc (suc n)))) .fst
Iso.rightInv (fst (subComplex→GrIso C n)) =
  funExt⁻ (cong fst (sym (finCellMap→HomologyMapComp n
             (cellMap→finCellMap (suc (suc (suc n)))
               (subComplex→ C (suc (suc (suc n)))))
             (finCellMapSubComplex C (suc (suc (suc n)))))
           ∙ cong (finCellMap→HomologyMap n) (finCellMapSubComplexComp C (suc (suc (suc n))))
           ∙ finCellMap→HomologyMapId n))
Iso.leftInv (fst (subComplex→GrIso C n)) =
  funExt⁻ (cong fst (sym (finCellMap→HomologyMapComp n
             (finCellMapSubComplex C (suc (suc (suc n))))
             (cellMap→finCellMap (suc (suc (suc n)))
               (subComplex→ C (suc (suc (suc n))))))
           ∙ cong (finCellMap→HomologyMap n) (finCellMapSubComplexComp' C (suc (suc (suc n))))
           ∙ finCellMap→HomologyMapId n))
snd (subComplex→GrIso C n) =
  finCellMap→HomologyMap n
    (cellMap→finCellMap (suc (suc (suc n)))
      (subComplex→ C (suc (suc (suc n))))) .snd
-- (cong fst (sym (finCellMap→HomologyMapComp n g⁻ g)) ∙ {!!})) {!!}) -- 
  where
  g⁻ : finCellMap (suc (suc (suc n))) (subComplex C (suc (suc (suc n)))) C
  g⁻ = (cellMap→finCellMap (suc (suc (suc n))) (subComplex→ C (suc (suc (suc n)))))

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

realiseSubComplexEq : ∀ {ℓ} (n : ℕ) (C : CWskel ℓ) (x : _)
  → Iso.fun (realiseSubComplex n C) x ≡ incl {n = n} {!!}
realiseSubComplexEq = {!!}



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

realiseSubComplexFun← : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → realise (subComplex C n) → fst C n
realiseSubComplexFun← C n (incl {n = m} x) = {!!} -- invEq (_ , isEqrealiseSubComplexPre C n) {!x!}
realiseSubComplexFun← C n (push x i) = {!!}



 
isEqrealiseSubComplex : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → isEquiv (realiseSubComplexFun C n)
isEqrealiseSubComplex C n = isoToIsEquiv {!!}


finCellApproxRealiseCellMap : ∀ {ℓ ℓ'} {C : CWskel ℓ} {D : CWskel ℓ'}
  (f : cellMap C D) (n : ℕ) → finCellApprox C D (realiseCellMap f) n
fst (finCellApproxRealiseCellMap f n) = cellMap→finCellMap n f
snd (finCellApproxRealiseCellMap f n) = →FinSeqColimHomotopy _ _ λ _ → refl

funCharac? : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ)
  → (CW↪∞ C n ∘ invEq (isoToEquiv (realiseSubComplex n C)))
   ≡ realiseCellMap (subComplex→ C n)
funCharac? C n = funExt λ x
  → better (Iso.inv (realiseSubComplex n C) x)
   ∙ cong (realiseCellMap (subComplex→ C n))
       (Iso.rightInv (realiseSubComplex n C) x)
  where
  lem : (n : ℕ) (x : _)
    → x ≡ SequenceMap.map (subComplex→ C n) n
            (complex≃subcomplex C n flast .fst x)
  lem n x with (n ≟ᵗ n)
  ... | lt x₁ = refl
  ... | eq x₁ = refl
  ... | gt x₁ = ⊥.rec (¬squeeze (x₁ , <ᵗsucm))

  better : (x : _) → CW↪∞ C n x
    ≡ realiseCellMap (subComplex→ C n)
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
  fst (T n) = finCellApproxRealiseCellMap (subComplex→ C n) n .fst
  snd (T n) = finCellApproxRealiseCellMap (subComplex→ C n) n .snd
            ∙ funExt λ x → funExt⁻ (sym (funCharac? C n)) (FinSeqColim→Colim n x)

  ww = SeqColim
  main : isEquiv (fst (Hᶜʷ→ {C = fst C (suc (suc (suc n))) , _} n (CW↪∞ C (suc (suc (suc n))))))
  main = subst isEquiv (cong fst (sym (Hˢᵏᵉˡ→β _ _ n (T (suc (suc (suc n)))))))
               (isoToIsEquiv (fst (subComplex→GrIso C n)))



∃HomologyEquivalentSubComplex : ∀ {ℓ} (C : CW ℓ) (n : ℕ)
  → ∃[ C' ∈ CW ℓ ] Σ[ ι ∈ (fst C' → fst C) ] isEquiv (Hᶜʷ→ {C = C'} {D = C} n ι .fst)
∃HomologyEquivalentSubComplex = uncurry λ C → PT.elim (λ _ → isPropΠ λ _ → squash₁)
  λ C n → ∣ ((fst (fst C) (suc (suc n)))
          , {!C -- subComplex!})
          , {!subComplex !} ∣₁
  where
  main : {!!}
  main = {!!}


module _ (Sskel : (n : ℕ) → CWskel ℓ-zero)
         (S∞ : (n : ℕ) → S₊ n ≃ realise (Sskel n))
         where
  Sᶜʷ : (n : ℕ) → CW ℓ-zero
  fst (Sᶜʷ n) = S₊ n
  snd (Sᶜʷ n) = ∣ (Sskel n) , S∞ n ∣₁

  preHurewiczMap : ∀ {ℓ} {n : ℕ} (X : CW ℓ) (x : fst X) (f : S₊∙ n →∙ (fst X , x))
    → GroupHom (Hᶜʷ (Sᶜʷ n) n) (Hᶜʷ X n)
  preHurewiczMap {n = n} X x f = Hᶜʷ→ {C = Sᶜʷ n} {D = X} n (fst f)

  HurewiczMap : ∀ {ℓ} {n : ℕ} (X : CW ℓ) (x : fst X)
    → π' n (fst X , x)
    → GroupHom (Hᶜʷ (Sᶜʷ n) n) (Hᶜʷ X n)
  HurewiczMap X x = ST.rec isSetGroupHom (preHurewiczMap X x)

  HurewiczMapAb : {!!}
  HurewiczMapAb = {!!}
