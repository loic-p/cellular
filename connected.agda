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
open import Cubical.Data.Sequence


open import Cubical.CW.Map
open import Cubical.CW.Base
open import Cubical.CW.Properties
open import Cubical.Foundations.GroupoidLaws


open import Cubical.CW.Homotopy
open import Cubical.CW.ChainComplex
open import Cubical.CW.Approximation

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


open import Cubical.Foundations.Transport

open import Cubical.CW.Map
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.SequentialColimit

open import Cubical.Algebra.Group.GroupPath

module connected where

open import Cubical.Data.Sum hiding (map)

¬+<ᵗ : ∀ {n m : ℕ} → ¬ ((m +ℕ n) <ᵗ n)
¬+<ᵗ {n = suc n} {m = m} = subst ¬_ (sym (cong (_<ᵗ suc n) (+-suc m n)))
                                    (¬+<ᵗ {n = n} {m})


Iso-SeqColim→SeqColimSuc : ∀ {ℓ} (X : Sequence ℓ) → Iso (SeqColim X) (SeqColim (ShiftSeq X))
Iso-SeqColim→SeqColimSuc X = iso G F F→G→F G→F→G
  where
  open Sequence
  F : SeqColim (ShiftSeq X) → SeqColim X
  F (incl {n = n} x) = incl {n = suc n} x
  F (push {n = n} x i) = push {n = suc n} x i

  G : SeqColim X → SeqColim (ShiftSeq X)
  G (incl {n = zero} x) = incl {n = zero} (map X x)
  G (incl {n = suc n} x) = incl {n = n} x
  G (push {n = zero} x i) = incl {n = zero} (map X x)
  G (push {n = suc n} x i) = push {n = n} x i

  F→G→F : (x : SeqColim (ShiftSeq X)) → G (F x) ≡ x
  F→G→F (incl x) = refl
  F→G→F (push x i) = refl

  G→F→G : (x : SeqColim X) → F (G x) ≡ x
  G→F→G (incl {n = zero} x) = sym (push {n = zero} x)
  G→F→G (incl {n = suc n} x) = refl
  G→F→G (push {n = zero} x i) j = push {n = zero} x (i ∨ ~ j)
  G→F→G (push {n = suc n} x i) = refl

ShiftSequenceIt : ∀ {ℓ} (S : Sequence ℓ) (n : ℕ) → Sequence ℓ
ShiftSequenceIt S zero = S
ShiftSequenceIt S (suc n) = ShiftSeq (ShiftSequenceIt S n)

ShiftSequenceExpl : ∀ {ℓ} (S : Sequence ℓ) (n : ℕ) → Sequence ℓ
Sequence.obj (ShiftSequenceExpl S n) m = Sequence.obj S (m +ℕ n)
Sequence.map (ShiftSequenceExpl S n) {n = m} = Sequence.map S

Iso-SeqColim→SeqColimShift : ∀ {ℓ} (S : Sequence ℓ) (n : ℕ)
  → Iso (SeqColim S) (SeqColim (ShiftSequenceIt S n))
Iso-SeqColim→SeqColimShift S zero = idIso
Iso-SeqColim→SeqColimShift S (suc n) =
  compIso (Iso-SeqColim→SeqColimShift S n) (Iso-SeqColim→SeqColimSuc _)

-----

_≤ᵗ_ : (n m : ℕ) → Type
n ≤ᵗ m = (n <ᵗ m) ⊎ (n ≡ m)

Dicotomyᵗ : (n m : ℕ) → Type
Dicotomyᵗ n m = (n ≤ᵗ m) ⊎ (m <ᵗ n)

_≟ᵗd_ : (n m : ℕ) → Dicotomyᵗ n m
n ≟ᵗd m with (n ≟ᵗ m)
... | lt x = inl (inl x)
... | eq x = inl (inr x)
... | gt x = inr x

isProp≤ᵗ : {n m : ℕ} → isProp (n ≤ᵗ m)
isProp≤ᵗ (inl x) (inl x₁) i = inl (isProp<ᵗ x x₁ i)
isProp≤ᵗ {m = m} (inl x) (inr x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) x₁ x))
isProp≤ᵗ {m = m} (inr x) (inl x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) x x₁))
isProp≤ᵗ (inr x) (inr x₁) i = inr (isSetℕ _ _ x x₁ i)

-- isPropDichomotmyᵗ : (n m : ℕ) → isProp (Dicotomyᵗ n m)
-- isPropDichomotmyᵗ n m (inl x) (inl x₁) i = inl {!isProp<ᵗ !}
-- isPropDichomotmyᵗ n m (inl x) (inr x₁) = {!!}
-- isPropDichomotmyᵗ n m (inr x) (inl x₁) = {!!}
-- isPropDichomotmyᵗ n m (inr x) (inr x₁) = {!!}

open import Cubical.Data.Unit
open import Cubical.Data.Fin as diffFin
open import Cubical.Data.Nat.Order as diffOrder

SequenceMapIterate : ∀ {ℓ} (A : Sequence ℓ) → (n m : ℕ) → Sequence.obj A n → Sequence.obj A (m +ℕ n) 
SequenceMapIterate A n zero x = x
SequenceMapIterate A n (suc m) = Sequence.map A ∘ SequenceMapIterate A n m

suc-≤ᵗ-suc : {n m : ℕ} → n ≤ᵗ m → suc n ≤ᵗ suc m
suc-≤ᵗ-suc (inl x) = inl x
suc-≤ᵗ-suc (inr x) = inr (cong suc x)

pred-≤ᵗ-pred : {n m : ℕ} → suc n ≤ᵗ suc m → n ≤ᵗ m
pred-≤ᵗ-pred (inl x) = inl x
pred-≤ᵗ-pred (inr x) = inr (cong predℕ x)

<→≤ : {n m : ℕ} → n <ᵗ suc m → n ≤ᵗ m
<→≤ {n = zero} {m = zero} _ = inr refl
<→≤ {n = zero} {m = suc m} _ = inl tt
<→≤ {n = suc n} {m = suc m} = suc-≤ᵗ-suc ∘ <→≤ {n = n} {m = m}

SequenceMapIterate' : ∀ {ℓ} (A : Sequence ℓ) → (n m : ℕ) → n ≤ᵗ m →  Sequence.obj A n → Sequence.obj A m
SequenceMapIterate' A n (suc m) (inl x) = Sequence.map A ∘ SequenceMapIterate' A n m (<→≤ x)
SequenceMapIterate' A n m (inr x) = subst (Sequence.obj A) x

SequenceMapIterate'≡ : ∀ {ℓ} (A : Sequence ℓ) (n m : ℕ) (s : _) (a :  Sequence.obj A n)
  → SequenceMapIterate A n m a ≡ SequenceMapIterate' A n (m +ℕ n) s a
SequenceMapIterate'≡ A n zero (inl x₁) = ⊥.rec (¬m<ᵗm x₁)
SequenceMapIterate'≡ A zero (suc x) (inl tt) a =
  cong (Sequence.map A) (SequenceMapIterate'≡ A zero x (<→≤ tt) a)
SequenceMapIterate'≡ A (suc n) (suc x) (inl x₁) a =
  cong (Sequence.map A) (SequenceMapIterate'≡ A (suc n) x (<→≤ x₁) a)
SequenceMapIterate'≡ A zero zero (inr x₁) a =
  sym (transportRefl a) ∙ λ j → subst (Sequence.obj A) (isSetℕ _ _ refl x₁ j) a
SequenceMapIterate'≡ A (suc n) zero (inr x₁) a =
  sym (transportRefl a) ∙ λ j → subst (Sequence.obj A) (isSetℕ _ _ refl x₁ j) a
SequenceMapIterate'≡ A n (suc x) (inr x₁) = ⊥.rec (¬m<m (x , +-suc x n ∙ sym x₁))

  
cofib→ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  {f : A → B} (h : B → C)
  → cofib f → cofib (h ∘ f)
cofib→ h (inl x) = inl x
cofib→ h (inr x) = inr (h x)
cofib→ h (push a i) = push a i


SequenceIso : ∀ {ℓ ℓ'} (A : Sequence ℓ) (B : Sequence ℓ') → Type (ℓ-max ℓ ℓ')
SequenceIso A B =
  Σ[ is ∈ ((n : ℕ) → Iso (Sequence.obj A n) (Sequence.obj B n)) ]
     ((n : ℕ) (a : Sequence.obj A n)
       → Sequence.map B (Iso.fun (is n) a) ≡ Iso.fun (is (suc n)) (Sequence.map A a))

compSequenceIso : ∀ {ℓ ℓ' ℓ''} {A : Sequence ℓ} {B : Sequence ℓ'} {C : Sequence ℓ''}
  → SequenceIso A B → SequenceIso B C → SequenceIso A C
fst (compSequenceIso e g) n = compIso (fst e n) (fst g n)
snd (compSequenceIso e g) n a = snd g n _ ∙ cong (Iso.fun (fst g (suc n))) (snd e n a)

SequenceEquiv : ∀ {ℓ ℓ'} (A : Sequence ℓ) (B : Sequence ℓ') → Type (ℓ-max ℓ ℓ')
SequenceEquiv A B =
  Σ[ e ∈ (SequenceMap A B) ]
     ((n : ℕ) → isEquiv (SequenceMap.map e n))

invSequenceEquiv : ∀ {ℓ ℓ'} {A : Sequence ℓ} {B : Sequence ℓ'} → SequenceEquiv A B → SequenceEquiv B A
SequenceMap.map (fst (invSequenceEquiv eqs)) n = invEq (_ , snd eqs n)
SequenceMap.comm (fst (invSequenceEquiv {A = A} {B} eqs)) n x =
    sym (retEq (_ , snd eqs (suc n)) (Sequence.map A (invEq (_  , snd eqs n) x)))
  ∙∙ cong (invEq (_ , snd eqs (suc n))) (sym (SequenceMap.comm (fst eqs) n (invEq (_ , snd eqs n) x)))
  ∙∙ cong (invEq (_ , snd eqs (suc n)) ∘ Sequence.map B) (secEq (_ , snd eqs n) x)
snd (invSequenceEquiv eqs) n = invEquiv (_ , snd eqs n) .snd


SequenceIso→SequenceEquiv : ∀ {ℓ ℓ'} {A : Sequence ℓ} {B : Sequence ℓ'}
  → SequenceIso A B → SequenceEquiv A B
SequenceMap.map (fst (SequenceIso→SequenceEquiv (is , e))) = Iso.fun ∘ is
SequenceMap.comm (fst (SequenceIso→SequenceEquiv (is , e))) = e
snd (SequenceIso→SequenceEquiv (is , e)) n = isoToIsEquiv (is n)

idSequenceEquiv : ∀ {ℓ} → (A : Sequence ℓ) → SequenceEquiv A A
fst (idSequenceEquiv A) = idSequenceMap A
snd (idSequenceEquiv A) _ = idIsEquiv _

invIdSequenceEquiv : ∀ {ℓ} {A : Sequence ℓ}
  → invSequenceEquiv (idSequenceEquiv A) ≡ idSequenceEquiv A
invIdSequenceEquiv {A = A} =
  Σ≡Prop (λ _ → isPropΠ (λ _ → isPropIsEquiv _)) main
  where
  main : invSequenceEquiv (idSequenceEquiv A) .fst ≡ idSequenceMap A
  SequenceMap.map (main i) n z = z
  SequenceMap.comm (main i) n x j = rUnit (λ _ → Sequence.map A x) (~ i) j

uaSequence : ∀ {ℓ} {A B : Sequence ℓ} → SequenceEquiv A B → A ≡ B
Sequence.obj (uaSequence {A = A} {B} (e , eqv) i) n = ua (_ , eqv n) i
Sequence.map (uaSequence {A = A} {B} (e , eqv) i) {n = n} a =
  hcomp (λ k → λ {(i = i0) → Sequence.map A (retEq (_ , eqv n) a k)
                 ; (i = i1) → (sym (SequenceMap.comm e n (invEq (_ , eqv n) a))
                              ∙ cong (Sequence.map B) (secEq (_ , eqv n) a)) k})
        (ua-gluePt (_ , eqv (suc n)) i
          (Sequence.map A (invEq (_ , eqv n) (ua-unglue (_ , eqv n) i a))))


uaSequenceIdEquiv : ∀ {ℓ} {A : Sequence ℓ}
  → uaSequence (idSequenceEquiv A) ≡ refl
Sequence.obj (uaSequenceIdEquiv {A = A} i j) n = uaIdEquiv {A = Sequence.obj A n} i j
Sequence.map (uaSequenceIdEquiv {A = A} i j) {n = n} x =
  hcomp (λ k → λ {(i = i1) → Sequence.map A x
                 ; (j = i0) → Sequence.map A x
                 ; (j = i1) → rUnit (refl {x = Sequence.map A x}) (~ i) k})
   (glue {φ = j ∨ ~ j ∨ i}
      (λ { (j = i0) → Sequence.map A x
         ; (j = i1) → Sequence.map A x
         ; (i = i1) → Sequence.map A x})
      ((Sequence.map A
          (unglue (j ∨ ~ j ∨ i) x))))

open import Cubical.Foundations.Equiv.HalfAdjoint

halfAdjointSequenceEquiv : ∀ {ℓ ℓ'} {A : Sequence ℓ} {B : Sequence ℓ'} → SequenceEquiv A B → SequenceEquiv A B
fst (halfAdjointSequenceEquiv (e , eqv)) = e
snd (halfAdjointSequenceEquiv (e , eqv)) n = isHAEquiv→isEquiv (equiv→HAEquiv (_ , eqv n) .snd)

isContrTotalSequence : ∀ {ℓ} (A : Sequence ℓ)
  → isContr (Σ[ B ∈ Sequence ℓ ] SequenceEquiv A B)
fst (isContrTotalSequence A) = A , idSequenceEquiv A
snd (isContrTotalSequence A) (B , eqv*) =
  ΣPathP (uaSequence eqv , main)
  where
  eqv = halfAdjointSequenceEquiv eqv*

  open import Cubical.Foundations.Path


  help : (n : ℕ) (x : Sequence.obj A n)
    → Square (cong (SequenceMap.map (fst eqv) (suc n) ∘ Sequence.map A)
                    (retEq (_ , snd eqv n) x))
              (SequenceMap.comm (fst eqv) n x)
              (sym (SequenceMap.comm (fst eqv) n (invEq (_ , snd eqv n) (SequenceMap.map (fst eqv) n x)))
              ∙ λ i₁ → Sequence.map B (secEq (SequenceMap.map (fst eqv) n , snd eqv n)
                         (SequenceMap.map (fst eqv) n x) i₁))
              λ _ → SequenceMap.map (fst eqv) (suc n) (Sequence.map A x)
  help n x = flipSquare ((compPath≡compPath' _ _
    ∙ cong₂ _∙'_ refl λ j i → Sequence.map B (isHAEquiv.com (equiv→HAEquiv (_ , eqv* .snd n) .snd) x (~ j) i))
    ◁ λ i j → 
    hcomp (λ k → λ {(j = i0) → SequenceMap.comm (fst eqv) n
                                  (lUnit ((cong fst (eqv* .snd n .equiv-proof (SequenceMap.map (fst eqv*) n x)
                                   .snd (x , (λ _ → SequenceMap.map (fst eqv*) n x))))) k i) k
                   ; (j = i1) → SequenceMap.comm (fst eqv) n x (i ∧ k)
                   ; (i = i0) → compPath'-filler (sym (SequenceMap.comm (fst eqv) n (invEq (_ , snd eqv n) (SequenceMap.map (fst eqv) n x))))
                                                  (cong (Sequence.map B) (isHAEquiv.com (equiv→HAEquiv (_ , eqv* .snd n) .snd) x i0)) k j
                   ; (i = i1) → SequenceMap.comm (fst eqv) n x k
                   })
          (Sequence.map B (SequenceMap.map (fst eqv*) n
            ((cong fst (eqv* .snd n .equiv-proof (SequenceMap.map (fst eqv*) n x)
              .snd (x , (λ _ → SequenceMap.map (fst eqv*) n x)))) (i ∨ j)))))

  main : PathP (λ i → SequenceEquiv A (uaSequence eqv i))
      (idSequenceEquiv A) eqv*
  SequenceMap.map (fst (main i)) n x = ua-gluePt (_ , snd eqv n) i x
  SequenceMap.comm (fst (main i)) n x j =
    hcomp (λ k → λ {(i = i0) → Sequence.map A
                                  (retEq (_ , snd eqv n) x (k ∨ j))
                   ; (i = i1) → help n x k j
                   ; (j = i1) → ua-gluePt (_ , snd eqv (suc n)) i (Sequence.map A x)})
          (ua-gluePt (_ , snd eqv (suc n)) i
                     (Sequence.map A (retEq (_ , snd eqv n) x j)))
  snd (main i) n =
    isProp→PathP {B = λ i → isEquiv  (λ x → ua-gluePt (_ , snd eqv n) i x)}
     (λ i → isPropIsEquiv _)
     (idIsEquiv (Sequence.obj A n)) (snd eqv* n) i



SequenceEquivJ : ∀ {ℓ ℓ'} {A : Sequence ℓ}
  (P : (B : Sequence ℓ) → SequenceEquiv A B → Type ℓ')
  → P A (idSequenceEquiv A)
  → (B : _) (e : _) → P B e
SequenceEquivJ {ℓ = ℓ} {A = A} P ind B e = main (B , e)
  where
  P' : Σ[ B ∈ Sequence ℓ ] SequenceEquiv A B → Type _ 
  P' (B , e) = P B e

  main : (x : _) → P' x
  main (B , e) = subst P' (isContrTotalSequence A .snd (B , e)) ind

SequenceEquivJ>_ : ∀ {ℓ ℓ'} {A : Sequence ℓ}
  {P : (B : Sequence ℓ) → SequenceEquiv A B → Type ℓ'}
  → P A (idSequenceEquiv A)
  → (B : _) (e : _) → P B e
SequenceEquivJ>_ {P = P} hyp B e = SequenceEquivJ P hyp B e

open import Cubical.Foundations.Transport

ShiftSequenceIso : ∀ {ℓ} {A : Sequence ℓ} (n : ℕ)
  → SequenceIso (ShiftSequenceIt A n) (ShiftSequenceExpl A n)
fst (ShiftSequenceIso {A = A} zero) m = pathToIso λ i → Sequence.obj A (+-comm zero m i)
fst (ShiftSequenceIso {A = A} (suc n)) m =
  compIso (fst (ShiftSequenceIso {A = A} n) (suc m))
          (pathToIso λ i → Sequence.obj A (+-suc m n (~ i)))
snd (ShiftSequenceIso {A = A} zero) m a =
  sym (substCommSlice (Sequence.obj A) (Sequence.obj A ∘ suc)
                        (λ _ → Sequence.map A)
                        (+-comm zero m) a)
  ∙ λ t → subst (Sequence.obj A)
             (lUnit (cong suc (+-comm zero m)) t)
             (Sequence.map A a) 
snd (ShiftSequenceIso {A = A} (suc n)) m a =
    sym (substCommSlice (Sequence.obj A) (Sequence.obj A ∘ suc)
                        (λ _ → Sequence.map A)
                        (λ i → (+-suc m n (~ i)))
                        (Iso.fun (fst (ShiftSequenceIso n) (suc m)) a))
  ∙ cong (subst (λ x → Sequence.obj A (suc x)) (sym (+-suc m n)))
         (snd (ShiftSequenceIso {A = A} n) (suc m) a)

SequenceEquivJRefl : ∀ {ℓ ℓ'} {A : Sequence ℓ}
  (P : (B : Sequence ℓ) → SequenceEquiv A B → Type ℓ')
    (id : P A (idSequenceEquiv A))
  → SequenceEquivJ P id A (idSequenceEquiv A) ≡ id
SequenceEquivJRefl {ℓ = ℓ} {A = A} P ids =
  (λ j → subst P' (isProp→isSet (isContr→isProp (isContrTotalSequence A))
                    _ _ (isContrTotalSequence A .snd (A , idSequenceEquiv A)) refl j) ids)
  ∙ transportRefl ids
  where
  P' : Σ[ B ∈ Sequence ℓ ] SequenceEquiv A B → Type _ 
  P' (B , e) = P B e

sequenceEquiv→ColimIso : ∀ {ℓ} {A B : Sequence ℓ} → SequenceEquiv A B → Iso (SeqColim A) (SeqColim B)
sequenceEquiv→ColimIso e = mainIso
  where
  main : ∀ {ℓ} {A : Sequence ℓ} (B : Sequence ℓ) (e : SequenceEquiv A B)
    → section (realiseSequenceMap (fst e))
               (realiseSequenceMap (fst (invSequenceEquiv e)))
     × retract (realiseSequenceMap (fst e))
               (realiseSequenceMap (fst (invSequenceEquiv e)))
  main {A = A} = SequenceEquivJ>
    ((λ x → (λ i → realiseIdSequenceMap {C = A} i
                      (realiseSequenceMap (fst (invIdSequenceEquiv {A = A} i)) x))
           ∙ funExt⁻ realiseIdSequenceMap x)
   , λ x → (λ i → realiseSequenceMap (fst (invIdSequenceEquiv {A = A} i))
                      (realiseIdSequenceMap {C = A} i x))
           ∙ funExt⁻ realiseIdSequenceMap x)

  mainIso : Iso _ _
  Iso.fun mainIso = realiseSequenceMap (fst e)
  Iso.inv mainIso = realiseSequenceMap (fst (invSequenceEquiv e))
  Iso.rightInv mainIso = main _ e .fst
  Iso.leftInv mainIso = main _ e .snd


SeqColimIso : ∀ {ℓ} (S : Sequence ℓ) (n : ℕ)
  → Iso (SeqColim S) (SeqColim (ShiftSequenceExpl S n))
SeqColimIso S n =
  compIso (Iso-SeqColim→SeqColimShift S n)
    (sequenceEquiv→ColimIso
      (SequenceIso→SequenceEquiv (ShiftSequenceIso n)))

asdd = Trichotomyᵗ

SequenceMapIterate₀ : ∀ {ℓ} (S : Sequence ℓ) (n : ℕ) → Sequence.obj S 0 → Sequence.obj S n
SequenceMapIterate₀ S zero = idfun _
SequenceMapIterate₀ S (suc n) = Sequence.map S ∘ SequenceMapIterate₀ S n

SeqColim/₀Sequence : ∀ {ℓ} (S : Sequence ℓ) → Sequence ℓ
Sequence.obj (SeqColim/₀Sequence S) n =
  cofib {A = Sequence.obj S 0} {B = Sequence.obj S n} (SequenceMapIterate₀ S n) 
Sequence.map (SeqColim/₀Sequence S) = cofib→ (Sequence.map S)

incl₀ : ∀ {ℓ} {S : Sequence ℓ} → Sequence.obj S 0 → SeqColim S
incl₀ = incl

SeqColim/₀Iso : ∀ {ℓ} {S : Sequence ℓ}
  → Iso (cofib {B = SeqColim S} incl₀)
         (SeqColim (SeqColim/₀Sequence S))
SeqColim/₀Iso {S = S} = iso lr rl sect retr
  where

  pt≡ : (n : ℕ) → Path (SeqColim (SeqColim/₀Sequence S))
                         (incl {n = zero} (inl tt)) (incl {n = n} (inl tt))
  pt≡ zero = refl
  pt≡ (suc n) = pt≡ n ∙ push (inl tt)

  P : (n : ℕ) (a : _) → Path (SeqColim S) (incl {n = zero} a)
                               (incl {n = n} (SequenceMapIterate₀ S n a))
  P zero a = refl
  P (suc n) a = P n a ∙ push (SequenceMapIterate₀ S n a)

  lr : cofib incl → SeqColim (SeqColim/₀Sequence S)
  lr (inl x) = incl {n = zero} (inl x)
  lr (inr (incl {n = n} x)) = incl {n = n} (inr x)
  lr (inr (push x i)) = push (inr x) i
  lr (push a i) = incl {n = zero} (push a i)

  rl : SeqColim (SeqColim/₀Sequence S) → cofib incl₀
  rl (incl {n = n} (inl x)) = inl x
  rl (incl {n = n} (inr x)) = inr (incl {n = n} x)
  rl (incl {n = n} (push a i)) = (push a ∙ (λ i → inr (P n a i))) i
  rl (push {n = n} (inl x) i) = inl x
  rl (push {n = n} (inr x) i) = inr (push x i)
  rl (push {n = n} (push a j) i) =
    (push a
    ∙ λ k → inr (compPath-filler (P n a)
                  (push (SequenceMapIterate₀ S n a)) i k)) j

  pt≡-coh : (a : Sequence.obj S 0) (n : ℕ)
    → Square (pt≡ n) (cong (lr ∘ inr) (P n a))
              (cong incl (push a)) (cong incl (push a))
  pt≡-coh a zero i j = incl {n = zero} (push a i)
  pt≡-coh a (suc n) i j =
    hcomp (λ k → λ {(i = i0) → compPath-filler (pt≡ n) (push (inl tt)) k j
                   ; (i = i1) → lr (inr (compPath-filler (P n a)
                                    (push (SequenceMapIterate₀ S n a)) k j))
                   ; (j = i0) → incl {n = zero} (push a i)
                   ; (j = i1) → push {n = n} (push a i) k})
           (pt≡-coh a n i j)


  sect-help-fill : (a : Sequence.obj S 0) (n : ℕ)
    → I → I → I → SeqColim (SeqColim/₀Sequence S)
  sect-help-fill a n i j k =
    hfill (λ k → λ {(i = i0) → pt≡ n j
                   ; (i = i1) → lr (inr (P n a (k ∨ j)))
                   ; (j = i0) → lr (compPath-filler (push a) (λ i → inr (P n a i)) k i)
                   ; (j = i1) → incl {n = n} (push a i)})
          (inS (pt≡-coh a n i j)) k


  sect-help : (a : Sequence.obj S 0) (n : ℕ) →
    Square (pt≡ n) (λ _ → incl (inr (SequenceMapIterate₀ S n a)))
           (cong lr (push a ∙ (λ i → inr (P n a i))))
           λ i → incl {n = n} (push a i)
  sect-help a n i j = sect-help-fill a n i j i1

  sect : section lr rl
  sect (incl {n = n} (inl x)) = pt≡ n
  sect (incl (inr x)) = refl
  sect (incl {n = n} (push a i)) j = sect-help a n i j
  sect (push {n = n} (inl x) i) = compPath-filler (pt≡ n) (push (inl tt)) i
  sect (push (inr x) i) = refl
  sect (push {n = n} (push a k) i) j =
    hcomp (λ r → λ {(i = i0) → sect-help-fill a n k j r
                   ; (i = i1) → sect-help-fill a (suc n) k j r
                   ; (j = i0) → lr (compPath-filler (push a)
                                      (λ k → inr (compPath-filler (P n a)
                                                (push (SequenceMapIterate₀ S n a)) i k)) r k)
                   ; (j = i1) → push {n = n} (push a k) i
                   ; (k = i0) → compPath-filler (pt≡ n) (push (inl tt)) i j
                   ; (k = i1) → lr (inr (compPath-filler (P n a)
                                         (push (SequenceMapIterate₀ S n a)) i (j ∨ r)))})
      (hcomp (λ r → λ {(i = i0) → pt≡-coh a n k j
                   ; (j = i0) → incl {n = zero} (push a k)
                   ; (j = i1) → push {n = n} (push a k) (i ∧ r)
                   ; (k = i0) → compPath-filler (pt≡ n) (push (inl tt)) (i ∧ r) j
                   ; (k = i1) → lr (inr (compPath-filler (P n a)
                                         (push (SequenceMapIterate₀ S n a)) (i ∧ r) j)) })
             (pt≡-coh a n k j))

  retr : retract lr rl
  retr (inl x) = refl
  retr (inr (incl x)) = refl
  retr (inr (push x i)) = refl
  retr (push a i) j = rUnit (push a) (~ j) i

sequenceIso→ColimIso : ∀ {ℓ} {A B : Sequence ℓ}
  → SequenceIso A B → Iso (SeqColim A) (SeqColim B)
sequenceIso→ColimIso e = sequenceEquiv→ColimIso (SequenceIso→SequenceEquiv e)


module _ {ℓ} (A : Sequence ℓ) where
  open Sequence renaming (map to seqMap)

  cofibSequenceObj : (n m : ℕ) → Type ℓ
  cofibSequenceObj n m with (n ≟ᵗd m)
  ... | inl s = cofib {A = obj A n} {B = obj A m} (SequenceMapIterate' A n m s)
  ... | inr x = Unit*

  cofibSequenceMap : (n m : ℕ) → cofibSequenceObj n m → cofibSequenceObj n (suc m)
  cofibSequenceMap n m with (n ≟ᵗd m) | (n ≟ᵗd suc m)
  ... | inl s | inl (inl x) = cofib→ (seqMap A)
      ∘ subst (cofib ∘ SequenceMapIterate' A n m) (isProp≤ᵗ s (<→≤ x))
  ... | inl s | inl (inr x) = λ _ → inl tt
  ... | inr x | inl q = λ _ → inl tt
  ... | s | inr x = λ _ → tt*

  cofibSequence : (n : ℕ) → Sequence ℓ
  obj (cofibSequence n) = cofibSequenceObj n
  seqMap (cofibSequence n) = cofibSequenceMap n _

  cofibSequenceShifted : (n : ℕ) → Sequence ℓ
  obj (cofibSequenceShifted n) m =
    cofib {A = obj A n} {B = obj A (m +ℕ n)} (SequenceMapIterate A n m)
  seqMap (cofibSequenceShifted n) = cofib→ (seqMap A)

  cofibSequenceShifted' : (n : ℕ) → Sequence ℓ
  cofibSequenceShifted' n = SeqColim/₀Sequence (ShiftSequenceExpl A n)

  cofibSequenceShiftedIso : (n : ℕ)
    → SequenceIso (cofibSequenceShifted n) (cofibSequenceShifted' n)
  fst (cofibSequenceShiftedIso n) m = {!idIso!}
  snd (cofibSequenceShiftedIso n) = {!!}


  cofibSequenceIso : (n : ℕ)
    → SequenceIso (ShiftSequenceExpl (cofibSequence n) n)
                   (cofibSequenceShifted n)
  cofibSequenceIso n = theIso , theCoh
    where
    theIso : (n₁ : ℕ) →
      Iso (cofibSequenceObj n (n₁ +ℕ n))
      (cofib (SequenceMapIterate A n n₁))
    theIso m with (n ≟ᵗd (m +ℕ n) )
    theIso m | inl s = pathToIso (cong cofib (sym (funExt (SequenceMapIterate'≡ A n m s))))
    ... | inr x = ⊥.rec (¬+<ᵗ x)

    transportCofib : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
      (f' f : A → B) (p : f' ≡ f) (g : B → C) (x : cofib f')
      → cofib→ g (subst cofib p x) ≡ subst cofib (cong (g ∘_) p) (cofib→ g x)
    transportCofib f' = J> λ g x → cong (cofib→ g) (transportRefl x) ∙ sym (transportRefl _)

    main-coh : (n m : ℕ) (p : _) (x : _)
      → (cong (_∘_ (seqMap A))
           (λ i → funExt (SequenceMapIterate'≡ A n m p) (~ i)))
      ≡ (λ i x₁ →
          seqMap A
          (SequenceMapIterate' A n (m +ℕ n) (isProp≤ᵗ p (<→≤ x) i) x₁))
       ∙ (λ i → funExt (SequenceMapIterate'≡ A n (suc m) (inl x)) (~ i))
    main-coh zero m p x =
      sym (sym (cong-∙  (_∘_ (seqMap A)) _ _)
        ∙ cong (cong (_∘_ (seqMap A)))
       (cong funExt ((λ i a
         → ((λ i₁ → SequenceMapIterate' A zero (m +ℕ zero)
                       (isProp≤ᵗ p (<→≤ x) (i₁ ∧ ~ i)) a))
         ∙ λ i₁ → SequenceMapIterate'≡ A zero m (isProp≤ᵗ p (<→≤ tt) (~ i)) a (~ i₁))
         ∙ funExt λ a → sym (lUnit _))))
    main-coh (suc n) m p x =
      sym (sym (cong-∙  (_∘_ (seqMap A)) _ _)
        ∙ cong (cong (_∘_ (seqMap A)))
        (cong funExt
          ((λ i a → (λ i₁ →
            SequenceMapIterate' A (suc n) (m +ℕ suc n)
              (isProp≤ᵗ p (<→≤ x) (i₁ ∧ ~ i)) a)
          ∙ sym (SequenceMapIterate'≡ A (suc n) m (isProp≤ᵗ p (<→≤ x) (~ i)) a))
         ∙ funExt λ _ → sym (lUnit _))))

    theCoh : (n₁ : ℕ) (a : cofibSequenceObj n (n₁ +ℕ n)) →
      cofib→ (seqMap A) (Iso.fun (theIso n₁) a) ≡
      Iso.fun (theIso (suc n₁)) (cofibSequenceMap n (n₁ +ℕ n) a)
    theCoh m a with (n ≟ᵗd (m +ℕ n)) | (n ≟ᵗd suc (m +ℕ n))
    ... | inl p | inl (inl x) =
        transportCofib _ _
          (sym (funExt (SequenceMapIterate'≡ A n m p))) (seqMap A {n = m +ℕ n}) a
      ∙ ((λ j → subst cofib (main-coh n m p x j) (cofib→ (seqMap A) a))
      ∙ substComposite cofib
          (cong (_∘_ (seqMap A))
           (λ i → SequenceMapIterate' A n (m +ℕ n)
             (isProp≤ᵗ p (<→≤ x) i)))
          (λ i → funExt (SequenceMapIterate'≡ A n (suc m) (inl x)) (~ i))
          (cofib→ (seqMap A) a))
      ∙ cong (subst cofib (sym (funExt (SequenceMapIterate'≡ A n (suc m) (inl x)))))
             (sym (transportCofib _ _
               (λ i → SequenceMapIterate' A n (m +ℕ n) (isProp≤ᵗ p (<→≤ x) i))
                 (seqMap A {n = m +ℕ n}) a))
    ... | inl p | inl (inr x) = ⊥.rec (¬m<m (m , +-suc m n ∙ sym x))
    ... | inl p | inr x = ⊥.rec (¬+<ᵗ x)
    ... | inr x | q = ⊥.rec (¬+<ᵗ x)

  asd = pushoutIso

  colimCofibSequenceIso : (n : ℕ)
    → Iso (SeqColim (cofibSequence n))
           (cofib {A = Sequence.obj A n} {B = SeqColim A} (incl {n = n}))
  colimCofibSequenceIso n =
    compIso (Iso-SeqColim→SeqColimShift _ n)
      (compIso (sequenceIso→ColimIso {A = ShiftSequenceIt (cofibSequence n) n}
                                      {B = cofibSequenceShifted n}
                 (compSequenceIso {A = ShiftSequenceIt (cofibSequence n) n}
                                  {B = ShiftSequenceExpl (cofibSequence n) n}
                                  {C = cofibSequenceShifted n}
                   (ShiftSequenceIso {A = cofibSequence n} n)
                                  (cofibSequenceIso n)))
        (compIso {!!} (compIso (invIso (SeqColim/₀Iso {S = cofibSequenceShifted n})) {!cofibIso !})))
 -- ShiftSequenceIso
  -- SeqColimIso : ?
  -- SeqColimIso = ?

--   cofibSequenceShifted≡ : {!!} ≡ {!!}
--   cofibSequenceShifted≡ = {!!}

--   cofibColim→colimCofib : (n : ℕ) → {!!} → {!!}
--   cofibColim→colimCofib = {!!}


-- module _ {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {E : Type ℓ'''}
--   (f : A → B) (h : E → B) (g : A → C) where
--   private
--     inl-h : E → Pushout f g
--     inl-h = inl ∘ h

--   Pushout[_mod_]_ : Type _
--   Pushout[_mod_]_ = Pushout {B = (cofib h)} (inr ∘ f) g

--   PushoutMod : Type _
--   PushoutMod = cofib {B = Pushout f g} (inl ∘ h)

--   →PushoutMod : Pushout[_mod_]_ → PushoutMod
--   →PushoutMod (inl (inl x)) = inl x
--   →PushoutMod (inl (inr x)) = inr (inl x)
--   →PushoutMod (inl (push a i)) = push a i
--   →PushoutMod (inr x) = inr (inr x)
--   →PushoutMod (push a i) = inr (push a i)

--   ←PushoutMod : PushoutMod → Pushout[_mod_]_
--   ←PushoutMod (inl x) = inl (inl x)
--   ←PushoutMod (inr (inl x)) = inl (inr x)
--   ←PushoutMod (inr (inr x)) = inr x
--   ←PushoutMod (inr (push a i)) = push a i
--   ←PushoutMod (push a i) = inl (push a i)

--   PushoutModIso : Iso Pushout[_mod_]_ PushoutMod
--   Iso.fun PushoutModIso = →PushoutMod
--   Iso.inv PushoutModIso = ←PushoutMod
--   Iso.rightInv PushoutModIso (inl x) = refl
--   Iso.rightInv PushoutModIso (inr (inl x)) = refl
--   Iso.rightInv PushoutModIso (inr (inr x)) = refl
--   Iso.rightInv PushoutModIso (inr (push a i)) = refl
--   Iso.rightInv PushoutModIso (push a i) = refl
--   Iso.leftInv PushoutModIso (inl (inl x)) = refl
--   Iso.leftInv PushoutModIso (inl (inr x)) = refl
--   Iso.leftInv PushoutModIso (inl (push a i)) = refl
--   Iso.leftInv PushoutModIso (inr x) = refl
--   Iso.leftInv PushoutModIso (push a i) = refl


-- module _ (C : CWskel ℓ-zero) (n : ℕ) where
--   open CWskel-fields C

--   collapseAs : ℕ → ℕ
--   collapseAs zero = 1
--   collapseAs (suc m) with ((suc m) ≟ᵗd n)
--   ... | inl s = 0
--   ... | inr x = fst (snd C) (suc m)

--   QuotBy : (m : ℕ) → Type
--   QuotBy zero = fst C (suc n)
--   QuotBy (suc m) = {!!}

--   collapseFam : (m : ℕ) → Type
--   collapseFam zero = ⊥
--   collapseFam (suc m) with ((suc m) ≟ᵗd n)
--   ... | inl s = Unit
--   ... | inr x = {!!} -- fst C (suc m)

--   -- αs : (m : ℕ) → Fin (collapseAs m) × S⁻ m → collapseFam m
--   -- αs (suc m) with (suc m ≟ᵗd n)
--   -- ... | inr x = α (suc m)

--   -- es-inl : (m : ℕ) (x : (suc m ≤ᵗ n)) → Iso Unit (Pushout (αs m) fst)
--   -- es-inl zero p = isContr→Iso isContrUnit
--   --                  (inr (0 , tt) , λ { (inr (zero , p)) → refl})
--   -- es-inl (suc m) p with (suc m ≟ᵗd n)
--   -- ... | inl s = isContr→Iso isContrUnit ((inl tt) , λ { (inl x) → refl})
--   -- es-inl (suc m) (inl a) | inr b = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans a b))
--   -- es-inl (suc m) (inr a) | inr b = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ (suc m)) (sym a) b))

--   -- es-inr : (m : ℕ) (x : n <ᵗ suc m) → fst C (suc m) ≃ Pushout (αs m) fst
--   -- es-inr zero p = {!!}
--   -- es-inr (suc m) p with (suc m ≟ᵗd n)
--   -- ... | inl (inl q) = {!!}
--   -- ... | inl (inr r) = {!!}
--   -- ... | inr x = e (suc m)

--   -- es : (n₁ : ℕ) →
--   --     (collapseFam (suc n₁)) ≃ Pushout (αs n₁) (λ r → fst r)
--   -- es m with (suc m ≟ᵗd n)
--   -- ... | inl x = isoToEquiv (es-inl m x)
--   -- ... | inr x = es-inr m x

--   -- C' : CWskel ℓ-zero
--   -- fst C' = collapseFam
--   -- fst (snd C') = collapseAs
--   -- fst (snd (snd C')) = αs
--   -- fst (snd (snd (snd C'))) = idfun _
--   -- snd (snd (snd (snd C'))) = es

