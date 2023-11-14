{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Fin
open import Cubical.Data.Empty
open import Cubical.Data.Sigma

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.FreeAbGroup.Base
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Relation.Nullary

-- all that stuff should probably go in the library somewhere

private
  variable
    ℓ ℓ' ℓ'' : Level

-- terminal map from any type to Unit
terminal : (A : Type ℓ) → A → Unit
terminal A x = tt

σ : (n : ℕ) → S₊ n → typ (Ω (S₊∙ (suc n)))
σ zero false = loop
σ zero true = refl
σ (suc n) x = toSusp (S₊∙ (suc n)) x

S⁻ : ℕ → Type
S⁻ zero = ⊥
S⁻ (suc n) = S₊ n

σ∙ : (n : ℕ) → S₊∙ n →∙ (Ω (S₊∙ (suc n)))
fst (σ∙ n) = σ n
snd (σ∙ zero) = refl
snd (σ∙ (suc n)) = rCancel (merid (ptSn (suc n)))

module _ (A : Type ℓ) where
  ℤ[_] : AbGroup ℓ
  ℤ[_] = FAGAbGroup {A = A}

suspFun-comp : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : B → C) (g : A → B)
               → suspFun (f ∘ g) ≡ (suspFun f) ∘ (suspFun g)
suspFun-comp f g i north = north
suspFun-comp f g i south = south
suspFun-comp f g i (merid a i₁) = merid (f (g a)) i₁

suspFun-const : {A : Type ℓ} {B : Type ℓ'} (b : B) → suspFun (λ (_ : A) → b) ≡ λ _ → north
suspFun-const b i north = north
suspFun-const b i south = merid b (~ i)
suspFun-const b i (merid a j) = merid b (~ i ∧ j)

suspFun-id : {A : Type ℓ} → suspFun (λ (a : A) → a) ≡ λ x → x
suspFun-id i north = north
suspFun-id i south = south
suspFun-id i (merid a j) = merid a j

-- a pointed map is constant iff its non-pointed part is constant
constant-pointed : {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B)
                 → fst f ≡ fst (const∙ A B) → f ≡ const∙ A B
constant-pointed {A = A} {B = B , b} f Hf i =
  (λ x → ((λ j → Hf j x) ∙∙ (λ j → Hf (~ j) (pt A)) ∙∙ (snd f)) i)
  , λ j → hcomp (λ k → λ { (i = i0) → invSides-filler (λ i → Hf i (pt A)) (λ i → snd f i) k (~ j)
                           ; (i = i1) → snd f k
                           ; (j = i1) → snd f k })
          (Hf ((~ i) ∧ (~ j)) (pt A))


-- TODO: trivGroupHom is located in the wrong place in the library
-- and should be done for groups and then maybe also for AbGroups?
0hom : {G : AbGroup ℓ} {H : AbGroup ℓ'} → AbGroupHom G H
0hom {G = G} {H = H} = trivGroupHom (AbGroup→Group G) H

-- TODO: remove this as it's subsumed by the above definition, but before doing this we should fix the definition of trivGroupHom in the library
-- constAbGroupHom : ∀ {ℓA} {ℓB} → (A : AbGroup ℓA) → (B : AbGroup ℓB) → AbGroupHom A B
-- fst (constAbGroupHom A B) = λ _ → B .snd .AbGroupStr.0g
-- snd (constAbGroupHom A B) = makeIsGroupHom λ a b → sym (B .snd .AbGroupStr.+IdL (B .snd .AbGroupStr.0g))

-- Characterizing equality in a fiber of some function f
pathFiber : {A B : Type} (f : A → B) (b : B) {a a' : A} {t : f a ≡ b} {t' : f a' ≡ b} →
  ((a , t) ≡ (a' , t' )) → Σ[ e ∈ a ≡ a' ] (t ≡ cong f e ∙ t')
pathFiber {A} {B} f b {a} {a'} {t} {t'} e =
  J (λ X _ → Σ[ e ∈ a ≡ fst X ] (t ≡ cong f e ∙ (snd X))) (refl , lUnit t) e

-- A pushout of a n-connected map is n-connected
-- The symmetric version of this is in Cubical.Homotopy.Connected
inlConnected : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (n : ℕ)
            → (f : C → A) (g : C → B)
            → isConnectedFun n g
            → isConnectedFun n {A = A} {B = Pushout f g} inl
inlConnected {A = A} {B = B} {C = C} n f g iscon =
  elim.isConnectedPrecompose inl n λ P → (k P) , λ a → refl
  where
  module _ {ℓ : Level} (P : (Pushout f g) → TypeOfHLevel ℓ n)
                   (h : (a : A) → typ (P (inl a)))
    where
    Q : B → TypeOfHLevel _ n
    Q b = (P (inr b))

    fun : (c : C) → typ (Q (g c))
    fun c = transport (λ i → typ (P (push c (i)))) (h (f c))

    k : (d : Pushout f g) → typ (P d)
    k (inl x) = h x
    k (inr x) = equiv-proof (elim.isEquivPrecompose g n Q iscon) fun .fst .fst x
    k (push a i) =
      hcomp (λ k → λ { (i = i1) → equiv-proof (elim.isEquivPrecompose g n Q iscon) fun .fst .snd i0 a
                     ; (i = i0) → transportTransport⁻ (λ j → typ (P (push a (~ j)))) (h (f a)) k })
            (transp (λ j → typ (P (push a (i ∨ (~ j)))))
                    (i)
                    (equiv-proof (elim.isEquivPrecompose g n Q iscon)
                                 fun .fst .snd (~ i) a))

PushoutEmptyFam : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ} {C : Type ℓ}
  → ¬ A → ¬ C
  → {f : A → B} {g : A → C}
  → Iso B (Pushout {A = A} {B = B} {C = C} f g)
PushoutEmptyFam {ℓ = ℓ} {A = A} {B = B} {C = C} ¬A ¬C =
  compIso iso1
    (pushoutIso _ _ _ _
      (uninhabEquiv (λ {()}) ¬A)
      (idEquiv B)
      (uninhabEquiv (λ {()}) ¬C)
      (funExt (λ{()})) (funExt λ{()}))
  where
  lift⊥ : ∀ ℓ → Type ℓ
  lift⊥ ℓ = Lift ⊥

  iso1 : Iso B (Pushout {A = lift⊥ ℓ} {B = B} {C = lift⊥ ℓ''} (λ{()}) λ{()})
  Iso.fun iso1 = inl
  Iso.inv iso1 (inl x) = x
  Iso.rightInv iso1 (inl x) = refl
  Iso.leftInv iso1 x = refl

open import Cubical.Data.Nat.Order
¬-suc-n<n : {n : ℕ} → ¬ (suc n < n)
¬-suc-n<n {n = n} = <-asym (1 , refl)

¬squeeze< : {n m : ℕ} → ¬ (n < m) × (m < suc n)
¬squeeze< {n = n} ((zero , p) , t) = ¬m<m (subst (_< suc n) (sym p) t)
¬squeeze< {n = n}  ((suc diff1 , p) , q) =
  ¬m<m (<-trans help (subst (_< suc n) (sym p) q))
  where
  help : suc n < suc (diff1 + suc n)
  help = diff1 , +-suc diff1 (suc n)

snot : {n : ℕ} → ¬ (suc n ≡ n)
snot {n = zero} = snotz
snot {n = suc n} p = snot {n = n} (cong predℕ p)

¬-<-suc : {n m : ℕ} → n < m → ¬ m < suc n
¬-<-suc {n = n} {m = m} (zero , q) p = ¬m<m (subst (_< suc n) (sym q) p)
¬-<-suc {n = n} {m = m} (suc diff , q) p = ¬m<m (<-trans p lem)
  where
  lem : suc n < m
  lem = diff , +-suc diff (suc n) ∙ q


-- stuff about Sequencetial colimits
open Sequence
open ElimDataShifted

-- terminating sequences
terminates : ∀ {ℓ} → Sequence ℓ → (n : ℕ) → Type ℓ
terminates seq n = (k : ℕ) → isEquiv (Sequence.map seq {n = k + n})

-- goal: prove that colim Aₘ ≃ Aₙ for a sequence
-- A₀ → A₁ → ... → Aₙ ≃ Aₙ₊₁ ≃ ...
module _ {ℓ : Level} (seq : Sequence ℓ) (n : ℕ) (term : terminates seq n)
  where
  shiftEq : ∀ {k} → seq .obj n ≃ (seq .obj (k + n))
  shiftEq {k = zero} = idEquiv _
  shiftEq {k = suc k} = compEquiv (shiftEq {k}) (_ , term k)

  shiftEq-coh : (k : ℕ) (x : _)
    → invEq shiftEq x
     ≡ invEq (compEquiv shiftEq (Sequence.map seq , term k)) (seq .Sequence.map x)
  shiftEq-coh zero x = sym (retEq (_ , term 0) x)
  shiftEq-coh (suc k) x =
    cong (invEq shiftEq) (sym (retEq (_ , term (suc k)) x))

  map← : ElimDataShifted seq n (λ _ → obj seq n)
  inclP map← = invEq shiftEq
  pushP map← = shiftEq-coh _

  -- induction principle for terminating sequences
  module _ {P : (k : ℕ) → seq .obj (k + n) → Type ℓ}
           (bs : (s : _) → P zero s)
           (indr : (k : ℕ) → ((y : _) → P k y) →  (x : _) → P (suc k) (Sequence.map seq x))
           where
    terminaates-seq-ind :  (k : ℕ) (x : _) → P k x
    terminaates-seq-ind zero = bs
    terminaates-seq-ind (suc k) x =
      subst (P (suc k)) (secEq (_ , term k) x)
            (indr k (terminaates-seq-ind k) (invEq (_ , term k) x))

    terminaates-seq-indβ : (k : ℕ) (s : ((y : seq .obj (k + n)) → P k y)) (x : _)
      → terminaates-seq-ind (suc k) (Sequence.map seq x)
       ≡ indr k (terminaates-seq-ind k) x
    terminaates-seq-indβ k s x =
        lem (Sequence.map seq , term k) x (P (suc k))
             (indr k (terminaates-seq-ind k))
      where
      lem : ∀ {ℓ ℓ'} {A B : Type ℓ} (e : A ≃ B) (x : A)
            (P : B → Type ℓ') (πP : (x : A) → P (fst e x))
        → subst P (secEq e (fst e x)) (πP (invEq e (fst e x))) ≡ πP x
      lem {ℓ' = ℓ'} {B = B} =
        EquivJ (λ A e → (x : A) (P : B → Type ℓ') (πP : (x : A) → P (fst e x))
                      → subst P (secEq e (fst e x)) (πP (invEq e (fst e x)))
                       ≡ πP x)
               λ b P πP → transportRefl _

  -- an special case
  module _
    (0case : (x : seq .obj n)
      → Path (SeqColim seq)
              (incl (elimShifted seq n (λ _ → obj seq n) map← (incl x)))
              (incl x)) where

    Lim→FiniteIso-main-lem : (k : ℕ) (x : seq .obj (k + n))
      → Path (SeqColim seq)
              (incl (elimShifted seq n (λ _ → obj seq n)
                                 map← (incl x)))
              (incl x)
    Lim→FiniteIso-main-lem =
      terminaates-seq-ind
        0case
        (λ k id x
        → cong incl
          (sym (cong (elimShifted seq n (λ _ → obj seq n) map←) (push x)))
             ∙∙ id x
             ∙∙ push x)

    Lim→FiniteIso-main-lemβ : (k : ℕ) (x : seq .obj (k + n))
        → Lim→FiniteIso-main-lem (suc k) (Sequence.map seq x)
         ≡ (cong incl
           (sym (cong (elimShifted seq n (λ _ → obj seq n)
                                    map←) (push x)))
             ∙∙ Lim→FiniteIso-main-lem k x
             ∙∙ push x)
    Lim→FiniteIso-main-lemβ k x =
      terminaates-seq-indβ
        0case
        (λ k id x
        → cong incl
          (sym (cong (elimShifted seq n (λ _ → obj seq n) map←) (push x)))
        ∙∙ id x
        ∙∙ push x)
        k (Lim→FiniteIso-main-lem k) x

-- main result
-- (todo: add more thy about colimits to get nicer proof)
Lim→FiniteIso : ∀ {ℓ} {seq : Sequence ℓ} (n : ℕ)
  → terminates seq n
  → Iso (obj seq n) (SeqColim seq)
Iso.fun (Lim→FiniteIso {seq = seq} n e) = incl
Iso.inv (Lim→FiniteIso {seq = seq} n e) = elimShifted seq n _ (map← seq n e)
Iso.rightInv (Lim→FiniteIso {seq = seq} n e) = elimShifted seq n _
  (record { inclP = λ {k} → paths k
          ; pushP = λ {k} → cohs k})
  where
  zero-case : (x : seq .obj n)
    → Path (SeqColim seq)
            (incl (elimShifted seq n (λ _ → obj seq n) (map← seq n e) (incl x)))
            (incl x)
  zero-case x i = incl (elimShiftedβ seq n 0 (λ _ → obj seq n) (map← seq n e) i x)

  paths : (k : ℕ) → (x : seq .obj (k + n))
    → Path (SeqColim seq)
            (incl (elimShifted seq n (λ _ → obj seq n) (map← seq n e) (incl x)))
            (incl x)
  paths = Lim→FiniteIso-main-lem seq n e zero-case

  cohs : (k : ℕ) (x : seq .obj (k + n))
    → PathP (λ i → Path (SeqColim seq)
                          (incl (elimShifted seq n (λ _ → obj seq n)
                                  (map← seq n e)
                          (push x i)))
                          (push x i))
             (paths k x) (paths (suc k) (seq .Sequence.map x))
  cohs k x =
    doubleCompPath-filler
      (λ i → incl (elimShifted seq n (λ _ → obj seq n)
                     (map← seq n e) (push x (~ i))))
      (Lim→FiniteIso-main-lem seq n e zero-case k x)
      (push x)
    ▷ sym (Lim→FiniteIso-main-lemβ seq n e (zero-case) k x)
Iso.leftInv (Lim→FiniteIso {seq = seq} n e) a =
    funExt⁻ (elimShiftedβ seq n _ (λ _ → obj seq n)
             (map← seq n e)) a

-- different form
Lim→Finite : ∀ {ℓ} {seq : Sequence ℓ} (n : ℕ)
  → terminates seq n
  → isEquiv {A = obj seq n} {B = SeqColim seq} (incl {n = n})
Lim→Finite n x = isoToEquiv (Lim→FiniteIso n x) .snd

-- elimination from colimit into prop
Lim→Prop : ∀ {ℓ ℓ'} {C : Sequence ℓ} {B : SeqColim C → Type ℓ'}
  → ((x : _) → isProp (B x))
  → (s : (n : ℕ) (x : obj C n) → B (incl x))
  → (x : _) → B x
Lim→Prop {C = C} pr ind (incl x) = ind _ x
Lim→Prop {C = C} {B = B} pr ind (push x i) =
  isProp→PathP {B = λ i → B (push x i)}
    (λ i → pr _)
    (ind _ x) (ind (suc _) (C .Sequence.map x)) i
