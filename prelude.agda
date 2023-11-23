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
open import Cubical.HITs.Truncation as TR

open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Connected

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Properties

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

-- connectedness lemma
isConnectedCong² : ∀ {ℓ ℓ'} (n : HLevel) {A : Type ℓ} {B : Type ℓ'} (f : A → B)
    → isConnectedFun (suc (suc n)) f
    → ∀ {a₀ a₁ a₂ a₃} {p : a₀ ≡ a₁} {q : a₂ ≡ a₃}
                       {r : a₀ ≡ a₂} {s : a₁ ≡ a₃}
    → isConnectedFun n
         {A = Square p q r s}
         {B = Square (cong f p) (cong f q) (cong f r) (cong f s)}
         (λ p i j → f (p i j))
isConnectedCong² n {A = A} f cf {a₀} {a₁} {r = r} {s = s}
  = isConnectedCong²' _ r _ s
  where
  isConnectedCong²' : (a₂ : A) (r : a₀ ≡ a₂) (a₃ : A) (s : a₁ ≡ a₃)
       {p : a₀ ≡ a₁} {q : a₂ ≡ a₃}
    → isConnectedFun n
         {A = Square p q r s}
         {B = Square (cong f p) (cong f q) (cong f r) (cong f s)}
         (λ p i j → f (p i j))
  isConnectedCong²' =
    J> (J> isConnectedCong n (cong f) (isConnectedCong (suc n) f cf))

sphereToTrunc : (n : ℕ) {A : S₊ n → Type}
  → ((x : S₊ n) → hLevelTrunc (suc n) (A x))
  → ∥ ((x : _) → A x) ∥₁
sphereToTrunc zero {A = A} indr =
  TR.rec squash₁ (λ p → TR.rec squash₁
    (λ q → ∣ (λ { false → q ; true → p}) ∣₁)
         (indr false)) (indr true)
sphereToTrunc (suc zero) {A = A} indr =
  lem (indr base) (cong indr loop)
  where
  lem : (x : hLevelTrunc 2 (A base))
      → PathP (λ i → hLevelTrunc 2 (A (loop i))) x x
      → ∥ ((x : S¹) → A x) ∥₁
  lem = TR.elim (λ _ → isSetΠ λ _ → isProp→isSet squash₁) λ a p
    → TR.rec squash₁ (λ q → ∣ (λ { base → a
      ; (loop i) → toPathP {A = λ i → A (loop i)} q i}) ∣₁)
        (PathIdTruncIso 1 .Iso.fun
          (fromPathP p))
sphereToTrunc (suc (suc n)) {A = A} indr =
  lem (sphereToTrunc (suc n)) (indr north) (indr south)
    λ a → cong indr (merid a)
  where
  lem : ({A : S₊ (suc n) → Type} →
      ((i : S₊ (suc n)) → hLevelTrunc (suc (suc n)) (A i)) →
      ∥ ((x : S₊ (suc n)) → A x) ∥₁)
      → (x : hLevelTrunc (3 + n) (A north))
        (y : hLevelTrunc (3 + n) (A south))
      → ((a : _) → PathP (λ i → hLevelTrunc (3 + n) (A (merid a i))) x y)
      → ∥ ((x : S₊ (2 + n)) → A x) ∥₁
  lem indr =
    TR.elim (λ _ → isOfHLevelΠ2 (3 + n)
              λ _ _ → isProp→isOfHLevelSuc (2 + n) squash₁)
      λ a → TR.elim (λ _ → isOfHLevelΠ (3 + n)
              λ _ → isProp→isOfHLevelSuc (2 + n) squash₁)
              λ b → λ f →
          PT.map (λ ma → λ { north → a
                            ; south → b
                            ; (merid a i) → ma a i})
            (indr {A = λ x → PathP (λ i → A (merid x i)) a b}
              λ x → TR.rec (isOfHLevelTrunc (2 + n))
                (λ p → ∣ toPathP p ∣)
                (Iso.fun (PathIdTruncIso _) (fromPathP (f x))))

compPath-filler'' : ∀ {ℓ} {A : Type ℓ} {x y z : A}
      (p : x ≡ y) (q : y ≡ z)
      → Square refl (p ∙ q) (sym p) q
compPath-filler'' p q i j =
  hcomp (λ k → λ {(i = i0) → p i1
                 ; (i = i1) → compPath-filler p q k j
                 ; (j = i0) → p (~ i)
                 ; (j = i1) → q (i ∧ k)})
        (p (~ i ∨ j))

addGroupHom : ∀ {ℓ} (A B : AbGroup ℓ) (ϕ ψ : AbGroupHom A B) → AbGroupHom A B
fst (addGroupHom A B ϕ ψ) x = AbGroupStr._+_ (snd B) (ϕ .fst x) (ψ .fst x) 
snd (addGroupHom A B ϕ ψ) = makeIsGroupHom
  λ x y → cong₂ (AbGroupStr._+_ (snd B))
                 (IsGroupHom.pres· (snd ϕ) x y)
                 (IsGroupHom.pres· (snd ψ) x y)
        ∙ AbGroupTheory.comm-4 B (fst ϕ x) (fst ϕ y) (fst ψ x) (fst ψ y)

negGroupHom : ∀ {ℓ} (A B : AbGroup ℓ) (ϕ : AbGroupHom A B) → AbGroupHom A B
fst (negGroupHom A B ϕ) x = AbGroupStr.-_ (snd B) (ϕ .fst x)
snd (negGroupHom A B ϕ) =
  makeIsGroupHom λ x y
    → sym (IsGroupHom.presinv (snd ϕ) (AbGroupStr._+_ (snd A) x y))
     ∙ cong (fst ϕ) (GroupTheory.invDistr (AbGroup→Group A) x y
                  ∙ AbGroupStr.+Comm (snd A) _ _)
     ∙ IsGroupHom.pres· (snd ϕ) _ _
     ∙ cong₂ (AbGroupStr._+_ (snd B))
             (IsGroupHom.presinv (snd ϕ) x)
             (IsGroupHom.presinv (snd ϕ) y)

subtrGroupHom : ∀ {ℓ} (A B : AbGroup ℓ) (ϕ ψ : AbGroupHom A B) → AbGroupHom A B
subtrGroupHom A B ϕ ψ = addGroupHom A B (negGroupHom A B ϕ) (negGroupHom A B ψ)
