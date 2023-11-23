{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
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

open import prelude
open import spherebouquet

module cw-complex where


--- CW complexes ---
-- Definition of (the skeleton) of an arbitrary CW complex

-- New def: X 0 is empty and C (suc n) is pushout
yieldsCW : (ℕ → Type) → Type
yieldsCW X =
  Σ[ f ∈ (ℕ → ℕ) ]
    Σ[ α ∈ ((n : ℕ) → (Fin (f n) × (S⁻ n)) → X n) ]
      ((¬ X zero) ×
      ((n : ℕ) → X (suc n) ≃ Pushout (α n) fst))

CW : Type₁
CW = Σ[ X ∈ (ℕ → Type) ] (yieldsCW X)

CW₀-empty : (C : CW) → ¬ fst C 0
CW₀-empty C = snd (snd (snd C)) .fst

CW₁-discrete : (C : CW) → fst C 1 ≃ Fin (snd C .fst 0)
CW₁-discrete C = compEquiv (snd C .snd .snd .snd 0) (isoToEquiv main)
  where
  main : Iso (Pushout (fst (snd C .snd) 0) fst) (Fin (snd C .fst 0))
  Iso.fun main (inl x) = ⊥.rec (CW₀-empty C x)
  Iso.fun main (inr x) = x
  Iso.inv main = inr
  Iso.rightInv main x = refl
  Iso.leftInv main (inl x) = ⊥.rec (CW₀-empty C x)
  Iso.leftInv main (inr x) = refl

-- Technically, a CW complex should be the sequential colimit over the following maps
CW↪ : (T : CW) → (n : ℕ) → fst T n → fst T (suc n)
CW↪ (X , f , α , e₀ , e₊) n x = invEq (e₊ n) (inl x)

-- But if it stabilises, no need for colimits.
yieldsFinCW : (n : ℕ) (X : ℕ → Type) → Type
yieldsFinCW n X =
  Σ[ CW ∈ yieldsCW X ] ((k : ℕ) → isEquiv (CW↪ (X , CW) (k +ℕ n)))

-- ... which should give us finite CW complexes.
finCW : (n : ℕ) → Type₁
finCW n = Σ[ C ∈ (ℕ → Type) ] (yieldsFinCW n C)

finCW→CW : (n : ℕ) → finCW n → CW
finCW→CW n C = fst C , fst (snd C)

--the cofiber of the inclusion of X n into X (suc n)
cofiber : (n : ℕ) (C : CW) → Type
cofiber n C = Pushout (terminal (fst C n)) (CW↪ C n)

--...is basically a sphere bouquet
cofiber≃bouquet : (n : ℕ) (C : CW)
  → cofiber n C ≃ SphereBouquet n (Fin (snd C .fst n))
cofiber≃bouquet n C = Bouquet≃-gen n (snd C .fst n) (α n) e
  where
  s = Bouquet≃-gen
  α = C .snd .snd .fst
  e = C .snd .snd .snd .snd n

--sending X (suc n) into the cofiber
to_cofiber : (n : ℕ) (C : CW) → (fst C (suc n)) → (cofiber n C)
to_cofiber n C x = inr x

--the connecting map of the long exact sequence
δ-pre :  ∀ {ℓ} {A B : Type ℓ} (conn : A → B)
  → Pushout (terminal A) conn → Susp A
δ-pre conn (inl x) = north
δ-pre conn (inr x) = south
δ-pre conn (push a i) = merid a i

δ : (n : ℕ) (C : CW) → (cofiber n C) → Susp (fst C n)
δ n C = δ-pre (CW↪ C n)


-- elimination from Cₙ into prop
CWskel→Prop : (C : CW) {A : (n : ℕ) → fst C n → Type}
  → ((n : ℕ) (x : _) → isProp (A n x))
  → ((a : _) → A (suc zero) a)
  → ((n : ℕ) (a : _) → (A (suc n) a → A (suc (suc n)) (CW↪ C (suc n) a)))
  → (n : _) (c : fst C n) → A n c
CWskel→Prop C {A = A} pr b eqs zero c = ⊥.rec (CW₀-empty C c)
CWskel→Prop C {A = A} pr b eqs (suc zero) = b
CWskel→Prop C {A = A} pr b eqs (suc (suc n)) c =
  subst (A (suc (suc n)))
        (retEq (snd C .snd .snd .snd (suc n)) c)
        (help (CWskel→Prop C pr b eqs (suc n)) _)
  where
  help : (inder : (c₁ : fst C (suc n)) → A (suc n) c₁)
       → (a : Pushout _ fst)
       → A (suc (suc n)) (invEq (snd C .snd .snd .snd (suc n)) a)
  help inder =
    elimProp _ (λ _ → pr _ _) (λ b → eqs n _ (inder b))
     λ c → subst (A (suc (suc n)))
                  (cong (invEq (snd C .snd .snd .snd (suc n))) (push (c , ptSn n)))
                  (eqs n _ (inder _))

isSet-CW₀ : (C : CW) → isSet (fst C (suc zero))
isSet-CW₀ C =
   isOfHLevelRetractFromIso 2 (equivToIso (CW₁-discrete C))
    isSetFin

open import Cubical.HITs.SequentialColimit
open Sequence

realiseSeq : CW → Sequence ℓ-zero
Sequence.obj (realiseSeq (C , p)) = C
Sequence.map (realiseSeq C) = CW↪ C _

-- realisation of CW complex from skeleton
realise : CW → Type
realise C = SeqColim (realiseSeq C)

-- send the stage n to the realization (the same as incl, but with explicit args and type)
CW↪∞ : (C : CW) → (n : ℕ) → fst C n → realise C
CW↪∞ C n x = incl x

-- eliminating from CW complex into prop
CW→Prop : (C : CW) {A : realise C → Type}
  → ((x : _) → isProp (A x))
  → ((a : _) → A (incl {n = suc zero} a))
  → (a : _) → A a
CW→Prop C {A = A} pr ind  =
  Lim→Prop pr (CWskel→Prop C (λ _ _ → pr _)
    ind
    λ n a → subst A (push a))

-- realisation of finite complex
realiseFin : (n : ℕ) (C : finCW n) → Iso (fst C n) (realise (finCW→CW n C))
realiseFin n C = Lim→FiniteIso n (snd C .snd)

-- elimination principles for CW complexes
module _ {ℓ : Level} (C : CW) where
  private
    e = snd C .snd .snd .snd
    A : (n : ℕ) → _
    A n = Fin (snd C .fst n)
    α = snd C .snd .fst

  module _ (n : ℕ) {B : fst C (suc n) → Type ℓ}
         (inler : (x : fst C n) → B (invEq (e n) (inl x)))
         (inrer : (x : A n) → B (invEq (e n) (inr x)))
         (pusher : (x : A n) (y : S⁻ n)
        → PathP (λ i → B (invEq (e n) (push (x , y) i)))
                 (inler (α n (x , y)))
                 (inrer x)) where
    private
      gen : ∀ {ℓ ℓ'} {A B : Type ℓ} (C : A → Type ℓ')
                  (e : A ≃ B)
               → ((x : B) → C (invEq e x))
               → (x : A) → C x
      gen C e h x = subst C (retEq e x) (h (fst e x))

      gen-coh : ∀ {ℓ ℓ'} {A B : Type ℓ} (C : A → Type ℓ')
                  (e : A ≃ B) (h : (x : B) → C (invEq e x))
               → (b : B)
               → gen C e h (invEq e b) ≡ h b
      gen-coh {ℓ' = ℓ'} {A = A} {B = B} C e =
        EquivJ (λ A e → (C : A → Type ℓ') (h : (x : B) → C (invEq e x))
               → (b : B)
               → gen C e h (invEq e b) ≡ h b)
               (λ C h b → transportRefl (h b)) e C

      main : (x : _) → B (invEq (snd C .snd .snd .snd n) x)
      main (inl x) = inler x
      main (inr x) = inrer x
      main (push (x , y) i) = pusher x y i

    CW-elim : (x : _) → B x
    CW-elim = gen B (snd C .snd .snd .snd n) main

    CW-elim-inl : (x : _) → CW-elim (invEq (snd C .snd .snd .snd n) (inl x)) ≡ inler x
    CW-elim-inl x = gen-coh B (snd C .snd .snd .snd n) main (inl x)

  module _ (n : ℕ) {B : fst C (suc (suc n)) → Type ℓ}
           (inler : (x : fst C (suc n))
                  → B (invEq (snd C .snd .snd .snd (suc n)) (inl x)))
           (ind : ((x : Fin (snd C .fst (suc n))) (y : S₊ n)
           → PathP (λ i → B (invEq (snd C .snd .snd .snd (suc n))
                                   ((push (x , y) ∙ sym (push (x , ptSn n))) i)))
                   (inler (snd C .snd .fst (suc n) (x , y)))
                   (inler (snd C .snd .fst (suc n) (x , ptSn n))))) where
    CW-elim' : (x : _) → B x
    CW-elim' =
      CW-elim (suc n) inler
        (λ x → subst (λ t → B (invEq (snd C .snd .snd .snd (suc n)) t))
                      (push (x , ptSn n))
                      (inler (α (suc n) (x , ptSn n))))
        λ x y → toPathP (sym (substSubst⁻ (B ∘ invEq (snd C .snd .snd .snd (suc n)))  _ _)
           ∙ cong (subst (λ t → B (invEq (snd C .snd .snd .snd (suc n)) t))
                         (push (x , ptSn n)))
                  (sym (substComposite (B ∘ invEq (snd C .snd .snd .snd (suc n))) _ _ _)
            ∙ fromPathP (ind x y)))

    CW-elim'-inl : (x : _)
      → CW-elim' (invEq (snd C .snd .snd .snd (suc n)) (inl x)) ≡ inler x
    CW-elim'-inl = CW-elim-inl (suc n) {B = B} inler _ _


module CW-fields (C : CW) where
  card = C .snd .fst
  A = Fin ∘ card
  α = C .snd .snd .fst
  e = C .snd .snd .snd .snd
  
