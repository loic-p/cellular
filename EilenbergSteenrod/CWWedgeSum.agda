{-# OPTIONS --cubical #-}
module EilenbergSteenrod.CWWedgeSum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path

open import Cubical.Data.Empty renaming (rec to emptyrec)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.Wedge
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout

open import Cubical.CW.Base
open import Cubical.CW.Properties



Fin-aux1 : (n m : ℕ) → m <ᵗ n → predℕ n <ᵗ m → ⊥
Fin-aux1 zero m H _ = H
Fin-aux1 (suc n) m H H' = ¬m<m {m} (≤-trans {suc m}{suc n}{m} (<ᵗ→< {m}{suc n} H) (<ᵗ→< {n}{m} H'))

Fin-aux2 : (n m l : ℕ) → (l <ᵗ m) → (n <ᵗ predℕ m) → suc n <ᵗ m
Fin-aux2 n m l H H' = subst (suc n <ᵗ_) (sym (suc-predℕ m (λ H'' → subst (l <ᵗ_) H'' H))) H'

opaque
  Fin-aux3 : (n m l : ℕ) → (l <ᵗ n) → (n <ᵗ m) → predℕ n <ᵗ predℕ m
  Fin-aux3 n m l H H' = <→<ᵗ {predℕ n}{predℕ m} (subst (λ X → X ≤ predℕ m)
                                                       (suc-predℕ n (λ H'' → subst (l <ᵗ_) H'' H))
                                                       (predℕ-≤-predℕ {suc n}{m} (<ᵗ→< H')))

Fin-aux4 : (n : ℕ) → suc n ≡ n → ⊥
Fin-aux4 zero H = snotz {zero} H
Fin-aux4 (suc n) H = Fin-aux4 n (injSuc H)

wedgeIso : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {A' : Type ℓ₃} {B' : Type ℓ₄} (a : A) (b : B) (eA : A ≃ A') (eB : B ≃ B')
           → Iso ((A , a) ⋁ (B , b)) ((A' , eA .fst a) ⋁ (B' , eB .fst b))
wedgeIso {A = A} {B} {A'} {B'} a b eA eB = iso₀
  where
    fun : ((A , a) ⋁ (B , b)) → ((A' , eA .fst a) ⋁ (B' , eB .fst b))
    fun (inl x) = inl (eA .fst x)
    fun (inr x) = inr (eB .fst x)
    fun (push a i) = push a i

    iso₀ : Iso ((A , a) ⋁ (B , b)) ((A' , eA .fst a) ⋁ (B' , eB .fst b))
    Iso.fun iso₀ = fun
    Iso.inv iso₀ (inl x) = inl (invEq eA x)
    Iso.inv iso₀ (inr x) = inr (invEq eB x)
    Iso.inv iso₀ (push x i) = ((λ i → inl (retEq eA a i)) ∙∙ (push x) ∙∙ λ i → inr (retEq eB b (~ i))) i
    Iso.leftInv iso₀ (inl x) i = inl (retEq eA x i)
    Iso.leftInv iso₀ (inr x) i = inr (retEq eB x i)
    Iso.leftInv iso₀ (push x i) j =
        hcomp (λ k → λ { (i = i0) → inl (retEq eA a (j ∨ (~ k)))
                       ; (i = i1) → inr (retEq eB b (j ∨ (~ k)))
                       ; (j = i0) → doubleCompPath-filler (λ i → inl (retEq eA a i)) (push x) (λ i → inr (retEq eB b (~ i))) k i
                       ; (j = i1) → push x i })
              (push x i)
    Iso.rightInv iso₀ (inl x) i = inl (secEq eA x i)
    Iso.rightInv iso₀ (inr x) i = inr (secEq eB x i)
    Iso.rightInv iso₀ (push x i) j =
        hcomp (λ k → λ { (i = i0) → inl (compPath→Square {p = λ i → secEq eA (eA .fst a) i}{refl}
                                                         {λ i → eA .fst (retEq eA a i)}{refl}
                                                         (cong (λ X → X ∙ refl) (commPathIsEq (eA .snd) a)) j (~ k))
                       ; (i = i1) → inr (compPath→Square {p = λ i → secEq eB (eB .fst b) i}{refl}
                                                         {λ i → eB .fst (retEq eB b i)}{refl}
                                                         (cong (λ X → X ∙ refl) (commPathIsEq (eB .snd) b)) j (~ k))
                       ; (j = i0) → fun (doubleCompPath-filler (λ i → inl (retEq eA a i)) (push x) (λ i → inr (retEq eB b (~ i))) k i)
                       ; (j = i1) → push x i })
              (push x i)

wedgeIso' : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} {A : Type ℓ₁} {B : Type ℓ₂} {A' : Type ℓ₃} {B' : Type ℓ₄} (a : A') (b : B') (eA : A ≃ A') (eB : B ≃ B')
            → Iso ((A , invEq eA a) ⋁ (B , invEq eB b)) ((A' , a) ⋁ (B' , b))
wedgeIso' {A = A} {B} {A'} {B'} a b eA eB = invIso (wedgeIso a b (invEquiv eA) (invEquiv eB))

wedgeFinIso : (n m : ℕ) (basen : Fin n) (basem : Fin m) → Iso ((Fin n , basen) ⋁ (Fin m , basem)) ((Fin n) ⊎ (Fin (predℕ m)))
Iso.fun (wedgeFinIso n m basen basem) (inl x) = inl x
Iso.fun (wedgeFinIso n m basen basem) (inr x) with (fst x ≟ᵗ fst basem)
... | lt H = inr (fst x , <→<ᵗ {fst x}{predℕ m} (≤-trans (<ᵗ→< {fst x}{fst basem} H)
                            (predℕ-≤-predℕ {suc (fst basem)}{m} (<ᵗ→< (snd basem)))))
... | eq H = inl basen
... | gt H = inr (predℕ (fst x) ,  Fin-aux3 (fst x) m (fst basem) H (snd x))
Iso.fun (wedgeFinIso n m basen basem) (push a i) with (fst basem ≟ᵗ fst basem)
... | lt H with (¬m<ᵗm {fst basem} H)
...        | ()
Iso.fun (wedgeFinIso n m basen basem) (push a i) | eq H = inl basen
Iso.fun (wedgeFinIso n m basen basem) (push a i) | gt H with (¬m<ᵗm {fst basem} H)
... | ()
Iso.inv (wedgeFinIso n m basen basem) (inl x) = inl x
Iso.inv (wedgeFinIso n m basen basem) (inr x) with (fst x ≟ᵗ fst basem)
... | lt H = inr (fst x , <ᵗ-trans {fst x}{fst basem}{m} H (snd basem))
... | eq H = inr (suc (fst x) , Fin-aux2 (fst x) m (fst basem) (snd basem) (snd x))
... | gt H = inr (suc (fst x) , Fin-aux2 (fst x) m (fst basem) (snd basem) (snd x))
Iso.leftInv (wedgeFinIso n m basen basem) (inl x) = refl
Iso.leftInv (wedgeFinIso n m basen basem) (inr x) with (fst x ≟ᵗ fst basem)
... | lt H with (fst x ≟ᵗ fst basem)
...        | lt H' = λ i → inr (Fin≡ {m} (fst x , <ᵗ-trans {fst x}{fst basem}{m} H' (snd basem)) x refl i)
...        | eq H' = emptyrec (¬m<ᵗm {fst basem} (subst (λ X → X <ᵗ fst basem) H' H))
...        | gt H' = emptyrec (¬m<ᵗm {fst basem} (<ᵗ-trans {fst basem}{fst x}{fst basem} H' H))
Iso.leftInv (wedgeFinIso n m basen basem) (inr x) | eq H = (push tt) ∙∙ (λ i → inr (Fin≡ {m} basem x (sym H) i)) ∙∙ (λ _ → inr x)
Iso.leftInv (wedgeFinIso n m basen basem) (inr x) | gt H with (predℕ (fst x) ≟ᵗ fst basem)
... | lt H' = emptyrec (Fin-aux1 (fst x) (fst basem) H H')
... | eq H' = λ i → inr (Fin≡ {m} (suc (predℕ (fst x)) , Fin-aux2 (predℕ (fst x)) m (fst basem) (snd basem)
                                                         (Fin-aux3 (fst x) m (fst basem) H (snd x)))
                                  x (sym (suc-predℕ (fst x) (λ H'' → subst (fst basem <ᵗ_) H'' H))) i)
... | gt H' = λ i → inr (Fin≡ {m} (suc (predℕ (fst x)) , Fin-aux2 (predℕ (fst x)) m (fst basem) (snd basem)
                                                         (Fin-aux3 (fst x) m (fst basem) H (snd x)))
                                  x (sym (suc-predℕ (fst x) (λ H'' → subst (fst basem <ᵗ_) H'' H))) i)
Iso.leftInv (wedgeFinIso n m basen basem) (push tt i) j with (fst basem ≟ᵗ fst basem)
... | lt H with (¬m<ᵗm {fst basem} H)
... | ()
Iso.leftInv (wedgeFinIso n m basen basem) (push tt i) j | eq H =
  hcomp (λ k → λ { (i = i0) → push tt (~ k)
                 ; (i = i1) → doubleCompPath-filler (push tt) (λ i → inr (Fin≡ {m} basem basem (sym H) i)) (λ _ → inr basem) k j
                 ; (j = i0) → push tt (~ k)
                 ; (j = i1) → push tt (i ∨ (~ k)) })
        (inr (isSet→SquareP {A = λ i j → Fin m} (λ _ _ → isSetFin {m}) (λ _ → basem) (λ _ → basem) (λ _ → basem)
                            (Fin≡ {m} basem basem (sym H)) j i))
Iso.leftInv (wedgeFinIso n m basen basem) (push tt i) j | gt H with (¬m<ᵗm {fst basem} H)
... | ()
Iso.rightInv (wedgeFinIso n m basen basem) (inl x) = refl
Iso.rightInv (wedgeFinIso n m basen basem) (inr x) with (fst x ≟ᵗ fst basem)
... | lt H with (fst x ≟ᵗ fst basem)
...        | lt H' = λ i → inr (Fin≡ {predℕ m} (fst x , <→<ᵗ {fst x}{predℕ m}(≤-trans (<ᵗ→< H') (predℕ-≤-predℕ
                                                          (<ᵗ→< {fst basem}{m} (snd basem))))) x refl i)
...        | eq H' = emptyrec (¬m<ᵗm {fst basem} (subst (λ X → X <ᵗ fst basem) H' H))
...        | gt H' = emptyrec (¬m<ᵗm {fst basem} (<ᵗ-trans {fst basem}{fst x}{fst basem} H' H))
Iso.rightInv (wedgeFinIso n m basen basem) (inr x) | eq H with (suc (fst x) ≟ᵗ fst basem)
... | lt H' = emptyrec (¬m<ᵗm {fst x} (<ᵗ-trans-suc {suc (fst x)}{fst x} (subst (suc (fst x) <ᵗ_) (sym H) H')))
... | eq H' = emptyrec (Fin-aux4 (fst x) (H' ∙ (sym H)))
... | gt H' = λ i → inr (Fin≡ {predℕ m} (fst x , Fin-aux3 (suc (fst x)) m (fst basem) H'
                                                   (Fin-aux2 (fst x) m (fst basem) (snd basem) (snd x))) x refl i)
Iso.rightInv (wedgeFinIso n m basen basem) (inr x) | gt H with (suc (fst x) ≟ᵗ fst basem)
... | lt H' = emptyrec (¬m<ᵗm {fst x} (<ᵗ-trans-suc {suc (fst x)}{fst x} (<ᵗ-trans {suc (fst x)}{fst basem}{fst x} H' H)))
... | eq H' = emptyrec (¬m<ᵗm {fst x} (<ᵗ-trans-suc {suc (fst x)}{fst x} (subst (λ X → X <ᵗ fst x) (sym H') H)))
... | gt H' = λ i → inr (Fin≡ {predℕ m} (fst x , Fin-aux3 (suc (fst x)) m (fst basem) H'
                                                   (Fin-aux2 (fst x) m (fst basem) (snd basem) (snd x))) x refl i)

-- CW structure for the wedge sum of two based CW complexes

module _ (ℓ : Level) (C D : CWskel ℓ) (c₀ : Fin (CWskel-fields.card C 0)) (d₀ : Fin (CWskel-fields.card D 0)) where
  open CWskel-fields

  basepoint : (C : CWskel ℓ) (c₀ : Fin (CWskel-fields.card C 0)) (n : ℕ) → fst C (suc n)
  basepoint C c₀ zero = invEq (CW₁-discrete C) c₀
  basepoint C c₀ (suc n) = CW↪ C (suc n) (basepoint C c₀ n)

  wedgeA : ℕ → Type ℓ
  wedgeA zero = fst C zero
  wedgeA (suc n) = (fst C (suc n) , basepoint C c₀ n) ⋁ (fst D (suc n) , basepoint D d₀ n)

  wedgeCells : ℕ → ℕ
  wedgeCells zero = card C zero +ℕ predℕ (card D zero)
  wedgeCells (suc n) = card C (suc n) +ℕ card D (suc n)

  wedgeMap-aux1 : (n : ℕ) → Fin (card C (suc n)) ⊎ Fin (card D (suc n)) × (S⁻ (suc n)) → wedgeA (suc n)
  wedgeMap-aux1 n (inl a , x) = inl (α C (suc n) (a , x))
  wedgeMap-aux1 n (inr a , x) = inr (α D (suc n) (a , x))

  wedgeMap : (n : ℕ) → Fin (wedgeCells n) × (S⁻ n) → wedgeA n
  wedgeMap zero ()
  wedgeMap (suc n) (a , x) = wedgeMap-aux1 n ( Iso.inv (Iso-Fin⊎Fin-Fin+ {card C (suc n)}{card D (suc n)}) a , x)

  wedgeIso₀ : Iso ((fst C 1 , basepoint C c₀ 0) ⋁ (fst D 1 , basepoint D d₀ 0)) (Pushout (wedgeMap 0) fst)
  wedgeIso₀ = compIso (compIso iso0 (wedgeFinIso (card C 0) (card D 0) c₀ d₀))
                      (compIso (Iso-Fin⊎Fin-Fin+ {card C 0}{predℕ (card D 0)}) iso1)
    where
      iso0-inv : ((Fin (card C 0) , c₀) ⋁ (Fin (card D 0) , d₀)) → ((fst C 1 , basepoint C c₀ 0) ⋁ (fst D 1 , basepoint D d₀ 0))
      iso0-inv (inl x) = inl (invEq (CW₁-discrete C) x)
      iso0-inv (inr x) = inr (invEq (CW₁-discrete D) x)
      iso0-inv (push a i) = push a i

      iso0 : Iso ((fst C 1 , basepoint C c₀ 0) ⋁ (fst D 1 , basepoint D d₀ 0)) ((Fin (card C 0) , c₀) ⋁ (Fin (card D 0) , d₀))
      iso0 = wedgeIso' c₀ d₀ (CW₁-discrete C) (CW₁-discrete D)

      iso1 : Iso (Fin ((card C 0) +ℕ (predℕ (card D 0)))) (Pushout (wedgeMap 0) fst)
      Iso.fun iso1 x = inr x
      Iso.inv iso1 (inl x) with (C .snd .snd .snd .fst x)
      ... | ()
      Iso.inv iso1 (inr x) = x
      Iso.leftInv iso1 x = refl
      Iso.rightInv iso1 (inl x) with (C .snd .snd .snd .fst x)
      ... | ()
      Iso.rightInv iso1 (inr x) = refl

  wedgeIsoₛ : (n : ℕ) → Iso ((fst C (suc (suc n)) , basepoint C c₀ (suc n)) ⋁ (fst D (suc (suc n)) , basepoint D d₀ (suc n)))
                            (Pushout (wedgeMap (suc n)) fst)
  wedgeIsoₛ n = compIso iso0 (compIso iso1 iso2)
    where
      iso0 : Iso ((fst C (suc (suc n)) , basepoint C c₀ (suc n)) ⋁ (fst D (suc (suc n)) , basepoint D d₀ (suc n)))
                 ((Pushout (α C (suc n)) fst , inl (basepoint C c₀ n)) ⋁ (Pushout (α D (suc n)) fst , inl (basepoint D d₀ n)))
      iso0 = wedgeIso' (inl (basepoint C c₀ n)) (inl (basepoint D d₀ n)) (e C (suc n)) (e D (suc n))

      iso1 : Iso ((Pushout (α C (suc n)) fst , inl (basepoint C c₀ n)) ⋁ (Pushout (α D (suc n)) fst , inl (basepoint D d₀ n)))
                 (Pushout (wedgeMap-aux1 n) fst)
      Iso.fun iso1 (inl (inl x)) = inl (inl x)
      Iso.fun iso1 (inl (inr x)) = inr (inl x)
      Iso.fun iso1 (inl (push (a , x) i)) = push (inl a , x) i
      Iso.fun iso1 (inr (inl x)) = inl (inr x)
      Iso.fun iso1 (inr (inr x)) = inr (inr x)
      Iso.fun iso1 (inr (push (a , x) i)) = push (inr a , x) i
      Iso.fun iso1 (push a i) = inl (push a i)
      Iso.inv iso1 (inl (inl x)) = inl (inl x)
      Iso.inv iso1 (inl (inr x)) = inr (inl x)
      Iso.inv iso1 (inl (push a i)) = push a i
      Iso.inv iso1 (inr (inl x)) = inl (inr x)
      Iso.inv iso1 (inr (inr x)) = inr (inr x)
      Iso.inv iso1 (push (inl a , x) i) = inl (push (a , x) i)
      Iso.inv iso1 (push (inr a , x) i) = inr (push (a , x) i)
      Iso.leftInv iso1 (inl (inl x)) = refl
      Iso.leftInv iso1 (inl (inr x)) = refl
      Iso.leftInv iso1 (inl (push a i)) = refl
      Iso.leftInv iso1 (inr (inl x)) = refl
      Iso.leftInv iso1 (inr (inr x)) = refl
      Iso.leftInv iso1 (inr (push a i)) = refl
      Iso.leftInv iso1 (push a i) = refl
      Iso.rightInv iso1 (inl (inl x)) = refl
      Iso.rightInv iso1 (inl (inr x)) = refl
      Iso.rightInv iso1 (inl (push a i)) = refl
      Iso.rightInv iso1 (inr (inl x)) = refl
      Iso.rightInv iso1 (inr (inr x)) = refl
      Iso.rightInv iso1 (push (inl x₁ , x) i) = refl
      Iso.rightInv iso1 (push (inr x₁ , x) i) = refl

      eqFin = isoToEquiv (invIso (Iso-Fin⊎Fin-Fin+ {card C (suc n)}{card D (suc n)}))

      iso2-inv : (Pushout (wedgeMap (suc n)) fst) → (Pushout (wedgeMap-aux1 n) fst)
      iso2-inv (inl x) = inl x
      iso2-inv (inr x) = inr (eqFin .fst x)
      iso2-inv (push (a , x) i) = push (eqFin .fst a , x) i

      iso2 : Iso (Pushout (wedgeMap-aux1 n) fst) (Pushout (wedgeMap (suc n)) fst)
      Iso.fun iso2 (inl x) = inl x
      Iso.fun iso2 (inr x) = inr (invEq eqFin x)
      Iso.fun iso2 (push (a , x) i) =
        ((λ i → inl (wedgeMap-aux1 n (secEq eqFin a (~ i) , x)))
        ∙∙ (push (invEq eqFin a , x)) ∙∙ refl) i
      Iso.inv iso2 x = iso2-inv x
      Iso.leftInv iso2 (inl x) = refl
      Iso.leftInv iso2 (inr x) i = inr (secEq eqFin x i)
      Iso.leftInv iso2 (push (a , x) i) j =
        hcomp (λ k → λ { (i = i0) → inl (wedgeMap-aux1 n (secEq eqFin a (k ∨ j) , x))
                       ; (i = i1) → inr (secEq eqFin a j)
                       ; (j = i0) → iso2-inv (doubleCompPath-filler (λ i → inl (wedgeMap-aux1 n (secEq eqFin a (~ i) , x)))
                                                                    (push (invEq eqFin a , x)) refl k i)
                       ; (j = i1) → push (a , x) i })
              (push (secEq eqFin a j , x) i)
      Iso.rightInv iso2 (inl x) = refl
      Iso.rightInv iso2 (inr x) i = inr (retEq eqFin x i)
      Iso.rightInv iso2 (push (a , x) i) j =
        hcomp (λ k → λ { (i = i0) → inl (wedgeMap-aux1 n (compPath→Square {p = λ i → secEq eqFin (eqFin .fst a) i}{refl}
                                                                          {λ i → eqFin .fst (retEq eqFin a i)}{refl}
                                                                          (cong (λ X → X ∙ refl) (commPathIsEq (eqFin .snd) a)) k j , x))
                       ; (i = i1) → inr (retEq eqFin a j)
                       ; (j = i0) → doubleCompPath-filler (λ i → inl (wedgeMap-aux1 n (secEq eqFin (eqFin .fst a) (~ i) , x)))
                                                          (push (invEq eqFin (eqFin .fst a) , x)) refl k i
                       ; (j = i1) → push (a , x) i })
              (push (retEq eqFin a j , x) i)

  wedgeEquiv : (n : ℕ) → ((fst C (suc n) , basepoint C c₀ n) ⋁ (fst D (suc n) , basepoint D d₀ n)) ≃ Pushout (wedgeMap n) fst
  wedgeEquiv zero = isoToEquiv wedgeIso₀
  wedgeEquiv (suc n) = isoToEquiv (wedgeIsoₛ n)

  wedgeSkel : CWskel ℓ
  wedgeSkel = wedgeA , wedgeCells , wedgeMap , (C .snd .snd .snd .fst) , wedgeEquiv
