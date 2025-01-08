{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.random where

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

open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.HITs.Wedge


open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.LES
open import Cubical.Homotopy.Loopspace

open import Cubical.HITs.Truncation as TR
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Subgroup

open import Cubical.Algebra.Group.Abelianization.Base
open import Hurewicz.Abelianization as Abi


AbelianizationIdempotent : ∀ {ℓ} (G : AbGroup ℓ)
  → AbGroupIso G (AbelianizationAbGroup (AbGroup→Group G))
Iso.fun (fst (AbelianizationIdempotent G)) = η
Iso.inv (fst (AbelianizationIdempotent G)) = Abi.rec _ (AbGroupStr.is-set (snd G))
  (idfun _)
  λ a b c → cong (AbGroupStr._+_ (snd G) a) (AbGroupStr.+Comm (snd G) _ _)
Iso.rightInv (fst (AbelianizationIdempotent G)) =
  Abi.elimProp _ (λ _ → isset _ _) (λ _ → refl)
Iso.leftInv (fst (AbelianizationIdempotent G)) x = refl
snd (AbelianizationIdempotent G) = snd (AbelianizationGroupStructure.ηAsGroupHom _)

bouquetFin1 : ∀ {ℓ} {B : Fin 1 → Pointed ℓ} → Iso (⋁gen (Fin 1) B) (B fzero .fst)
Iso.fun (bouquetFin1 {B = B}) (inl x) = B fzero .snd
Iso.fun bouquetFin1 (inr ((zero , tt) , p)) = p
Iso.fun (bouquetFin1 {B = B}) (push (zero , tt) i) = B fzero .snd
Iso.inv bouquetFin1 x = inr (fzero , x)
Iso.rightInv bouquetFin1 x = refl
Iso.leftInv bouquetFin1 (inl x) = sym (push fzero)
Iso.leftInv bouquetFin1 (inr ((zero , tt) , p)) = refl
Iso.leftInv bouquetFin1 (push (zero , tt) i) j = push fzero (~ j ∨ i)

-- todo: use to replace orginal
GroupHomπ≅π'PathP' : ∀ {ℓ ℓ'} (A : Pointed ℓ) (B : Pointed ℓ') (n m : ℕ)
  → GroupHom (πGr n A) (πGr m B) ≡ GroupHom (π'Gr n A) (π'Gr m B)
GroupHomπ≅π'PathP' A B n m i =
  GroupHom (fst (GroupPath _ _) (GroupIso→GroupEquiv (π'Gr≅πGr n A)) (~ i))
           (fst (GroupPath _ _) (GroupIso→GroupEquiv (π'Gr≅πGr m B)) (~ i))


Hom/ : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'}
  {G' : NormalSubgroup G} {H' : NormalSubgroup H}
  → (ϕ : GroupHom G H)
  → (ϕ' : (a b : _) (r : (G ~ G' .fst) (G' .snd) a b)
        → (H ~ H' .fst) (H' .snd) (fst ϕ a) (fst ϕ b))
  → GroupHom (G / G') (H / H')
fst (Hom/ ϕ ϕ') = SQ.elim (λ _ → squash/) ([_] ∘ fst ϕ) λ a b r → eq/ _ _ (ϕ' a b r)
snd (Hom/ ϕ ϕ') = makeIsGroupHom (SQ.elimProp2 (λ _ _ → squash/ _ _)
  λ _ _ → cong [_] (IsGroupHom.pres· (snd ϕ) _ _))

Hom/Iso : ∀ {ℓ ℓ'} {G : Group ℓ} {H : Group ℓ'}
  {G' : NormalSubgroup G} {H' : NormalSubgroup H}
  → (ϕ : GroupIso G H)
  → (ϕ' : (a b : _) (r : (G ~ G' .fst) (G' .snd) a b)
        → (H ~ H' .fst) (H' .snd) (Iso.fun (fst ϕ) a) (Iso.fun (fst ϕ) b))
     (ψ' : (a b : _) (r : (H ~ H' .fst) (H' .snd) a b)
        → (G ~ G' .fst) (G' .snd) (Iso.inv (fst ϕ) a) (Iso.inv (fst ϕ) b))
  → GroupIso (G / G') (H / H')
Iso.fun (fst (Hom/Iso ϕ ϕ' ψ')) = fst (Hom/ (GroupIso→GroupHom ϕ) ϕ')
Iso.inv (fst (Hom/Iso ϕ ϕ' ψ')) =
  fst (Hom/ (GroupIso→GroupHom (invGroupIso ϕ)) ψ')
Iso.rightInv (fst (Hom/Iso ϕ ϕ' ψ')) =
  SQ.elimProp (λ _ → squash/ _ _) (cong [_] ∘ Iso.rightInv (fst ϕ))
Iso.leftInv (fst (Hom/Iso ϕ ϕ' ψ')) =
  SQ.elimProp (λ _ → squash/ _ _) (cong [_] ∘ Iso.leftInv (fst ϕ))
snd (Hom/Iso ϕ ϕ' ψ') = snd (Hom/ (GroupIso→GroupHom ϕ) ϕ')

Hom/ImIso : ∀ {ℓ ℓ'} {G H : Group ℓ'} (ϕ : GroupHom G H)
                     {G' H' : Group ℓ} (ψ : GroupHom G' H')
                     {ϕ' : isNormal (imSubgroup ϕ)} {ψ' : isNormal (imSubgroup ψ)}
   (eG : GroupIso G G') (eH : GroupIso H H')
   (e~ : (g : fst G)
     → fst ψ (Iso.fun (fst eG) g) ≡
        Iso.fun (fst eH) (ϕ .fst g))
  → GroupIso (H / (_ , ϕ')) (H' / (_ , ψ'))
Hom/ImIso {G = G} {H} ϕ {G'} {H'} ψ eG eH e∼ = Hom/Iso eH
  (λ a b → PT.map (uncurry λ x p
    → (Iso.fun (fst eG) x) , e∼ x
    ∙ cong (Iso.fun (fst eH)) p
    ∙ IsGroupHom.pres· (snd eH) _ _
    ∙ cong₂ (GroupStr._·_ (snd H'))
      refl (IsGroupHom.presinv (snd eH) _)))
  λ a b → PT.map (uncurry λ x p
    → (Iso.inv (fst eG) x)
      , (sym ((cong₂ (GroupStr._·_ (snd H)) refl (sym (IsGroupHom.presinv (snd (invGroupIso eH)) b)) --
        ∙ sym (IsGroupHom.pres· (snd (invGroupIso eH)) a (GroupStr.inv (H' .snd) b))
        ∙ cong (Iso.inv (fst eH)) (sym p)
        ∙ cong (Iso.inv (fst eH) ∘ fst ψ) (sym (Iso.rightInv (fst eG) x)))
       ∙ cong (Iso.inv (fst eH)) (e∼ (Iso.inv (fst eG) x))
       ∙ Iso.leftInv (fst eH) _)))

module πLES' {ℓ ℓ' : Level} {A : Pointed ℓ} {B : Pointed ℓ'} (f : A →∙ B) where
  module M = πLES f
  fib : Pointed _
  fib = (fiber (fst f) (pt B)) , (pt A , snd f)

  fib→A : (n : ℕ) → GroupHom (π'Gr n fib) (π'Gr n A)
  fib→A n = π'∘∙Hom n (fst , refl)

  A→B : (n : ℕ) → GroupHom (π'Gr n A) (π'Gr n B)
  A→B n = π'∘∙Hom n f

  -- todo: improve
  B→fib : (n : ℕ) → GroupHom (π'Gr (suc n) B) (π'Gr n fib)
  B→fib n = transport (GroupHomπ≅π'PathP' B fib (suc n) n) (M.B→fib n)

  private
    P : (n : ℕ) → PathP (λ i → GroupHomπ≅π'PathP' B fib (suc n) n i)
                          (M.B→fib n) (B→fib n)
    P n = toPathP refl

  Ker-A→B⊂Im-fib→A : (n : ℕ) (x : π' (suc n) A)
    → isInKer (A→B n) x
    → isInIm (fib→A n) x
  Ker-A→B⊂Im-fib→A n =
    transport (λ i → (x : _) → isInKer (π∘∙A→B-PathP n f i) x
                              → isInIm (π∘∙fib→A-PathP n f i) x)
              (M.Ker-A→B⊂Im-fib→A n)

  Im-fib→A⊂Ker-A→B : (n : ℕ) (x : π' (suc n) A)
    → isInIm (fib→A n) x
    → isInKer (A→B n) x
  Im-fib→A⊂Ker-A→B n =
    transport (λ i → (x : _) → isInIm (π∘∙fib→A-PathP n f i) x
                              → isInKer (π∘∙A→B-PathP n f i) x)
              (M.Im-fib→A⊂Ker-A→B n)

  Ker-fib→A⊂Im-B→fib : (n : ℕ) (x : π' (suc n) fib)
    → isInKer (fib→A n) x
    → isInIm (B→fib n) x
  Ker-fib→A⊂Im-B→fib n =
    transport (λ i → (x : _) → isInKer (π∘∙fib→A-PathP n f i) x
                              → isInIm (P n i) x)
              (M.Ker-fib→A⊂Im-B→fib n)

  Im-B→fib⊂Ker-fib→A : (n : ℕ) (x : π' (suc n) fib)
    → isInIm (B→fib n) x
    → isInKer (fib→A n) x
  Im-B→fib⊂Ker-fib→A n =
    transport (λ i → (x : _) → isInIm (P n i) x
                              → isInKer (π∘∙fib→A-PathP n f i) x)
              (M.Im-B→fib⊂Ker-fib→A n)

  Im-A→B⊂Ker-B→fib : (n : ℕ) (x : π' (suc (suc n)) B)
    → isInIm (A→B (suc n)) x
    → isInKer (B→fib n) x
  Im-A→B⊂Ker-B→fib n =
    transport (λ i → (x : _) → isInIm (π∘∙A→B-PathP (suc n) f i) x
                              → isInKer (P n i) x)
              (M.Im-A→B⊂Ker-B→fib n)

  Ker-B→fib⊂Im-A→B : (n : ℕ) (x : π' (suc (suc n)) B)
    → isInKer (B→fib n) x
    → isInIm (A→B (suc n)) x
  Ker-B→fib⊂Im-A→B n =
    transport (λ i → (x : _) → isInKer (P n i) x
                              → isInIm (π∘∙A→B-PathP (suc n) f i) x)
              (M.Ker-B→fib⊂Im-A→B n)

isConnectedCofib : ∀ {ℓ} {A B : Type ℓ} (n : ℕ) {f : A → B}
  → isConnectedFun (suc n) f → isConnected (suc (suc n)) (cofib f)
isConnectedCofib n {f = f} cf =
  isConnectedPoint2 (suc n) (inl tt) (inlConnected (suc n) (λ _ → tt) f cf)

connectedFunPresConnected : ∀ {ℓ} {A B : Type ℓ} (n : ℕ) {f : A → B}
  → isConnected n B → isConnectedFun n f → isConnected n A
connectedFunPresConnected n {f = f} conB conf =
  isOfHLevelRetractFromIso 0 (connectedTruncIso n f conf) conB


normalFormCofibFun : ∀ {n m k : ℕ}
  (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
  (f : S₊∙ (suc n) →∙ (cofib (fst α) , inl tt))
  → ∃[ f' ∈ S₊∙ (suc n) →∙ SphereBouquet∙ (suc n) (Fin k) ]
      (((inr , (λ i → inr (α .snd (~ i))) ∙ sym (push (inl tt))) ∘∙ f') ≡ f)
normalFormCofibFun {n = n} {m} {k} α f =
  PT.rec squash₁
    (λ g → TR.rec (isProp→isOfHLevelSuc n squash₁)
      (λ gid → ∣ ((λ x → g x .fst) , (cong fst gid))
               , ΣPathP ((λ i x → g x .snd i)
               , (lem _ _ _ _ _ _ _ _ _ _ (cong snd gid))) ∣₁)
      (isConnectedPath (suc n)
        (help (fst f (ptSn (suc n)))) (g (ptSn (suc n)))
          ((inl tt) , (((λ i → inr (α .snd (~ i))) ∙ sym (push (inl tt))) ∙ sym (snd f))) .fst))
    makefun
  where
  lem : ∀ {ℓ} {A : Type ℓ} (x y : A) (inrgid : x ≡ y) (z : _) (inrα : y ≡ z) (w : _) (pushtt : z ≡ w)
    (t : _) (snf : w ≡ t) (s : x ≡ t)
    → Square s ((inrα ∙ pushtt) ∙ snf) inrgid refl
    → Square (inrgid ∙ inrα ∙ pushtt) (sym snf) s refl
  lem x = J> (J> (J> (J> λ s sq → (sym (lUnit _) ∙ sym (rUnit _))
    ◁ λ i j → (sq ∙ sym (rUnit _) ∙ sym (rUnit _)) j i)))
  cool : (x : S₊ (suc n)) → Type
  cool x =
    Σ[ x' ∈ SphereBouquet (suc n) (Fin k) ]
      Σ[ y ∈ ((ptSn (suc n) ≡ x) → inl tt ≡ x') ]
        Σ[ feq ∈ inr x' ≡ fst f x ]
          ((p : ptSn (suc n) ≡ x)
            → Square ((λ i → inr (snd α (~ i))) ∙ sym (push (inl tt))) (snd f)
                      ((λ i → inr (y p i)) ∙∙ feq ∙∙ cong (fst f) (sym p)) refl)

  inr' : SphereBouquet (suc n) (Fin k) → cofib (fst α)
  inr' = inr

  help : isConnectedFun (suc (suc n)) inr'
  help = inrConnected _ _ _ (isConnected→isConnectedFun _ isConnectedSphereBouquet')

  makefun : ∥ ((x : _) → Σ[ x' ∈ SphereBouquet (suc n) (Fin k) ] inr x' ≡ fst f x) ∥₁
  makefun = sphereToTrunc _ λ x → help (fst f x) .fst


connected→πEquiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 +ℕ n) (fst f)
  → GroupEquiv (πGr n A) (πGr n B)
connected→πEquiv {ℓ = ℓ}  {A = A} {B = B} n f conf =
  (πHom n f .fst
  , subst isEquiv (funExt (ST.elim (λ _ → isSetPathImplicit) (λ _ → refl)))
    (sss .snd))
  , πHom n f .snd
  where
  lem : (n : ℕ) → suc (suc n) ∸ n ≡ 2
  lem zero = refl
  lem (suc n) = lem n

  Bat : isConnectedFun 2 (fst (Ω^→ (suc n) f))
  Bat = subst (λ k → isConnectedFun k (fst (Ω^→ (suc n) f)))
              (lem n)
              (isConnectedΩ^→ (suc (suc n)) (suc n) f conf)

  sss : π (suc n) A ≃ π (suc n) B
  sss = compEquiv setTrunc≃Trunc2
         (compEquiv (connectedTruncEquiv 2
                     (fst (Ω^→ (suc n) f)) Bat)
          (invEquiv setTrunc≃Trunc2))

GroupHomπ≅π'PathP-hom : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (n : ℕ) (f : A →∙ B)
  → PathP (λ i → GroupHomπ≅π'PathP A B n i) (πHom n f) (π'∘∙Hom n f)
GroupHomπ≅π'PathP-hom {A = A} {B = B} n f =
  (λ j → transp (λ i → GroupHomπ≅π'PathP A B n (i ∧ j)) (~ j)
                 (πHom n f))
  ▷ Σ≡Prop (λ _ → isPropIsGroupHom _ _) (π'∘∙Hom'≡π'∘∙fun n f)

connected→π'Equiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 +ℕ n) (fst f)
  → GroupEquiv (π'Gr n A) (π'Gr n B)
fst (fst (connected→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf)) = π'∘∙Hom n f .fst
snd (fst (connected→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf)) =
  transport (λ i → isEquiv (GroupHomπ≅π'PathP-hom n f i .fst))
            (connected→πEquiv n f conf .fst .snd)
snd (connected→π'Equiv {ℓ = ℓ} {A = A} {B = B} n f conf) = π'∘∙Hom n f .snd


AbelianizationFun : ∀ {ℓ} {G : Group ℓ} {H : Group ℓ}
  → GroupHom G H → AbGroupHom (AbelianizationAbGroup G) (AbelianizationAbGroup H)
fst (AbelianizationFun {G = G} {H} ϕ) = Abi.rec _ isset (η ∘ fst ϕ) λ a b c
  → cong η (IsGroupHom.pres· (snd ϕ) a _
         ∙ cong₂ (GroupStr._·_ (snd H)) refl (IsGroupHom.pres· (snd ϕ) b c))
  ∙ comm _ _ _
  ∙ sym (cong η (IsGroupHom.pres· (snd ϕ) a _
         ∙ cong₂ (GroupStr._·_ (snd H)) refl (IsGroupHom.pres· (snd ϕ) c b)))
snd (AbelianizationFun {G = G} {H} ϕ) = makeIsGroupHom
  (Abi.elimProp2 _ (λ _ _ → isset _ _)
    λ a b → cong η (IsGroupHom.pres· (snd ϕ) a b))

AbelianizationEquiv : ∀ {ℓ} {G : Group ℓ} {H : Group ℓ}
  → GroupEquiv G H → AbGroupEquiv (AbelianizationAbGroup G) (AbelianizationAbGroup H)
fst (AbelianizationEquiv {G = G} {H} ϕ) = isoToEquiv main
  where
  main : Iso _ _
  Iso.fun main = fst (AbelianizationFun (GroupEquiv→GroupHom ϕ))
  Iso.inv main = fst (AbelianizationFun (GroupEquiv→GroupHom (invGroupEquiv ϕ)))
  Iso.rightInv main = Abi.elimProp _ (λ _ → isset _ _) λ g → cong η (secEq (fst ϕ) g)
  Iso.leftInv main = Abi.elimProp _ (λ _ → isset _ _) λ g → cong η (retEq (fst ϕ) g)
snd (AbelianizationEquiv {G = G} {H} ϕ) =
  snd (AbelianizationFun (fst (fst ϕ) , snd ϕ))

connected→Abπ'Equiv : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (3 +ℕ n) (fst f)
  → AbGroupEquiv (AbelianizationAbGroup (π'Gr n A)) (AbelianizationAbGroup (π'Gr n B))
connected→Abπ'Equiv n f isc = AbelianizationEquiv (connected→π'Equiv n f isc)

connected→πSurj : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (2 +ℕ n) (fst f)
  → isSurjective {G = πGr n A} {H = πGr n B} (πHom n f)
connected→πSurj {ℓ = ℓ}  {A = A} {B = B} n f conf =
  ST.elim (λ _ → isProp→isSet squash₁)
    λ p → TR.rec squash₁ (λ {(q , r) → ∣ ∣ q ∣₂ , (cong ∣_∣₂ r) ∣₁}) (Bat p .fst)
  where
  lem : (n : ℕ) → suc n ∸ n ≡ 1
  lem zero = refl
  lem (suc n) = lem n

  Bat : isConnectedFun 1 (fst (Ω^→ (suc n) f))
  Bat = subst (λ k → isConnectedFun k (fst (Ω^→ (suc n) f)))
              (lem n)
              (isConnectedΩ^→ (suc n) (suc n) f conf)

connected→π'Surj : ∀ {ℓ} {A B : Pointed ℓ} (n : ℕ) (f : A →∙ B)
  → isConnectedFun (2 +ℕ n) (fst f)
  → isSurjective (π'∘∙Hom n f)
connected→π'Surj n f conf =
  transport (λ i → isSurjective (GroupHomπ≅π'PathP-hom n f i))
            (connected→πSurj n f conf)

-- move to around pre∂ defn?
module _ {ℓ} (C : CWskel ℓ) (n : ℕ) (ptC : fst C (suc n))
         (α≡0 : (x : _) → CWskel-fields.α C (suc n) (x , ptSn n) ≡ ptC) where
  open preboundary C n
  open CWskel-fields C
  pre∂-alt : SphereBouquet n (Fin (preboundary.An+1 C n)) → SphereBouquet n (Fin (preboundary.An C n))
  pre∂-alt = fst (Bouquet≃-gen n An (α n) (e n))
            ∘ to_cofibCW n C ∘ λ { (inl x) → ptC
                                ; (inr x) → α (suc n) x
                                ; (push a i) → α≡0 a (~ i)}

Susp-pred∂ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (ptC : fst C (suc n))
       (ptCn : Fin (fst (C .snd) n))
       (α≡0 : (x : _) → CWskel-fields.α C (suc n) (x , ptSn n) ≡ ptC)
       (e≡ : CWskel-fields.e C n .fst ptC ≡ inr ptCn)
       (x : _) → preboundary.pre∂ C n x ≡ bouquetSusp→ (pre∂-alt C n ptC α≡0) x
Susp-pred∂ C zero ptC ptCn α≡0 e≡ (inl x) = refl
Susp-pred∂ C zero ptC ptCn α≡0 e≡ (inr (x , base)) = refl
Susp-pred∂ C zero ptC ptCn α≡0 e≡ (inr (x , loop i)) j = lem j i
  where
  open preboundary C zero
  open CWskel-fields C
  lem : cong (pre∂ ∘ inr ∘ (x ,_)) loop
      ≡ λ i → bouquetSusp→ (pre∂-alt C zero ptC α≡0) (inr (x , loop i))
  lem = cong (cong (isoSuspBouquet ∘ (suspFun isoCofBouquet)
           ∘ (suspFun (to_cofibCW 0 C))))
             (cong-∙∙ (δ 1 C) (push (αn+1 (x , false)))
             (λ i → inr (invEq (e 1) ((push (x , false) ∙ sym (push (x , true))) i)))
             (sym (push (αn+1 (x , true))))
             ∙ (λ j → (λ i → merid (αn+1 (x , false)) (i ∧ ~ j)) ∙∙
                    (λ i → merid (αn+1 (x , false)) (~ j ∨ i)) ∙∙ sym (merid (α 1 (x , true)))))
          ∙ (cong-∙ (isoSuspBouquet ∘ suspFun isoCofBouquet ∘ suspFun (to 0 cofibCW C))
             (merid (αn+1 (x , false))) (sym (merid (α 1 (x , true)))))
      ∙ sym (cong-∙ sphereBouquetSuspFun
               (merid (pre∂-alt C zero ptC α≡0 (inr (x , false))))
               (sym (merid (pre∂-alt C zero ptC α≡0 (inr (x , true))))))
      ∙ cong (cong (sphereBouquetSuspFun))
             ( sym (cong-∙ (suspFun (pre∂-alt C zero ptC α≡0))
                   (merid (inr (x , false))) (sym (merid (inr (x , true))))))
      ∙ cong (cong (sphereBouquetSuspFun ∘ (suspFun (pre∂-alt C zero ptC α≡0))))
             (sym (cong-∙ (Iso.inv (Iso-SuspBouquet-Bouquet (Fin An+1) λ _ → S₊∙ zero)
                         ∘ inr ∘ (x ,_))
                         (merid false) (sym (merid true))))
Susp-pred∂ C zero ptC ptCn α≡0 e≡ (push a i) = refl
Susp-pred∂ C (suc n) ptC ptCn α≡0 e≡ (inl x) = refl
Susp-pred∂ C (suc n) ptC ptCn α≡0 e≡ (inr (x , north)) = refl
Susp-pred∂ C (suc n) ptC ptCn α≡0 e≡ (inr (x , south)) = refl
Susp-pred∂ C (suc n) ptC ptCn α≡0 e≡ (inr (x , merid a i)) j = lem j i
  where
  open preboundary C (suc n)
  open CWskel-fields C
  F = isoSuspBouquet ∘ (suspFun isoCofBouquet)
           ∘ (suspFun (to_cofibCW (suc n) C))
  lem : cong (pre∂ ∘ inr ∘ (x ,_)) (merid a)
      ≡ λ i → bouquetSusp→ (pre∂-alt C (suc n) ptC α≡0) (inr (x , merid a i))
  lem = cong-∙∙ (F ∘ δ (suc (suc n)) C)
           (push (αn+1 (x , a)))
                    (λ i → inr (invEq (e (2 +ℕ n)) ((push (x , a) ∙ sym (push (x , ptSn (suc n)))) i)))
                    (sym (push (αn+1 (x , ptSn (suc n)))))
      ∙ cong₃ _∙∙_∙∙_ refl refl
              (cong (cong F) (cong (sym ∘ merid) (α≡0 x))
            ∙ cong (sym ∘ Bouquet→ΩBouquetSusp (Fin An) (λ _ → S₊∙ (suc n)))
                   (cong (Pushout→Bouquet (suc n) (snd C .fst (suc n))
                           (snd C .snd .fst (suc n)) (snd C .snd .snd .snd (suc n)))
                             e≡)
            ∙ cong sym ((λ i → push ptCn ∙∙ (λ j → inr (ptCn , rCancel (merid (ptSn (suc n))) i j)) ∙∙ sym (push ptCn)) ∙ ∙∙lCancel (sym (push ptCn))))
      ∙ sym (compPath≡compPath' _ _)
      ∙ sym (rUnit _)
Susp-pred∂ C (suc n) ptC ptCn α≡0 e≡ (push (x , y) i) = refl

module _ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
  (f1 : A → B) (f2 : B → C) {g : A → D} where
  PushoutComp→IteratedPushout : Pushout (f2 ∘ f1) g → Pushout {C = Pushout f1 g} f2 inl
  PushoutComp→IteratedPushout (inl x) = inl x
  PushoutComp→IteratedPushout (inr x) = inr (inr x)
  PushoutComp→IteratedPushout (push a i) = (push (f1 a) ∙ λ i → inr (push a i)) i

  IteratedPushout→PushoutComp : Pushout {C = Pushout f1 g} f2 inl → Pushout (f2 ∘ f1) g
  IteratedPushout→PushoutComp (inl x) = inl x
  IteratedPushout→PushoutComp (inr (inl x)) = inl (f2 x)
  IteratedPushout→PushoutComp (inr (inr x)) = inr x
  IteratedPushout→PushoutComp (inr (push a i)) = push a i
  IteratedPushout→PushoutComp (push a i) = inl (f2 a)

  Iso-PushoutComp-IteratedPushout : Iso (Pushout (f2 ∘ f1) g) (Pushout {C = Pushout f1 g} f2 inl)
  Iso.fun Iso-PushoutComp-IteratedPushout = PushoutComp→IteratedPushout
  Iso.inv Iso-PushoutComp-IteratedPushout = IteratedPushout→PushoutComp
  Iso.rightInv Iso-PushoutComp-IteratedPushout (inl x) = refl
  Iso.rightInv Iso-PushoutComp-IteratedPushout (inr (inl x)) = push x
  Iso.rightInv Iso-PushoutComp-IteratedPushout (inr (inr x)) = refl
  Iso.rightInv Iso-PushoutComp-IteratedPushout (inr (push a i)) j =
    compPath-filler' (push (f1 a)) (λ i₁ → inr (push a i₁)) (~ j) i
  Iso.rightInv Iso-PushoutComp-IteratedPushout (push a i) j = push a (i ∧ j)
  Iso.leftInv Iso-PushoutComp-IteratedPushout (inl x) = refl
  Iso.leftInv Iso-PushoutComp-IteratedPushout (inr x) = refl
  Iso.leftInv Iso-PushoutComp-IteratedPushout (push a i) j = T j i
    where
    T = cong-∙ IteratedPushout→PushoutComp (push (f1 a)) (λ i → inr (push a i))
      ∙ sym (lUnit _)


-- move to Wedge.Properties?
module _ {ℓ ℓ'} {A : Type ℓ} (B : A → Pointed ℓ')
  where
  cofibFst : Type _
  cofibFst = cofib {A = Σ A (fst ∘ B)} {B = A} fst

  cofibFst→⋁ : cofibFst → ⋁gen A λ a → Susp∙ (fst (B a))
  cofibFst→⋁ (inl x) = inl x
  cofibFst→⋁ (inr a) = inr (a , north)
  cofibFst→⋁ (push (a , b) i) = (push a ∙ λ i → inr (a , toSusp (B a) b i)) i

  ⋁→cofibFst : ⋁gen A (λ a → Susp∙ (fst (B a))) → cofibFst
  ⋁→cofibFst (inl x) = inl x
  ⋁→cofibFst (inr (x , north)) = inl tt
  ⋁→cofibFst (inr (x , south)) = inr x
  ⋁→cofibFst (inr (x , merid a i)) = push (x , a) i
  ⋁→cofibFst (push a i) = inl tt

  Iso-cofibFst-⋁ : Iso cofibFst (⋁gen A (λ a → Susp∙ (fst (B a))))
  Iso.fun Iso-cofibFst-⋁ = cofibFst→⋁
  Iso.inv Iso-cofibFst-⋁ = ⋁→cofibFst
  Iso.rightInv Iso-cofibFst-⋁ (inl x) = refl
  Iso.rightInv Iso-cofibFst-⋁ (inr (x , north)) = push x
  Iso.rightInv Iso-cofibFst-⋁ (inr (x , south)) i = inr (x , merid (pt (B x)) i)
  Iso.rightInv Iso-cofibFst-⋁ (inr (x , merid a i)) j =
    hcomp (λ k → λ {(i = i0) → push x (j ∨ ~ k)
                   ; (i = i1) → inr (x , merid (pt (B x)) j)
                   ; (j = i0) → compPath-filler' (push x)
                                   (λ i₁ → inr (x , toSusp (B x) a i₁)) k i
                   ; (j = i1) → inr (x , merid a i)})
          (inr (x , compPath-filler (merid a) (sym (merid (pt (B x)))) (~ j) i))
  Iso.rightInv Iso-cofibFst-⋁ (push a i) j = push a (i ∧ j)
  Iso.leftInv Iso-cofibFst-⋁ (inl x) = refl
  Iso.leftInv Iso-cofibFst-⋁ (inr x) = push (x , snd (B x))
  Iso.leftInv Iso-cofibFst-⋁ (push (a , b) i) j = help j i
    where
    help : Square (cong ⋁→cofibFst ((push a ∙ λ i → inr (a , toSusp (B a) b i))))
                  (push (a , b)) refl (push (a , (snd (B a))))
    help = (cong-∙ ⋁→cofibFst (push a) (λ i → inr (a , toSusp (B a) b i))
         ∙ sym (lUnit _)
         ∙ cong-∙ (⋁→cofibFst ∘ inr ∘ (a ,_)) (merid b) (sym (merid (snd (B a)))))
         ◁ λ i j → compPath-filler (push (a , b)) (sym (push (a , pt (B a)))) (~ i) j

{-
  cofibFst : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Iso (cofib {A = A × B} {B = A} fst) (⋁gen A λ _ → Susp∙ B)
  Iso.fun cofibFst (inl x) = inl x
  Iso.fun cofibFst (inr x) = inr (x , north)
  Iso.fun cofibFst (push (a , b) i) = (push a ∙ λ j → inr (a , {!toSusp B !})) i
  Iso.inv cofibFst = {!!}
  Iso.rightInv cofibFst = {!!}
  Iso.leftInv cofibFst = {!!}
-}


-- delete?
module falseDichotomies where
  lt-eq : {n m : ℕ} → ¬ m <ᵗ n × (m ≡ suc n)
  lt-eq {n = n} (p , q) = ¬-suc-n<ᵗn (subst (_<ᵗ n) q p)

  lt-gt : {n m : ℕ}  → ¬ m <ᵗ n × (suc n <ᵗ m)
  lt-gt (p , q) = ¬-suc-n<ᵗn (<ᵗ-trans q p)

  eq-eq : {n m : ℕ} → ¬ (m ≡ n) × (m ≡ suc n)
  eq-eq {n = n} (p , q) = ¬m<ᵗm (subst (_<ᵗ suc n) (sym p ∙ q) <ᵗsucm)

  eq-gt : {n m : ℕ} → ¬ (m ≡ n) × (suc n <ᵗ m)
  eq-gt (p , q) = lt-eq (q , cong suc (sym p))

  gt-lt : {n m : ℕ} → ¬ (n <ᵗ m) × (m <ᵗ suc n)
  gt-lt = ¬squeeze

-- subComplexIncl : ∀ {ℓ} (C : CWskel ℓ) → {!!}
-- subComplexIncl = {!!}

-- CW↑' : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) →  m <ᵗ n → fst C m → fst C n
-- CW↑' C zero (suc n) p q = ⊥.rec (C .snd .snd .snd .fst q)
-- CW↑' C (suc m) (suc n) p x with (n ≟ᵗ suc m)
-- ... | gt s = CW↪ C n (CW↑ C (suc m) n s x)
-- ... | eq q = CW↪ C n (subst (fst C) (sym q) x)
-- ... | lt s = ⊥.rec (¬squeeze (p , s))

-- TrichotomyᵗSucR : {n m : ℕ} →  Trichotomyᵗ n m → Trichotomyᵗ n (suc m)
-- TrichotomyᵗSucR {n = n} {m} (lt x) = {!lt ?!}
-- TrichotomyᵗSucR {n = n} {m} (eq x) = {!!}
-- TrichotomyᵗSucR {n = n} {m} (gt x) = {!!}


open import Cubical.CW.Properties
open import Hurewicz.SnNew


-- Sn approx
Sn→SfamGen : ∀ {n k : ℕ} (p : Trichotomyᵗ k (suc n))
  → 0 <ᵗ k → S₊ n → Sgen.Sfam n k p
Sn→SfamGen {n = n} {suc k} (lt x₁) _ x = tt
Sn→SfamGen {n = n} {suc k} (eq x₁) _ x = x
Sn→SfamGen {n = n} {suc k} (gt x₁) _ x = x

Sn→SfamGen∙ : ∀ {n k : ℕ} (p : Trichotomyᵗ (suc k) (suc n))
  → Sn→SfamGen p tt (ptSn n) ≡ Sgen.Sfam∙ n k p
Sn→SfamGen∙ (lt x) = refl
Sn→SfamGen∙ (eq x) = refl
Sn→SfamGen∙ (gt x) = refl

{- {suc k} p with  (k ≟ᵗ n)
... | lt x = λ _ → tt
... | eq x = idfun _
... | gt x = idfun _
-}
CWskel∙ : ∀ {ℓ} (X : CWskel ℓ) → fst X 1 → (n : ℕ) → fst X (suc n)
CWskel∙ X x zero = x
CWskel∙ X x (suc n) = CW↪ X (suc n) (CWskel∙ X x n)

CWskel∞∙ : ∀ {ℓ} (X : CWskel ℓ) → fst X 1 → (n : ℕ) → realise X
CWskel∞∙ X x₀ n = incl (CWskel∙ X x₀ n)

CWskel∞∙Id : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) (n : ℕ) → CWskel∞∙ X x₀ n ≡ incl x₀
CWskel∞∙Id X x₀ zero = refl
CWskel∞∙Id X x₀ (suc n) = sym (push (CWskel∙ X x₀ n)) ∙ CWskel∞∙Id X x₀ n

incl∙ : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) {n : ℕ}
  → (fst X (suc n) , CWskel∙ X x₀ n) →∙ (realise X , incl x₀)
fst (incl∙ X x₀ {n = n}) = incl
snd (incl∙ X x₀ {n = n}) = CWskel∞∙Id X x₀ n

CWskel∙Gen : ∀ {ℓ} (X : CWskel ℓ) → fst X 1 → (n m : ℕ) (p : _)
  → G.subComplexFam X (suc m) (suc n) p
CWskel∙Gen X x₀ n m (lt x) = CWskel∙ X x₀ n
CWskel∙Gen X x₀ n m (eq x) = CWskel∙ X x₀ n
CWskel∙Gen X x₀ n m (gt x) = CWskel∙ X x₀ m

CWskel∙Gen≡CWskel∙ : ∀ {ℓ} (X : CWskel ℓ) (x : fst X 1) → (n m : ℕ)
  → CWskel∙Gen X x n (suc m) (suc n ≟ᵗ suc (suc m))
   ≡ CWskel∙ (subComplex X (suc (suc m))) x n
CWskel∙Gen≡CWskel∙ X x zero m = refl
CWskel∙Gen≡CWskel∙ X x (suc n) m =
  lem _ _
  ∙ cong (CW↪ (subComplex X (suc (suc m))) (suc n))
         (CWskel∙Gen≡CWskel∙ X x n m)
  where
  lem : (p : _) (q : _) → CWskel∙Gen X x (suc n) (suc m) p
      ≡ invEq (G.subComplexFam≃Pushout X (suc (suc m)) (suc n) q p)
         (inl (CWskel∙Gen X x n (suc m) q))
  lem (lt x) (lt x₁) = refl
  lem (lt x) (eq x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc m)) x₁ (<ᵗ-trans <ᵗsucm x)))
  lem (lt x) (gt x₁) = ⊥.rec (¬squeeze (x , <ᵗ-trans x₁ (<ᵗ-trans <ᵗsucm <ᵗsucm)))
  lem (eq x) (lt x₁) = refl
  lem (eq x) (eq x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) (x₁ ∙ sym x) <ᵗsucm))
  lem (eq x) (gt x₁) = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ suc n) (sym x) x₁))
  lem (gt x) (lt x₁) = ⊥.rec (¬squeeze (x₁ , x))
  lem (gt y) (eq z) = ((λ j → transp (λ i → fst X (suc (predℕ (z (~ j ∨ i))))) (~ j)
                                 (CWskel∙ X x (predℕ (z (~ j))))))
                     ∙ cong (λ p → subst (fst X) p (CWskel∙ X x n)) (isSetℕ _ _ _ z)
                     ∙ sym (transportRefl _)
  lem (gt x) (gt x₁) = refl

CWskel∙GenSubComplex : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) {n m : ℕ} (t : m <ᵗ suc (suc n))
  (p : _)
  → CWskel∙Gen X x₀ m (suc n) p
  ≡ subComplexMapGen.subComplex←map' X (suc (suc n)) (suc m) t p (CWskel∙ X x₀ m)
CWskel∙GenSubComplex X x₌ t (lt x) = refl
CWskel∙GenSubComplex X x₌ t (eq x) = refl
CWskel∙GenSubComplex X x₌ t (gt x) = ⊥.rec (¬squeeze (x , t))

CWskel∙SubComplex : ∀ {ℓ} (X : CWskel ℓ) (x₀ : fst X 1) {n m : ℕ} (t : m <ᵗ suc (suc n))
  → CWskel∙ (subComplex X (suc (suc n))) x₀ m
   ≡ fst (complex≃subcomplex' X (suc (suc n)) (suc m) t
           (suc m ≟ᵗ suc (suc n))) (CWskel∙ X x₀ m)
CWskel∙SubComplex X x₀ t  =
  sym (CWskel∙Gen≡CWskel∙ X x₀ _ _) ∙ CWskel∙GenSubComplex X x₀ t _

<ᵗ→0<ᵗ : {n m : ℕ} → n <ᵗ m → 0 <ᵗ m
<ᵗ→0<ᵗ {n} {suc m} _ = tt

module _ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
  (f : S₊ n → fst X (suc n))
  (f₀ : f (ptSn n) ≡ CWskel∙ X x₀ n) where
  makeFinSequenceMapGen : ∀ k → (p : _) → Sgen.Sfam n k p → fst X k
  makeFinSequenceMapGen (suc k) (lt x₁) x = CWskel∙ X x₀ k
  makeFinSequenceMapGen (suc k) (eq x₁) x = subst (fst X) (sym x₁) (f x)
  makeFinSequenceMapGen (suc k) (gt x₁) x =
    CW↪ X k (makeFinSequenceMapGen k (k ≟ᵗ suc n) (Sn→SfamGen _ (<ᵗ→0<ᵗ x₁) x))

  makeFinSequenceMapGen∙ : ∀ k → (p : _) → makeFinSequenceMapGen (suc k) p (Sgen.Sfam∙ n k p) ≡ CWskel∙ X x₀ k
  makeFinSequenceMapGen∙ k (lt x) = refl
  makeFinSequenceMapGen∙ k (eq x) =
    cong₂ (λ p q → subst (fst X) p q) (isSetℕ _ _ _ _) f₀ ∙ H _ (cong predℕ x)
    where
    H : (n : ℕ) (x : k ≡ n)
      → subst (fst X) (cong suc (sym x)) (CWskel∙ X x₀ n) ≡ CWskel∙ X x₀ k
    H = J> transportRefl _
  makeFinSequenceMapGen∙ (suc k) (gt x) =
    cong (CW↪ X (suc k))
      (cong (makeFinSequenceMapGen (suc k) (Trichotomyᵗ-suc (k ≟ᵗ n)))
            (Sn→SfamGen∙ (Trichotomyᵗ-suc (k ≟ᵗ n)))
      ∙ makeFinSequenceMapGen∙ k (suc k ≟ᵗ suc n))

  makeFinSequenceMapComm : (k : ℕ) (p : _) (q : _) (x : _)
    → makeFinSequenceMapGen (suc k) p (invEq (SαEqGen n k p q) (inl x))
    ≡ CW↪ X k (makeFinSequenceMapGen k q x)
  makeFinSequenceMapComm (suc k) (lt x₁) (lt x₂) x = refl
  makeFinSequenceMapComm (suc k) (lt x₁) (eq x₂) x =
    ⊥.rec (¬-suc-n<ᵗn (subst (suc k <ᵗ_) (cong predℕ (sym x₂)) x₁))
  makeFinSequenceMapComm (suc k) (lt x₁) (gt x₂) x =
    ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x₁ x₂))
  makeFinSequenceMapComm (suc k) (eq x₁) (lt x₂) x =
    cong (subst (fst X) (sym x₁) ∘ f) (invEqSαEqGen∙ n k _ _)
    ∙ makeFinSequenceMapGen∙ (suc k) (eq x₁)
  makeFinSequenceMapComm k (eq x₁) (eq x₂) x =
    ⊥.rec (falseDichotomies.eq-eq (refl , sym (x₁ ∙ sym x₂)))
  makeFinSequenceMapComm k (eq x₁) (gt x₂) x =
    ⊥.rec (¬-suc-n<ᵗn {n} (subst (suc (suc n) <ᵗ_) x₁ x₂))
  makeFinSequenceMapComm k (gt x₁) (lt x₂) x = ⊥.rec (¬squeeze (x₁ , x₂))
  makeFinSequenceMapComm (suc k) (gt x₁) (eq x₂) x with (k ≟ᵗ n)
  ... | lt x₃ = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (cong predℕ x₂) x₃))
  ... | eq x₃ = cong (CW↪ X (suc k))
    (cong (subst (fst X) (cong suc (sym x₃))) (cong f (lem n x x₁ x₂))
    ∙ cong (λ p → subst (fst X) p (f x)) (isSetℕ _ _ (cong suc (sym x₃)) (sym x₂)))
    where
    lem : (n : ℕ) (x : _) (x₁ : _) (x₂ : _)
      → invEq (SαEqGen n (suc k) (gt x₁) (eq x₂)) (inl x) ≡ x
    lem zero x x₁ x₂ = refl
    lem (suc n) x x₁ x₂ = refl
  ... | gt x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) (cong predℕ  x₂) x₃))
  makeFinSequenceMapComm (suc k) (gt x₁) (gt x₂) x with k ≟ᵗ n
  ... | lt x₃ = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₂ x₃))
  ... | eq x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₃ x₂))
  ... | gt x₃ =
    cong (CW↪ X (suc k))
       (cong (CW↪ X k ∘ makeFinSequenceMapGen k (k ≟ᵗ suc n))
         (cong (λ w → Sn→SfamGen (k ≟ᵗ suc n) (<ᵗ→0<ᵗ w)
           (invEq (SαEqGen n (suc k) (gt x₁) (gt x₂)) (inl x))) (isProp<ᵗ x₃ x₂)
       ∙ cong (Sn→SfamGen (k ≟ᵗ suc n) (<ᵗ→0<ᵗ x₂))
          (lem n k x₁ x₂ x (k ≟ᵗ suc n)))
      ∙ makeFinSequenceMapComm k (gt x₂) (k ≟ᵗ suc n) _)
      where
      lem : (n k : ℕ) (x₁ : _) (x₂ : _) (x : _) (w : _)
        → invEq (SαEqGen n (suc k) (gt x₁) (gt x₂)) (inl x) ≡
                         invEq (SαEqGen n k (gt x₂) w)
                         (inl (Sn→SfamGen w (<ᵗ→0<ᵗ x₂) x))
      lem n k x₁ x₂ x (lt x₃) = ⊥.rec (¬squeeze (x₂ , x₃))
      lem zero (suc k) x₁ x₂ x (eq x₃) = refl
      lem (suc n) (suc k) x₁ x₂ x (eq x₃) = refl
      lem zero (suc k) x₁ x₂ x (gt x₃) = refl
      lem (suc n) (suc k) x₁ x₂ x (gt x₃) = refl

  niceCellMapS : cellMap (Sˢᵏᵉˡ n) X
  SequenceMap.map niceCellMapS k = makeFinSequenceMapGen k (k ≟ᵗ suc n)
  SequenceMap.comm niceCellMapS k x =
    sym (makeFinSequenceMapComm k (suc k ≟ᵗ suc n) (k ≟ᵗ suc n) x)

approxSphereMap∙ : ∀ {ℓ} (Xsk : CWskel ℓ) → (x₀ : fst Xsk (suc zero)) (n : ℕ)
  (f : S₊∙ (suc n) →∙ (realise Xsk , incl x₀))
  → ∃[ f' ∈ S₊∙ (suc n) →∙ (fst Xsk (suc (suc n)) , CWskel∙ Xsk x₀ (suc n)) ]
      (incl∙ Xsk x₀ ∘∙ f' ≡ f)
approxSphereMap∙ Xsk x₀ n f = PT.rec squash₁
                (λ F → TR.rec squash₁ (λ fp → ∣ ((λ x → F x .fst .fst) , sym (cong fst fp))
                  , ΣPathP ((funExt (λ x → F x .fst .snd))
                  , (SQ' _ _ _ _ _ _ _ _ (cong snd fp))) ∣₁)
                (F (ptSn (suc n)) .snd refl))
                approx'
 where
 SQ' : ∀ {ℓ} {A : Type ℓ} (x y : A) (p : x ≡ y) (z : A) (q : y ≡ z) (w : A) (r : x ≡ w) (t :  w ≡ z)
   → Square (p ∙ q) t r refl → Square (sym r ∙ p) (sym q)  t refl
 SQ' x = J> (J> (J> λ t s → sym (rUnit refl) ◁ λ i j → (rUnit refl ◁ s) (~ j) i))
 approx' : ∥ ((x : S₊ (suc n)) → Σ[ fb ∈ fiber (CW↪∞ Xsk (suc (suc n))) (fst f x) ]
               ((p : ptSn (suc n) ≡ x)
             → hLevelTrunc 1 (PathP (λ i → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
                 ((CWskel∙ Xsk x₀ (suc n)) , (CWskel∞∙Id Xsk x₀ (suc n) ∙ sym (snd f))) fb))) ∥₁
 approx' = sphereToTrunc (suc n)
   {λ x → Σ[ fb ∈ fiber (CW↪∞ Xsk (suc (suc n))) (fst f x) ]
               ((p : ptSn (suc n) ≡ x)
             → hLevelTrunc 1 (PathP (λ i → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
                 ((CWskel∙ Xsk x₀ (suc n)) , (CWskel∞∙Id Xsk x₀ (suc n) ∙ sym (snd f))) fb) )}
     λ a → TR.rec (isOfHLevelTrunc (suc (suc n)))
     (λ fa → ∣ fa , (λ p → J (λ a p → (fa : fiber (CW↪∞ Xsk (suc (suc n))) (fst f a))
                    → hLevelTrunc 1 (PathP (λ i → fiber (CW↪∞ Xsk (suc (suc n))) (fst f (p i)))
                        (CWskel∙ Xsk x₀ (suc n) , CWskel∞∙Id Xsk x₀ (suc n) ∙ (λ i → snd f (~ i))) fa))
                        (λ fa → isConnectedPathP 1 (isConnectedSubtr' n 2
                          (isConnected-CW↪∞ (suc (suc n)) Xsk (fst f (ptSn (suc n))))) _ _ .fst) p fa) ∣ₕ)
     (isConnected-CW↪∞ (suc (suc n)) Xsk (fst f a) .fst)


module _ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
  (fap : S₊∙ n →∙ (fst X (suc n) , CWskel∙ X x₀ n))
  (f : S₊∙ n →∙ (realise X , incl x₀))
  (fap≡ : (x : _) → incl {n = suc n} (fst fap x) ≡ fst f x) where

  betterApprox : cellMap (Sˢᵏᵉˡ n) X
  betterApprox = niceCellMapS X n x₀ (fst fap) (snd fap)

  isApprox : realiseSequenceMap betterApprox ≡ fst f ∘ invEq (isCWSphere n .snd)
  isApprox = funExt λ x → cong (realiseSequenceMap betterApprox) (sym (secEq (isCWSphere n .snd) x))
                         ∙ lem _
    where
    lem : (x : _) → realiseSequenceMap betterApprox (fst (isCWSphere n .snd) x) ≡ fst f x
    lem x with (n ≟ᵗ n)
    ... | lt x₁ = ⊥.rec (¬m<ᵗm x₁)
    ... | eq x₁ = cong (incl {n = suc n})
                  (cong (λ p → subst (fst X) p (fst fap x))
                   (isSetℕ _ _ _ refl)
                ∙ transportRefl (fst fap x)) ∙ fap≡ x
    ... | gt x₁ = ⊥.rec (¬m<ᵗm x₁)

  betterFinCellApproxS : (k : ℕ) → finCellApprox (Sˢᵏᵉˡ n) X (fst f ∘ invEq (isCWSphere n .snd)) k
  FinSequenceMap.fmap (fst (betterFinCellApproxS k)) = SequenceMap.map betterApprox ∘ fst
  FinSequenceMap.fcomm (fst (betterFinCellApproxS k)) = SequenceMap.comm betterApprox ∘ fst
  snd (betterFinCellApproxS k) = →FinSeqColimHomotopy _ _
    (funExt⁻ isApprox ∘ FinSeqColim→Colim k ∘ (fincl flast))


sphereFunIso : ∀ {ℓ} {A : Pointed ℓ} (n : ℕ)
  → Iso (S₊∙ n →∙ Ω A) (S₊∙ (suc n) →∙ A)
sphereFunIso zero = compIso IsoBool→∙ (invIso (IsoSphereMapΩ 1))
sphereFunIso (suc n) = ΩSuspAdjointIso

∙Π∘∙ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'}
  (n : ℕ) (f g : S₊∙ (suc n) →∙ A) (h : A →∙ B)
  → h ∘∙ ∙Π f g ≡ ∙Π (h ∘∙ f) (h ∘∙ g)
∙Π∘∙ {A = A} n f g h =
     cong (h ∘∙_) (cong₂ ∙Π (sym (Iso.rightInv (sphereFunIso n) f))
                            (sym (Iso.rightInv (sphereFunIso n) g)))
  ∙∙ le n (Iso.inv (sphereFunIso n) f) (Iso.inv (sphereFunIso n) g)
  ∙∙ cong₂ (λ f g → ∙Π (h ∘∙ f) (h ∘∙ g))
           (Iso.rightInv (sphereFunIso n) f)
           (Iso.rightInv (sphereFunIso n) g)
  where


  lem : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) → Square p refl (refl ∙ p) refl
  lem p = lUnit p ◁ λ i j → (refl ∙ p) (i ∨ j)

  mainEq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (a : A) (b : B)
    (fp : f a ≡ b) (l1 l2 : a ≡ a)
    → Square (cong f ((l1 ∙ refl) ∙ (l2 ∙ refl)))
             ((sym (refl ∙ fp) ∙∙ cong f l1 ∙∙ (refl ∙ fp))
            ∙ (sym (refl ∙ fp) ∙∙ cong f l2 ∙∙ (refl ∙ fp)))
              fp fp
  mainEq f a = J> λ l1 l2 → cong-∙ f _ _
    ∙ cong₂ _∙_ (cong-∙ f l1 refl  ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
                (cong-∙ f l2 refl ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))

  le : (n : ℕ) (f g : S₊∙ n →∙ Ω A)
    → (h ∘∙ ∙Π (Iso.fun (sphereFunIso n) f) (Iso.fun (sphereFunIso n) g))
    ≡ ∙Π (h ∘∙ Iso.fun (sphereFunIso n) f) (h ∘∙ Iso.fun (sphereFunIso n) g)
  fst (le zero f g i) base = snd h i
  fst (le zero f g i) (loop i₁) = mainEq (fst h) _ _ (snd h) (fst f false) (fst g false) i i₁
  fst (le (suc n) f g i) north = snd h i
  fst (le (suc n) f g i) south = snd h i
  fst (le (suc n) f g i) (merid a i₁) =
    mainEq (fst h) _ _ (snd h)
      (cong (Iso.fun (sphereFunIso (suc n)) f .fst) (σS a))
      (cong (Iso.fun (sphereFunIso (suc n)) g .fst) (σS a)) i i₁
  snd (le zero f g i) j = lem (snd h) j i
  snd (le (suc n) f g i) j = lem (snd h) j i

niceCellMapS∙Π : ∀ {ℓ} (X : CWskel ℓ) (n : ℕ) (x₀ : fst X 1)
  (fap gap : S₊∙ (suc n) →∙ (fst X (suc (suc n)) , CWskel∙ X x₀ (suc n)))
  (f : S₊∙ (suc n) →∙ (realise X , incl x₀))
  (fap≡ : incl∙ X x₀ ∘∙ fap ≡ f)
  (g : S₊∙ (suc n) →∙ (realise X , incl x₀))
  (gap≡ : incl∙ X x₀ ∘∙ gap ≡ g)
  → realiseCellMap (betterApprox X (suc n) x₀ (∙Π fap gap) (∙Π f g)
      (λ x → funExt⁻ (cong fst (∙Π∘∙ n fap gap (incl∙ X x₀))) x
            ∙ λ i → ∙Π (fap≡ i) (gap≡ i) .fst x))
    ≡ (∙Π f g .fst ∘ invEq (isCWSphere (suc n) .snd))
niceCellMapS∙Π X n x₀ fap gap =
  J> (J> funExt λ x → cong h (sym (secEq (isCWSphere (suc n) .snd) x))
                     ∙ main _
                     ∙ cong (∙Π (incl∙ X x₀ ∘∙ fap) (incl∙ X x₀ ∘∙ gap) .fst)
                         (retEq (SfamTopElement (suc n)) _))
  where
  h = realiseCellMap (betterApprox X (suc n) x₀
      (∙Π fap gap) (∙Π (incl∙ X x₀ ∘∙ fap) (incl∙ X x₀ ∘∙ gap))
      (λ x → (funExt⁻ (cong fst (∙Π∘∙ n fap gap (incl∙ X x₀))) x) ∙ refl))

  main : (x : Sgen.Sfam (suc n) (suc (suc n)) (suc (suc n) ≟ᵗ suc (suc n)))
       → h (incl {n = suc (suc n)} x)
       ≡ ∙Π (incl∙ X x₀ ∘∙ fap) (incl∙ X x₀ ∘∙ gap) .fst (invEq (SfamTopElement (suc n)) x)
  main with (n ≟ᵗ n)
  ... | lt x = ⊥.rec (¬m<ᵗm x)
  ... | eq x = λ x
    → cong (incl {n = suc (suc n)})
         (cong (λ p → subst (fst X) p (fst (∙Π fap gap) x)) (isSetℕ _ _ _ refl)
          ∙ transportRefl _)
      ∙ funExt⁻ (cong fst (∙Π∘∙ n fap gap (incl∙ X x₀))) x
  ... | gt x = ⊥.rec (¬m<ᵗm x)


--------------------------------------------




isPropTrichotomyᵗ : ∀ {n m : ℕ} → isProp (Trichotomyᵗ n m)
isPropTrichotomyᵗ {n = n} {m = m} (lt x) (lt x₁) i = lt (isProp<ᵗ x x₁ i)
isPropTrichotomyᵗ {n = n} {m = m} (lt x) (eq x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) x₁ x))
isPropTrichotomyᵗ {n = n} {m = m} (lt x) (gt x₁) = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ x))
isPropTrichotomyᵗ {n = n} {m = m} (eq x) (lt x₁) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) x x₁))
isPropTrichotomyᵗ {n = n} {m = m} (eq x) (eq x₁) i = eq (isSetℕ n m x x₁ i)
isPropTrichotomyᵗ {n = n} {m = m} (eq x) (gt x₁) =
  ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (sym x) x₁))
isPropTrichotomyᵗ {n = n} {m = m} (gt x) (lt x₁) = ⊥.rec (¬m<ᵗm (<ᵗ-trans x₁ x))
isPropTrichotomyᵗ {n = n} {m = m} (gt x) (eq x₁) =
  ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (sym x₁) x))
isPropTrichotomyᵗ {n = n} {m = m} (gt x) (gt x₁) i = gt (isProp<ᵗ x x₁ i)



CW↪CommSubComplex : ∀ {ℓ} (C : CWskel ℓ) (m k : ℕ) →
    CW↪ C m ∘ subComplex→map C k m
  ≡ subComplex→map C k (suc m) ∘ CW↪ (subComplex C k) m
CW↪CommSubComplex C m k with (m ≟ᵗ k) | (suc m ≟ᵗ k)
... | lt x | lt x₁ = refl
... | lt x | eq x₁ = refl
... | lt x | gt x₁ = ⊥.rec (¬squeeze (x , x₁))
... | eq x | lt x₁ = (⊥.rec (¬m<ᵗm (subst (_<ᵗ k) x (<ᵗ-trans <ᵗsucm x₁))))
... | eq x | eq x₁ = (⊥.rec (¬m<ᵗm (subst (_<ᵗ_ m) (x₁ ∙ (λ i → x (~ i))) <ᵗsucm)))
... | eq x | gt x₁ = funExt λ s → help _ _ x x₁ s (suc m ≟ᵗ suc k)
  where
  help : (m : ℕ) (k : ℕ) (x : m ≡ k) (x₁ : k <ᵗ suc m) (s : fst C m) (p : _)
    →  CW↪ C m s ≡ CW↑Gen C k (suc m) p x₁ (transport refl (subst (fst C) x s))
  help zero = λ k x y s → ⊥.rec (CW₀-empty C s)
  help (suc m) = J> λ x₁ s
    → λ { (lt x) → ⊥.rec (¬squeeze (x₁ , x))
         ; (eq x) → cong (CW↪ C (suc m)) (sym (transportRefl s)
              ∙ λ i → subst (fst C) (isSetℕ _ _ refl (cong predℕ (sym x)) i)
                      (transportRefl (transportRefl s (~ i)) (~ i)))
         ; (gt x) → ⊥.rec (¬m<ᵗm x) }
... | gt x | lt x₁ = ⊥.rec (¬squeeze (x₁ , <ᵗ-trans x (<ᵗ-trans <ᵗsucm <ᵗsucm)))
... | gt x | eq x₁ =
  ⊥.rec (¬m<ᵗm (transp (λ i → k <ᵗ x₁ i) i0 (<ᵗ-trans x <ᵗsucm)))
... | gt x | gt x₁ = funExt λ a → help _ _ x x₁ (suc m ≟ᵗ suc k) a
  where
  help : (m k : ℕ) (x : k <ᵗ m) (x₁ : k <ᵗ suc m) (p : _) (a : _)
    → CW↪ C m (CW↑Gen C k m  (m ≟ᵗ suc k) x a) ≡ CW↑Gen C k (suc m) p x₁ a
  help (suc m) zero x x₁ p a = ⊥.rec (C .snd .snd .snd .fst a)
  help (suc m) (suc k) x x₁ (lt x₂) a = ⊥.rec (¬squeeze (x₁ , x₂))
  help (suc m) (suc k) x x₁ (eq x₂) a =
    ⊥.rec (¬m<ᵗm (subst (_<ᵗ m) (sym (cong (predℕ ∘ predℕ) x₂)) x))
  help (suc m) (suc k) x x₁ (gt x₂) a =
    cong (CW↪ C (suc m))
      λ i → CW↑Gen C (suc k) (suc m)
              (Trichotomyᵗ-suc (m ≟ᵗ suc k)) (isProp<ᵗ x x₂ i) a

CW↪SubComplexCharac : ∀ {ℓ} (C : CWskel ℓ) (m k : ℕ) (q : m <ᵗ k) →
    CW↪ (subComplex C k) m ≡ invEq (subComplex→Equiv C k (suc m) q) ∘ CW↪ C m ∘ subComplex→map C k m
CW↪SubComplexCharac C m k q = funExt λ x
  → sym (retEq (subComplex→Equiv C k (suc m) q) _)
   ∙ cong (invEq (subComplex→Equiv C k (suc m) q)) (funExt⁻ (sym (CW↪CommSubComplex C m k)) x)


CW↑GenComm : ∀ {ℓ} (C : CWskel ℓ) (m n k : ℕ) (p : Trichotomyᵗ n (suc m)) (t : m <ᵗ n) →
    CW↑Gen C m n p t ∘ subComplex→map C k m
  ≡ subComplex→map C k n ∘ CW↑Gen (subComplex C k) m n p t
CW↑GenComm C zero (suc n) k p t = funExt λ x → (⊥.rec (G.subComplex₀-empty C k (0 ≟ᵗ k) x))
CW↑GenComm C (suc m) (suc n) k p t =
  funExt (λ qa → (help n m k p _ t refl qa
  ∙ cong ((subComplex→map C k (suc n) ∘
       CW↑Gen (subComplex C k) (suc m) (suc n) p t)) (transportRefl qa)))
  where
  help : (n m k : ℕ) (p : _) (s : _) (t : _) (pp : s ≡ (suc m ≟ᵗ k))
    → (x : G.subComplexFam C k (suc m) s) →
         CW↑Gen C (suc m) (suc n) p t
         (subComplexMapGen.subComplex→map' C k (suc m) s x)
         ≡
         subComplexMapGen.subComplex→map' C k (suc n) (suc n ≟ᵗ k)
         (CW↑Gen (subComplex C k) (suc m) (suc n) p t (subst (G.subComplexFam C k (suc m)) pp x))
  help (suc n) m k (lt x₁) s t pp x = ⊥.rec (¬squeeze (t , x₁))
  help (suc n) m k (eq x₁) s t pp x = cong (CW↪ C (suc n))
    (cong (λ p → subst (fst C) p
      (subComplexMapGen.subComplex→map' C k (suc m) s x)) (isSetℕ _ _ _ _)
    ∙ lem m (cong predℕ (cong predℕ x₁)) s (sym pp) x
    ∙ cong (subComplex→map C k (suc n))
        (cong (λ p → subst (subComplexFam C k) p
          (subst (G.subComplexFam C k (suc m)) pp x))
          (isSetℕ _ _ _ _)))
    ∙ funExt⁻ (CW↪CommSubComplex C (suc n) k)
        ((subst (λ m₁ → subComplexFam C k m₁) (cong predℕ (sym x₁))
          (subst (G.subComplexFam C k (suc m)) pp x)))
    where
    lem : (m : ℕ) (x₁ : n ≡ m) (s : _) (t : (suc m ≟ᵗ k) ≡ s) (x : _)
      → subst (fst C) (cong suc (sym x₁)) (subComplexMapGen.subComplex→map' C k (suc m) s x)
        ≡ subComplex→map C k (suc n)
           (subst (subComplexFam C k) (cong suc (sym x₁))
             (subst (G.subComplexFam C k (suc m)) (sym t) x))
    lem = J> (J> λ x → transportRefl _ ∙ sym (cong (subComplex→map C k (suc n)) (transportRefl _ ∙ transportRefl x)))
  help (suc n) m k (gt x₁) s t pp x =
    cong (CW↪ C (suc n)) (help n m k (suc n ≟ᵗ suc (suc m)) s x₁ pp x)
    ∙ funExt⁻ (CW↪CommSubComplex C (suc n) k)
      (CW↑Gen (subComplex C k) (suc m) (suc n) (suc n ≟ᵗ suc (suc m)) x₁
         (subst (G.subComplexFam C k (suc m)) pp x))
  {-
  help pp s zero t x = {!!}
  help (lt x₁) s (suc n) p t pp x =
  help (eq x₁) s (suc n) p t pp x = cong (CW↪ C n) {!!}
    ∙ funExt⁻ (CW↪CommSubComplex C n k)
        ((subst (λ m₁ → subComplexFam C k m₁)
          (λ i → predℕ (x₁ (~ i))) (subst (G.subComplexFam C k (suc m)) pp x)))
  help (gt x₁) s (suc n) p t pp x =
    cong (CW↪ C n) {!help ? ? !}
    ∙ funExt⁻ (CW↪CommSubComplex C n k)
       ((CW↑Gen (subComplex C k) (suc m) n (n ≟ᵗ suc (suc m)) x₁
        (subst (G.subComplexFam C k (suc m)) pp x)))
        -}
  {-
  help (lt x₂) (lt x₁) pp x =  ⊥.rec (¬squeeze (t , x₂))
  help (eq x₂) (lt x₁) pp x = cong (CW↪ C n) {!!}
    ∙ funExt⁻ (CW↪CommSubComplex C n k) ((subst (λ m₁ → subComplexFam C k m₁) (λ i → predℕ (x₂ (~ i))) (subst (G.subComplexFam C k (suc m)) pp x)))
  help (gt x₂) (lt x₁) pp x = {!!}
  help p (eq x₁) pp x  = {!!}
  help p (gt x₁) pp x = {!!}
  -}
{-
  funExt λ q → help n (cong predℕ (sym x)) (suc m ≟ᵗ k) q (suc n ≟ᵗ k) (n ≟ᵗ k) λ i → predℕ (x (~ i)) ≟ᵗ k
-- {!CW↪SubComplexCharac C (suc m) k!}
  where
  help : (n : ℕ) (p : suc m ≡ n) (t : _) (q : G.subComplexFam C k (suc m) t) (t' : _) (s : _)
    → (pp : PathP (λ i → Trichotomyᵗ (p i) k) t s)
    → CW↪ C n (subst (fst C) p (subComplexMapGen.subComplex→map' C k (suc m) t q))
    ≡ subComplexMapGen.subComplex→map' C k (suc n) t'
        (invEq (G.subComplexFam≃Pushout C k n s t')
          (inl (transport (λ i → G.subComplexFam C k (p i) (pp i)) q)))
  help = J> λ t q t' → J> cong (CW↪ C (suc m)) (transportRefl _)
    ∙ {!!}
    ∙ cong (subComplexMapGen.subComplex→map' C k (suc (suc m)) t')
       (cong (invEq (G.subComplexFam≃Pushout C k (suc m) t t'))
         λ j → inl (transportRefl q (~ j)))
-}
-- CW↑GenComm C (suc m) (suc n) zero (gt x) t = funExt {!!}
-- CW↑GenComm C (suc m) (suc n) (suc k) (gt x) t = {!!}
{- with (suc n ≟ᵗ k)
... | lt x₁ = funExt λ r → {!!} ∙ {!!}
... | eq x₁ = {!!}
  where
  help : {!!}
  help = {!!}
... | gt x₁ = funExt λ r → {!CW↑GenComm C k (suc m) !}
-}
{-
 -- subComplex→map C k (suc n) ∘
      (λ x₁ →
         CW↪ (subComplex C k) n
         (CW↑Gen (subComplex C k) (suc m) n (n ≟ᵗ suc (suc m)) x x₁))
-}
-- ⊥elimLem : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {x : B} {s : _} → x ≡ f (⊥.rec s)
-- ⊥elimLem {s = ()}

subComplex→comm : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) (p : _) (q : _) (x : G.subComplexFam C n m p)
    → CW↪ C m (subComplexMapGen.subComplex→map' C n m p x)
    ≡ subComplexMapGen.subComplex→map' C n (suc m) q (SubComplexGen.subComplexCW↪Gen C n m p q x)
subComplex→comm C m zero (eq x₁) s x = ⊥.rec (CW₀-empty C (subst (fst C) x₁ x))
subComplex→comm C m zero (gt x₁) q x = ⊥.rec (CW₀-empty C x)
subComplex→comm C m (suc n) (lt x₁) (lt x₂) x = refl
subComplex→comm C m (suc n) (lt x₁) (eq x₂) x = refl
subComplex→comm C m (suc n) (lt x₁) (gt x₂) x = ⊥.rec (¬squeeze (x₁ , x₂))
subComplex→comm C m (suc n) (eq x₁) (lt x₂) x = ⊥.rec (¬m<ᵗm (transp (λ i → x₁ i <ᵗ suc n) i0 (<ᵗ-trans <ᵗsucm x₂)))
subComplex→comm C m (suc n) (eq x₁) (eq x₂) x = ⊥.rec ( falseDichotomies.eq-eq (sym x₁ , sym x₂))
subComplex→comm C m (suc n) (eq x₁) (gt x₂) x with (m ≟ᵗ suc n)
... | lt x₃ =  ⊥.rec (¬squeeze (x₂ , x₃))
... | eq x₃ = cong (CW↪ C m) (sym (cong (subst (fst C) (sym x₃)) (transportRefl _ ∙ cong (λ p → subst (fst C) p x) (isSetℕ _ _ x₁ x₃)) ∙ subst⁻Subst (fst C) x₃ x))
... | gt x₃ = ⊥.rec (¬m<ᵗm (subst (suc n <ᵗ_) x₁ x₃))
subComplex→comm C m (suc n) (gt x₁) (lt x₂) x = (⊥.rec (¬squeeze (x₂ , <ᵗ-trans x₁ (<ᵗ-trans <ᵗsucm <ᵗsucm))))
subComplex→comm C m (suc n) (gt x₁) (eq x₂) x = (⊥.rec
       (¬m<ᵗm (transp (λ i → suc n <ᵗ x₂ i) i0 (<ᵗ-trans x₁ <ᵗsucm))))
subComplex→comm C (suc m) (suc n) (gt x₁) (gt x₂) x with m ≟ᵗ n
... | lt x₃ = ⊥.rec (¬squeeze (x₂ , x₃))
... | eq x₃ = ⊥.rec (¬m<ᵗm (subst (n <ᵗ_) x₃ x₁))
... | gt x₃ = cong (CW↪ C (suc m)) λ j → CW↑Gen C (suc n) (suc m) (Trichotomyᵗ-suc (m ≟ᵗ suc n)) (isProp<ᵗ x₁ x₃ j) x

subComplex→Full : ∀ {ℓ} (C : CWskel ℓ) (m : ℕ) → cellMap (subComplex C m) C
SequenceMap.map (subComplex→Full C n) = subComplex→map C n
SequenceMap.comm (subComplex→Full C n) m = subComplex→comm C m n _ _

subComplex→ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) → finCellMap n (subComplex C m) C
FinSequenceMap.fmap (subComplex→ C m n) = subComplex→map C m ∘ fst
FinSequenceMap.fcomm (subComplex→ C m n) t = subComplex→comm C (fst t) m _ _

-- subComplex→ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) → finCellMap n (subComplex C m) C
-- FinSequenceMap.fmap (subComplex→ C m n) (t , q) = subComplex→map C m t
-- FinSequenceMap.fcomm (subComplex→ C zero (suc n)) (t , q) x with (t ≟ᵗ 0)
-- ... | eq x₁ = ⊥.rec
--       (C .snd .snd .snd .fst
--        (snd (G.subComplexFam≃Pushout C 0 t (eq x₁) (gt tt)) .equiv-proof
--         (inl x) .fst .fst))
-- ... | gt x₁ = ⊥.rec (C .snd .snd .snd .fst x)
-- FinSequenceMap.fcomm (subComplex→ C (suc m) (suc n)) (t , q) with (t ≟ᵗ m)
-- ... | lt x = ltx
--   where
--   ltx : _
--   ltx s with (t ≟ᵗ suc m)
--   ... | gt s = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans s x))
--   ... | eq s = ⊥.rec (¬-suc-n<ᵗn ((subst (suc t <ᵗ_) (sym s) x)))
--   ... | lt s = refl
-- ... | eq x = eqx
--   where
--   eqx : _
--   eqx s with (t ≟ᵗ suc m)
--   ... | lt s = refl
--   ... | eq s = ⊥.rec (falseDichotomies.eq-eq (x , s))
--   ... | gt s = ⊥.rec (¬-suc-n<ᵗn (subst (suc m <ᵗ_) x s))
-- ... | gt x = mx
--   where
--   mx : (o : _) → _ ≡ _
--   mx with (t ≟ᵗ suc m)
--   ... | lt s = ⊥.rec (¬squeeze (s , x))
--   ... | eq x = λ o
--     → cong (CW↪ C t) (sym (cong (subst (fst C) (sym x)) (transportRefl _)
--      ∙ subst⁻Subst (fst C) x o ))
--   ... | gt x = λ _ → refl

-- subComplexHomologyEquiv≡ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) (p : suc (suc n) <ᵗ m)
--   → (e : realise (subComplex C m) ≃ fst C m)
--   → ((x : _) → fst e (incl {n = m} x)
--                ≡ subst (G.subComplexFam C m m) (isPropTrichotomyᵗ (m ≟ᵗ m) (eq refl)) x)
--   → Iso.inv (fst (subComplexHomology C m n p)) ≡ Hˢᵏᵉˡ→ n (incl ∘ fst e) .fst
-- subComplexHomologyEquiv≡ C m n p e ide = {!!} -- funExt {!!}
--   where
--   help : finCellApprox (subComplex C m) C
--       (λ x → incl (fst e x))
--       (suc (suc (suc n)))
--   fst help = subComplex→ C m (suc (suc (suc n)))
--   snd help = →FinSeqColimHomotopy _ _ {!fst e!}-- →FinSeqColimHomotopy _ _ (λ x → main (suc (suc (suc n)) ≟ᵗ m) x refl ∙ {!!})
--     where
--     mainS : (b : ℕ) (t : b <ᵗ suc (suc (suc (suc n)))) (x : _) → incl (subComplex→map C m b x) ≡ incl (fst e (incl x))
--     mainS zero t x = {!!}
--     mainS (suc b) t x = {!!}


--     main : (p : _)  (x : _) (q : p ≡ (suc (suc (suc n)) ≟ᵗ m)) → Path (realise C) (incl {n = suc(suc (suc n))}
--       (subComplexMapGen.subComplex→map' C m (suc (suc (suc n)))
--        p x))
--      ( incl (fst e (incl (subst (G.subComplexFam C m (suc (suc (suc n)))) q x))))
--     main (lt x₁) x q = {!!} ∙ {!!} ∙  cong (incl {n = m}) (sym (ide _) ∙ {!!} ∙ cong (fst e) {!sym (CW↑Gen≡ C (suc (suc (suc n))) m ? x₁ ?)!})
--     main (eq x₁) x q = {!!}
--     main (gt x₁) x q = {!!}

goDown : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _)
  → G.subComplexFam C m (suc m) p → G.subComplexFam C m m q
goDown C m (lt x) q = ⊥.rec (¬-suc-n<ᵗn x)
goDown C m (eq x) q = ⊥.rec (falseDichotomies.eq-eq(refl , sym x))
goDown C m (gt x) (lt x₁) = ⊥.rec (¬m<ᵗm x₁)
goDown C m (gt x) (eq x₁) = idfun _
goDown C m (gt x) (gt x₁) = ⊥.rec (¬m<ᵗm x₁)

CW↪goDown : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _) (x : _)
  → SubComplexGen.subComplexCW↪Gen C m m p q (goDown C m q p x) ≡ x
CW↪goDown C m p (lt x₁) x = ⊥.rec (¬-suc-n<ᵗn x₁)
CW↪goDown C m p (eq x₁) x = ⊥.rec (falseDichotomies.eq-eq(refl , sym x₁))
CW↪goDown C m (lt x₂) (gt x₁) x = ⊥.rec (¬m<ᵗm x₂)
CW↪goDown C m (eq x₂) (gt x₁) x =
  transportRefl _ ∙ cong (λ p → subst (fst C) p x) (isSetℕ _ _ x₂ refl) ∙ transportRefl x
CW↪goDown C m (gt x₂) (gt x₁) x = ⊥.rec (¬m<ᵗm x₂)

Charac↑ : ∀ {ℓ} (C : CWskel ℓ)  (m : ℕ) (p : _) (q : _)
  → subComplexMapGen.subComplex→map' C m (suc m) p
   ≡ CW↪ C m ∘ subComplexMapGen.subComplex→map' C m m q ∘ goDown C m p q
Charac↑ C m p (lt x) = ⊥.rec (¬m<ᵗm x)
Charac↑ C m (lt x₁) (eq x) = ⊥.rec (¬-suc-n<ᵗn x₁)
Charac↑ C m (eq x₁) (eq x) = ⊥.rec (falseDichotomies.eq-eq (refl , sym x₁))
Charac↑ C zero (gt x₁) (eq x) = funExt (λ q → ⊥.rec (C .snd .snd .snd .fst q))
Charac↑ C (suc m) (gt x₁) (eq x) with (m ≟ᵗ m)
... | lt x₂ =  ⊥.rec (¬m<ᵗm x₂)
... | eq x₂ = funExt λ x
  → cong (CW↪ C (suc m)) (cong (λ p → subst (fst C) p x) (isSetℕ _ _ _ _)
    ∙ transportRefl x)
... | gt x₂ =  ⊥.rec (¬m<ᵗm x₂)
Charac↑ C m p (gt x) = ⊥.rec (¬m<ᵗm x)

subComplexHomologyEquiv≡ : ∀ {ℓ} (C : CWskel ℓ) (m n : ℕ) (p : suc (suc n) <ᵗ m)
  → Iso.inv (fst (subComplexHomology C m n p)) ≡ Hˢᵏᵉˡ→ n (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
subComplexHomologyEquiv≡ C m n p =
  funExt (SQ.elimProp (λ _ → squash/ _ _) λ a → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _) (main (fst a)))) -- funExt {!!}
  ∙ cong fst (sym (Hˢᵏᵉˡ→β (subComplex C m) C n {f = (incl ∘ Iso.inv (realiseSubComplex m C))}
    help))
  where
  help : finCellApprox (subComplex C m) C
      (λ x → incl (Iso.inv (realiseSubComplex m C) x))
      (suc (suc (suc n)))
  fst help = subComplex→ C m (suc (suc (suc n)))
  snd help = →FinSeqColimHomotopy _ _ λ x → CW↑Gen≡ C (suc (suc (suc n))) (suc m) (suc m ≟ᵗ suc (suc (suc (suc n)))) p _
    ∙ cong (incl {n = suc m}) (funExt⁻ (CW↑GenComm C (suc (suc (suc n))) (suc m) m (suc m ≟ᵗ suc (suc (suc (suc n)))) p) x
      ∙ funExt⁻ (Charac↑ C m (suc m ≟ᵗ m) (m ≟ᵗ m)) (CW↑Gen (subComplex C m)
                  (suc (suc (suc n))) (suc m) (Trichotomyᵗ-suc (m ≟ᵗ suc (suc (suc n)))) p x)  -- funExt⁻ (Charac↑ C m _ ?)
      ∙ cong (CW↪ C m) (sym (Iso.leftInv ( (realiseSubComplex m C) ) _)
      ∙ cong (Iso.inv (realiseSubComplex m C))
        ((push _ ∙ cong (incl {n = suc m}) (cong (CW↪ (subComplex C m) m) (secEq (complex≃subcomplex' C m m <ᵗsucm (m ≟ᵗ m)) _)
          ∙ CW↪goDown C m (m ≟ᵗ m) (suc m ≟ᵗ m) _))
        ∙ sym (CW↑Gen≡ (subComplex C m)  (suc (suc (suc n))) (suc m) ((suc m) ≟ᵗ (suc (suc (suc (suc n))))) p x))))
    ∙ sym (push _) -- mainna x (suc (suc (suc n)) ≟ᵗ m)

  FIN : Fin (suc (suc (suc n)))
  FIN = suc n , <ᵗ-trans {n = suc n} {m = suc (suc n)}{k = suc (suc (suc n))} <ᵗsucm <ᵗsucm

  f1/f2gen :  (q1 : _) (q2 : _)
           → cofib (invEq (G.subComplexFam≃Pushout C m (suc n) q1 q2) ∘ inl) →
             Pushout (λ _ → tt) (invEq (C .snd .snd .snd .snd (fst FIN)) ∘ inl)
  f1/f2gen q1 q2 (inl x) = inl x
  f1/f2gen q1 q2 (inr x) = inr (subComplexMapGen.subComplex→map' C m (suc (suc n)) q2 x)
  f1/f2gen q1 q2 (push a i) =
      (push (subComplexMapGen.subComplex→map' C m (suc n) q1 a)
    ∙ λ i → inr (subComplex→comm C (suc n) m q1 q2 a i)) i

  f1/f2≡ : f1/f2gen (suc n ≟ᵗ m) (suc (suc n) ≟ᵗ m)
         ≡ prefunctoriality.fn+1/fn (suc (suc (suc n))) (subComplex→ C m (suc (suc (suc n)))) FIN
  f1/f2≡ = funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl}

  f1/f2genId : (q1 : _) (q2 : _) → f1/f2gen (lt q1) (lt q2) ≡ idfun _
  f1/f2genId q1 q2 = funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) j
    → ((λ i → push a ∙ (λ j → inr (help2 m q1 q2 a i j))) ∙ sym (rUnit (push a))) j i}
    where
    help2 : (m : ℕ) (q1 : _) (q2 : _) (a : _) → subComplex→comm C (suc n) m (lt q1) (lt q2) a ≡ refl
    help2 (suc m) q1 q2 a = refl

  mainGen : (q1 : _) (q2 : _) (a : _)
    → Iso.inv (fst (subChainIsoGen C m (suc n , <ᵗ-trans <ᵗsucm p) q1)) a
    ≡ bouquetDegree
      (BouquetFuns.CTB (suc n) (C .snd .fst (suc n)) (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN))
      ∘ f1/f2gen q1 q2
      ∘ (BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) q1)
         (G.subComplexα C m (suc n) q1)
           (G.subComplexFam≃Pushout C m (suc n) q1 q2))) .fst a
  mainGen (lt x) (lt x₁) a = funExt⁻ (sym (cong fst (bouquetDegreeId))) a ∙ λ i → bouquetDegree (cool (~ i)) .fst a
    where
    cool : BouquetFuns.CTB (suc n) (C .snd .fst (suc n)) (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN))
         ∘ f1/f2gen (lt x) (lt x₁)
         ∘ BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) (lt x))
         (G.subComplexα C m (suc n) (lt x))
           (G.subComplexFam≃Pushout C m (suc n) (lt x) (lt x₁))
         ≡ idfun _
    cool = funExt λ a → cong (BouquetFuns.CTB (suc n) (C .snd .fst (suc n)) (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN)))
                  (funExt⁻ (f1/f2genId x x₁) _)
                ∙ CTB-BTC-cancel (suc n) (C .snd .fst (suc n)) (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN)) .fst _
  mainGen (lt x) (eq x₁) a = ⊥.rec (¬m<ᵗm (subst (suc (suc n) <ᵗ_) (sym x₁) p))
  mainGen (lt x) (gt x₁) a =  ⊥.rec (¬squeeze (x , x₁))
  mainGen (eq x) q2 a = ⊥.rec (¬m<ᵗm  (subst (_<ᵗ_ (suc n)) (sym x) (<ᵗ-trans <ᵗsucm p)))
  mainGen (gt x) q2 a = ⊥.rec (¬m<ᵗm (<ᵗ-trans x (<ᵗ-trans <ᵗsucm p)))

  main : (a : _) → Iso.inv
      (fst (subChainIso C m (suc n , <ᵗ-trans <ᵗsucm p)))
      a
      ≡ _
  main a = mainGen (suc n ≟ᵗ m) (suc (suc n) ≟ᵗ m) a
        ∙ λ j → bouquetDegree
      (BouquetFuns.CTB (suc n) (C .snd .fst (suc n))
       (C .snd .snd .fst (suc n)) (C .snd .snd .snd .snd (fst FIN))
       ∘
       f1/f2≡ j ∘
       BouquetFuns.BTC (suc n) (G.subComplexCard C m (suc n) (suc n ≟ᵗ m))
       (G.subComplexα C m (suc n) (suc n ≟ᵗ m))
       (G.subComplexFam≃Pushout C m (suc n) (suc n ≟ᵗ m)
        (suc (suc n) ≟ᵗ m)))
      .fst a

subComplexHomologyEquiv : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) (m : ℕ) (p : suc (suc n) <ᵗ m)
  → GroupEquiv (Hˢᵏᵉˡ (subComplex C m) n)
                (Hˢᵏᵉˡ C n)
fst (fst (subComplexHomologyEquiv C n m p)) = Hˢᵏᵉˡ→ n (incl ∘ Iso.inv (realiseSubComplex m C)) .fst
snd (fst (subComplexHomologyEquiv C n m p)) =
  subst isEquiv (subComplexHomologyEquiv≡ C m n p)
    (isoToIsEquiv (invIso (fst (subComplexHomology C m n p))))
snd (subComplexHomologyEquiv C n m p) = Hˢᵏᵉˡ→ n (incl ∘ Iso.inv (realiseSubComplex m C)) .snd

subComplexHomologyᶜʷEquiv : ∀ {ℓ} (C : CWexplicit ℓ) (n : ℕ) (m : ℕ) (p : suc (suc n) <ᵗ m)
  → GroupEquiv (Hᶜʷ ((fst (fst (snd C))) m , ∣ subComplex (snd C .fst) m , isoToEquiv (realiseSubComplex m (snd C .fst)) ∣₁) n)
                (Hᶜʷ (realise (snd C .fst) , ∣ fst (snd C) , idEquiv _ ∣₁) n)
fst (subComplexHomologyᶜʷEquiv C n m p) = Hᶜʷ→ n (incl {n = m}) .fst , subComplexHomologyEquiv (snd C .fst) n m p .fst .snd
snd (subComplexHomologyᶜʷEquiv C n m p) = Hᶜʷ→ n (incl {n = m}) .snd

--- bouquetDegreeHom
SphereBouquet∙Π : ∀ {ℓ'} {n m : ℕ} {B : Pointed ℓ'}
  → (f g : SphereBouquet∙ (suc n) (Fin m) →∙ B)
  → (SphereBouquet∙ (suc n) (Fin m) →∙ B)
fst (SphereBouquet∙Π {m = m} {B = B} f g) (inl x) = pt B
fst (SphereBouquet∙Π {m = m} {B = B} f g) (inr (a , s)) =
  ∙Π ((λ x → fst f (inr (a , x))) , cong (fst f) (sym (push a)) ∙ snd f)
     ((λ x → fst g (inr (a , x))) , cong (fst g) (sym (push a)) ∙ snd g) .fst s
fst (SphereBouquet∙Π {m = m} {B = B} f g) (push a i) =
  ∙Π ((λ x → fst f (inr (a , x))) , cong (fst f) (sym (push a)) ∙ snd f)
     ((λ x → fst g (inr (a , x))) , cong (fst g) (sym (push a)) ∙ snd g) .snd (~ i)
snd (SphereBouquet∙Π {m = m} f g) = refl



open import Cubical.HITs.Sn.Degree renaming (degreeConst to degree-const)

-- pickPetal

open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure


degreeHom : {n : ℕ} (f g : S₊∙ (suc n) →∙ S₊∙ (suc n))
  → degree (suc n) (∙Π f g .fst) ≡ degree (suc n) (fst f) + degree (suc n) (fst g)
degreeHom {n = n} f g =
   cong (Iso.fun (Hⁿ-Sⁿ≅ℤ n .fst)) (cong ∣_∣₂ (funExt
     λ x → cong ∣_∣ₕ (cong₂ (λ f g → ∙Π f g .fst x)
                     (sym (Iso.rightInv (sphereFunIso n) f))
                     (sym (Iso.rightInv (sphereFunIso n) g)))
         ∙∙ help n _ _ x
         ∙∙ cong₂ (λ x y → ∣ x ∣ₕ +[ suc n ]ₖ ∣ y ∣ₕ)
                  (funExt⁻ (cong fst (Iso.rightInv (sphereFunIso n) f)) x)
                  (funExt⁻ (cong fst (Iso.rightInv (sphereFunIso n) g)) x)))
  ∙ IsGroupHom.pres· (Hⁿ-Sⁿ≅ℤ n .snd) _ _
  where
  help : (n : ℕ) (f g : S₊∙ n →∙ Ω (S₊∙ (suc n))) (x : S₊ (suc n))
                      → Path (coHomK (suc n))
                  ∣ ∙Π (Iso.fun (sphereFunIso n) f) (Iso.fun (sphereFunIso n) g) .fst x ∣ₕ
                  (∣ fst (Iso.fun (sphereFunIso n) f) x ∣
       +[ suc n ]ₖ ∣ fst (Iso.fun (sphereFunIso n) g) x ∣)
  help zero f g base = refl
  help zero f g (loop i) j = lem j i
    where
    lem : cong ∣_∣ₕ ((fst f false ∙ refl) ∙ fst g false ∙ refl)
        ≡ cong₂ (λ x y → ∣ x ∣ₕ +[ suc zero ]ₖ ∣ y ∣ₕ)
                (fst f false) (fst g false)
    lem = cong-∙ ∣_∣ₕ _ _
      ∙ cong₂ _∙_ ((λ i j → ∣ rUnit (fst f false) (~ i) j  ∣ₕ)
                ∙ (λ j → cong (λ x → rUnitₖ 1 ∣ x ∣ₕ (~ j)) (fst f false)))
                ((λ i j → ∣ rUnit (fst g false) (~ i) j  ∣ₕ)
                ∙ (λ j → cong (λ x → lUnitₖ 1 ∣ x ∣ₕ (~ j)) (fst g false)))
      ∙ sym (cong₂Funct (λ x y → ∣ x ∣ₕ +[ suc zero ]ₖ ∣ y ∣ₕ)
             (fst f false) (fst g false))
  help (suc n) f g north = refl
  help (suc n) f g south = refl
  help (suc n) f g (merid a i) j = lem j i
    where
    lem : cong ∣_∣ₕ ((cong (fst (toΩ→fromSusp f)) (σS a) ∙ refl)
                 ∙ (cong (fst (toΩ→fromSusp g)) (σS a) ∙ refl))
        ≡ cong₂ (λ x y → ∣ x ∣ₕ +[ suc (suc n) ]ₖ ∣ y ∣ₕ)
                (fst f a) (fst g a)
    lem = cong-∙ ∣_∣ₕ _ _
      ∙ cong₂ _∙_ (cong (cong ∣_∣ₕ) (funExt⁻ (cong fst (Iso.leftInv ΩSuspAdjointIso f)) a)
                  ∙ λ j i → rUnitₖ (suc (suc n)) ∣ fst f a i ∣ₕ (~ j))
                  (cong (cong ∣_∣ₕ) (funExt⁻ (cong fst (Iso.leftInv ΩSuspAdjointIso g)) a)
                  ∙ (λ j i → lUnitₖ (suc (suc n)) ∣ fst g a i ∣ₕ (~ j)))
      ∙ sym (cong₂Funct (λ x y → ∣ x ∣ₕ +[ suc (suc n) ]ₖ ∣ y ∣ₕ)
              (fst f a) (fst g a))

bouquetDegree+ : (n m k : ℕ)
  (f g : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k))
  → bouquetDegree (SphereBouquet∙Π f g .fst)
   ≡ addGroupHom ℤ[Fin m ] ℤ[Fin k ] (bouquetDegree (fst f)) (bouquetDegree (fst g))
bouquetDegree+ n m k f g =
  agreeOnℤFinGenerator→≡
    λ s → funExt λ y → (sym (isGeneratorℤFinGenerator' _ s)
      ∙ cong (degree (suc n)) (funExt (main n s y f g))
       ∙ degreeHom {n = n}
         ((λ x₁ → pickPetal y (fst f (inr (s , x₁))))
                 , cong (pickPetal y) (cong (fst f) (sym (push s)) ∙ snd f))
         ((λ x₁ → pickPetal y (fst g (inr (s , x₁))))
                 , cong (pickPetal y) (cong (fst g) (sym (push s)) ∙ snd g))
      ∙ isGeneratorℤFinGenerator' _ s
      ∙ cong sumFinℤ (funExt λ x →
        ·DistR+ (ℤFinGenerator s x)
                (degree (suc n) (λ x₁ → pickPetal y (fst f (inr (x , x₁)))))
                (degree (suc n) (λ x₁ → pickPetal y (fst g (inr (x , x₁))))))
      ∙ sumFinℤHom _ _) --
  where
  main : (n : ℕ) (s : Fin m) (y : _)
    (f g : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k)) (x : S₊ (suc n)) →
      pickPetal y (SphereBouquet∙Π f g .fst (inr (s , x)))
    ≡ (∙Π ((λ x₁ → pickPetal y (fst f (inr (s , x₁)))) ,
           (λ i → pickPetal y (((λ i₁ → fst f (push s (~ i₁))) ∙ snd f) i)))
          ((λ x₁ → pickPetal y (fst g (inr (s , x₁)))) ,
           (λ i → pickPetal y (((λ i₁ → fst g (push s (~ i₁))) ∙ snd g) i))) .fst x)
  main zero s y f g base = refl
  main zero s y f g (loop i) = refl
  main (suc n) s y f g north = refl
  main (suc n) s y f g south = refl
  main (suc n) s y f g (merid a i) j = lem j i
    where
    lem : cong (pickPetal y) (cong (λ x → SphereBouquet∙Π f g .fst (inr (s , x))) (merid a))
        ≡ (sym (cong (pickPetal y) ((λ i₁ → fst f (push s (~ i₁))) ∙ snd f))
          ∙∙ cong (pickPetal y) (cong (λ x → fst f (inr (s , x))) (σS a))
          ∙∙ cong (pickPetal y) ((λ i₁ → fst f (push s (~ i₁))) ∙ snd f))
        ∙ (sym (cong (pickPetal y) ((λ i₁ → fst g (push s (~ i₁))) ∙ snd g))
          ∙∙ cong (pickPetal y) (cong (λ x → fst g (inr (s , x))) (σS a))
          ∙∙ cong (pickPetal y) ((λ i₁ → fst g (push s (~ i₁))) ∙ snd g))
    lem = (cong-∙ (pickPetal y) _ _
      ∙ cong₂ _∙_ (cong-∙∙ (pickPetal y) (sym ((λ i₁ → fst f (push s (~ i₁))) ∙ snd f)) _ _)
                  (cong-∙∙ (pickPetal y) (sym ((λ i₁ → fst g (push s (~ i₁))) ∙ snd g)) _ _))


-- Sphere stuff
module _ {ℓ} (Xsk : CWskel ℓ) (x₀ : fst Xsk 1) where
  fn+1/fn-SGen-inr : (n m : ℕ)
    (f : S₊∙ n →∙ (fst Xsk (suc m) , CWskel∙ Xsk x₀ m))
   → (p : _) → Sgen.Sfam n (suc (suc m)) p → fst Xsk (suc m)
  fn+1/fn-SGen-inr n m f (lt x) = λ _ → CWskel∙ Xsk x₀ m
  fn+1/fn-SGen-inr n m f (eq x) = fst f
  fn+1/fn-SGen-inr n m f (gt x) = fst f

  fn+1/fn-SGenEq : (n m : ℕ)
    (f : S₊∙ n →∙ (fst Xsk (suc (suc m)) , CWskel∙ Xsk x₀ (suc m)))
    (g : S₊∙ n →∙ (fst Xsk (suc m) , CWskel∙ Xsk x₀ m))
    → (q : _) (a : Sgen.Sfam n (suc (suc m)) q)
    →  fst Xsk (suc m)
  fn+1/fn-SGenEq n m f g (lt x) a = CWskel∙ Xsk x₀ m
  fn+1/fn-SGenEq n m f g (eq x) a = g .fst a
  fn+1/fn-SGenEq n m f g (gt x) a = g .fst a

  -- fn+1Eq : (n m : ℕ)
  --   (f : S₊∙ n →∙ (fst Xsk (suc (suc m)) , CWskel∙ Xsk x₀ (suc m)))
  --   (g : S₊∙ n →∙ (fst Xsk (suc m) , CWskel∙ Xsk x₀ m))
  --   → (p : _) (q : _) (a : _)
  --     → CW↪ Xsk (suc m) (fn+1/fn-SGenEq n m f g p a)
  --     ≡ fn+1/fn-SGen-inr n (suc m) ? q (invEq (SαMainEqGen n (suc m) q p) (inl a))
  -- fn+1Eq n m f g (lt x₁) (lt x) a = refl
  -- fn+1Eq n m f g (eq x₁) (lt x) a = {!!}
  -- fn+1Eq n m f g (gt x₁) (lt x) a = {!!}
  -- fn+1Eq (suc n) m f g (lt x₁) (eq x) a = sym (snd f)
  -- fn+1Eq n m f g (eq x₁) (eq x) a = {!⊥!}
  -- fn+1Eq n m f g (gt x₁) (eq x) a = {!⊥!}
  -- fn+1Eq (suc n) m f g (lt x₁) (gt x) a = {!!}
  -- fn+1Eq zero m f g (eq x₁) (gt x) a = {!!}
  -- fn+1Eq (suc n) m f g (eq x₁) (gt x) a = {!,u,u,u,u,u,u,u,u,u,u,!}
  -- fn+1Eq n m f g (gt x₁) (gt x) a = {!!}

  -- fn+1/fn-SGen : (n m : ℕ)
  --   (g : S₊∙ n →∙ (fst Xsk (suc m) , CWskel∙ Xsk x₀ m))
  --   → (p : _) (q : _) → cofib (invEq (SαMainEqGen n (suc m) p q) ∘ inl) → cofibCW (suc m) Xsk
  -- fn+1/fn-SGen n m g p q (inl x) = inl tt
  -- fn+1/fn-SGen n m g p q (inr x) = inr {!CW\!} -- (fn+1/fn-SGen-inr n (suc m) ((CW↪ Xsk (suc m) , refl) ∘∙ g) p x)
  -- fn+1/fn-SGen n m g p q (push a i) =
  --   (push (fst g {!!}) ∙ {!!}) i -- (push (fn+1/fn-SGenEq n m g q a)) i

  -- fn+1/fn-SGen n zero f (lt x₁) (lt x) (push a i) = {!in!}
  -- fn+1/fn-SGen (suc n) zero f (eq x₁) (lt x) (push a i) = {!!}
  -- fn+1/fn-SGen n zero f (gt x₁) (lt x) (push a i) = {!n!}
  -- fn+1/fn-SGen n zero f p (eq x) (push a i) = {!!}
  -- fn+1/fn-SGen n (suc m) f p q (push a i) = {!!} -- fn+1/fn-SGenEq n m f p q a i
