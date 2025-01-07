{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.SphereBouquetCofibHomotopy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GLaws
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed

open import Cubical.Functions.Morphism



open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.Connected
open import Cubical.CW.Homology
open import Cubical.CW.Subcomplex


open import Cubical.Data.Empty
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
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
open import Cubical.HITs.Sn.Degree
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
open import Cubical.Data.Int renaming (_·_ to _·ℤ_)
open import Cubical.Algebra.Group.QuotientGroup

open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Abelianization.Properties as Abi

open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Unit
open import Cubical.HITs.Wedge


open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup as FAB 

open import Hurewicz.random
open import Hurewicz.AbPath


open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Pushout as PO


open import Cubical.Algebra.Group.Subgroup
open import Cubical.Homotopy.Loopspace
open import Cubical.HITs.S1
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.HITs.FreeAbGroup.Base

open import Cubical.Algebra.Group.Free
open import Cubical.Data.List renaming ([_] to [_]L)



open import Cubical.HITs.Bouquet as Bouq
open import Cubical.HITs.Bouquet.Discrete



open import Cubical.HITs.FreeGroup as FG
open import Cubical.HITs.FreeGroup.NormalForm
open import Cubical.HITs.FreeGroupoid.Properties
open import Cubical.Algebra.Group.Free

-- general lemmas

Fin→BreakOutFirst : ∀ {ℓ} (n : ℕ) {A : Fin (suc n) → Type ℓ}
  → Iso ((x : Fin (suc n)) → A x)
         (((x : _) → A (fsuc x)) × A fzero)
fst (Iso.fun (Fin→BreakOutFirst n) f) x = f (fsuc x)
snd (Iso.fun (Fin→BreakOutFirst n) f) = f fzero
Iso.inv (Fin→BreakOutFirst n) (f , s) (zero , w) = s
Iso.inv (Fin→BreakOutFirst (suc n)) (f , s) (suc t , w) = f (t , w)
fst (Iso.rightInv (Fin→BreakOutFirst (suc n)) (f , s) i) (w , t) = f (w , t)
snd (Iso.rightInv (Fin→BreakOutFirst n) (f , s) i) = s
Iso.leftInv (Fin→BreakOutFirst n) f i (zero , tt) = f fzero
Iso.leftInv (Fin→BreakOutFirst (suc n)) f i (suc s , t) = f (suc s , t)

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  fiberFstIso : {x : A} → Iso (fiber {A = A × B} fst x) B
  Iso.fun fiberFstIso = snd ∘ fst
  Iso.inv (fiberFstIso {x = x}) b = (x , b) , refl
  Iso.rightInv fiberFstIso b = refl
  Iso.leftInv (fiberFstIso {x = x}) ((a , b) , p) i =
    (p (~ i) , b) , λ j → p (~ i ∨ j)

  fiberSndIso : {x : B} → Iso (fiber {A = A × B} snd x) A
  Iso.fun fiberSndIso = fst ∘ fst
  Iso.inv (fiberSndIso {x = x}) a = (a , x) , refl
  Iso.rightInv fiberSndIso b = refl
  Iso.leftInv (fiberSndIso {x = x}) ((a , b) , p) i =
    (a , p (~ i)) , λ j → p (~ i ∨ j)


breakOut⋁ : ∀ {ℓ} {n : ℕ} {A : Fin (suc n) → Pointed ℓ}
  → Iso (⋁gen (Fin (suc n)) A) (⋁gen∙ (Fin n) (A ∘ fsuc) ⋁ A fzero)
Iso.fun breakOut⋁ (inl x) = inl (inl tt)
Iso.fun breakOut⋁ (inr ((zero , w) , t)) = inr t
Iso.fun (breakOut⋁ {n = suc n}) (inr ((suc f , w) , t)) = inl (inr ((f , w) , t))
Iso.fun breakOut⋁ (push (zero , w) i) = push tt i
Iso.fun (breakOut⋁ {n = suc n}) (push (suc x , w) i) = inl (push (x , w) i)
Iso.inv breakOut⋁ (inl (inl x)) = inl tt
Iso.inv breakOut⋁ (inl (inr x)) = inr ((fsuc (fst x)) , (snd x))
Iso.inv breakOut⋁ (inl (push a i)) = push (fsuc a) i
Iso.inv breakOut⋁ (inr x) = inr (fzero , x)
Iso.inv breakOut⋁ (push a i) = push fzero i
Iso.rightInv breakOut⋁ (inl (inl tt)) i = inl (inl tt)
Iso.rightInv (breakOut⋁ {n = suc n}) (inl (inr ((zero , w) , t))) = refl
Iso.rightInv (breakOut⋁ {n = suc n}) (inl (inr ((suc a , w) , t))) = refl
Iso.rightInv (breakOut⋁ {n = suc n}) (inl (push (zero , w) i)) = refl
Iso.rightInv (breakOut⋁ {n = suc n}) (inl (push (suc a , w) i)) = refl
Iso.rightInv breakOut⋁ (inr x) i = inr x 
Iso.rightInv breakOut⋁ (push a i) j = push a i
Iso.leftInv breakOut⋁ (inl x) i = inl tt
Iso.leftInv breakOut⋁ (inr ((zero , tt) , t)) i = inr ((0 , tt) , t)
Iso.leftInv (breakOut⋁ {n = suc n}) (inr ((suc x , w) , t)) i = inr ((suc x , w) , t)
Iso.leftInv breakOut⋁ (push (zero , w) i) j = push (0 , w) i
Iso.leftInv (breakOut⋁ {n = suc n}) (push (suc x , w) i) = refl

pickPetalSwap : {n k : ℕ} → SphereBouquet n (Fin k) → Fin k → S₊ n
pickPetalSwap a b = pickPetal b a


open import Cubical.Homotopy.BlakersMassey

isConnected⋁↪ : ∀ {ℓ ℓ'} {A : Pointed ℓ} {B : Pointed ℓ'} {n m : ℕ}
  → isConnected (suc (suc n)) (fst A)
  → isConnected (suc (suc m)) (fst B)
  → isConnectedFun (suc m +ℕ suc n) (⋁↪ {A = A} {B})
isConnected⋁↪ {A = A} {B} {n} {m} cA cB =
  subst (isConnectedFun (suc m +ℕ suc n)) (sym main)
    (isConnectedComp _  _ _
      (isEquiv→isConnected _ (isoToIsEquiv lem) _)
      isConnected-toPullback)
  where
  foldL : A ⋁ B → fst A
  foldL (inl x) = x
  foldL (inr x) = pt A
  foldL (push a i) = pt A


  foldR : A ⋁ B → fst B
  foldR (inl x) = pt B
  foldR (inr x) = x
  foldR (push a i) = pt B



  isConnectedFoldL : (cB : isConnected (suc (suc m)) (fst B))
    → isConnectedFun (suc (suc m)) foldL
  isConnectedFoldL cB =
    subst (isConnectedFun (suc (suc m)))
      (funExt (λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl}))
      conf
    where
    f' : A ⋁ B → fst A
    f' = Iso.fun cofibInr-⋁ ∘ inr

    conf : isConnectedFun (suc (suc m)) f'
    conf = isConnectedComp (Iso.fun cofibInr-⋁) inr
             (suc (suc m))
               (isEquiv→isConnected _ (isoToIsEquiv cofibInr-⋁) (suc (suc m)))
               (inrConnected (suc (suc m)) _ _
                 (isConnected→isConnectedFun (suc (suc m)) cB))

  isConnectedFoldR : (cA : isConnected (suc (suc n)) (fst A))
    → isConnectedFun (suc (suc n)) foldR
  isConnectedFoldR cA =
    subst (isConnectedFun (suc (suc n)))
      (funExt (λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl}))
      conf
    where
    f' : A ⋁ B → fst B
    f' = (Iso.fun cofibInr-⋁ ∘ inr) ∘ fst (symPushout _ _)

    conf : isConnectedFun (suc (suc n)) f'
    conf =
      isConnectedComp (Iso.fun cofibInr-⋁ ∘ inr) (fst (symPushout _ _))
        (suc (suc n))
        (isConnectedComp _ inr (suc (suc n))
          (isEquiv→isConnected _ (isoToIsEquiv cofibInr-⋁) (suc (suc n)))
          (inrConnected (suc (suc n)) _ _
            (isConnected→isConnectedFun (suc (suc n)) cA))) -- 
             (isEquiv→isConnected _ (snd (symPushout _ _)) (suc (suc n)))

  l1 : (a : _) → Path (Pushout foldL foldR) (inl a) (inr (pt B)) 
  l1 x = push (inl x)

  l2 : (b : _) → Path (Pushout foldL foldR) (inl (pt A))  (inr b) 
  l2 x = push (inr x)

  l1≡l2 : l1 (pt A) ≡ l2 (pt B)
  l1≡l2 i = push (push tt i)

  F : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (l1 l2 : x ≡ y) (q : l1 ≡ l2)
    → (z : A) (m : x ≡ z) → Square (l1 ∙ sym l2) m refl m
  F y l1 l2 q z m = (cong₂ _∙_ q refl ∙ rCancel l2)  ◁ λ i j → m (i ∧ j)

  F' : ∀ {ℓ} {A : Type ℓ} {x : A} → F x refl refl refl _ refl ≡ sym (rUnit refl)
  F' = sym (compPath≡compPath' _ _) ∙ sym (rUnit _) ∙ sym (lUnit _)

  H : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (l1 l2 : x ≡ y) (q : l1 ≡ l2) -- k j i
    → Cube (λ k j → compPath-filler l2 (sym l1) (~ j) k)
           (λ k j → F _ l2 l1 (sym q) _ l2 j k)
           (λ i j → x) q
           (λ i j →  (l2 ∙ sym l1) j) λ i j → l2 j
 
  H {x = x} = J> (J> (λ k i j →  F' {x = x} (~ k) j i))

  PushoutWedge : isContr (Pushout foldL foldR)
  fst PushoutWedge = inl (pt A)
  snd PushoutWedge (inl x) = l2 (pt B) ∙ sym (l1 x)
  snd PushoutWedge (inr x) = push (inr x)
  snd PushoutWedge (push (inl x) i) =
    compPath-filler (l2 (pt B)) (sym (l1 x)) (~ i)
  snd PushoutWedge (push (inr x) i) =
    F _ (l2 (pt B)) (l1 (pt A)) (sym l1≡l2) _ (push (inr x)) i
  snd PushoutWedge (push (push a i) j) k =
    H _ (l1 (pt A)) (l2 (pt B)) l1≡l2 i k j

  open BlakersMassey□ {A = A ⋁ B} {B = fst A} {C = fst B}
    foldL foldR (suc m) (suc n)
      (isConnectedFoldL cB) (isConnectedFoldR cA)

  lem : Iso (Σ (fst A × fst B) PushoutPath×) (fst A × fst B)
  lem = compIso (Σ-cong-iso-snd
    (λ _ → equivToIso (isContr→≃Unit (isOfHLevelPath 0 PushoutWedge _ _))))
      rUnit×Iso

  main : ⋁↪ ≡ Iso.fun lem ∘ toPullback
  main = funExt λ { (inl x) → refl
                  ; (inr x) → refl
                  ; (push a i) → refl}
  
isConnectedPickPetalSwap : {n k : ℕ}
  → isConnectedFun (suc n +ℕ suc n) (pickPetalSwap {n = suc n} {suc k}) 
isConnectedPickPetalSwap {n = n} {k = zero} =
  subst (isConnectedFun (suc n +ℕ suc n))
    (funExt (λ x → funExt (m x)))
    (isEquiv→isConnected _ (isoToIsEquiv h) _)
  where
  t = isContr→≃Unit (inhProp→isContr fzero isPropFin1)
  h : Iso (SphereBouquet (suc n) (Fin 1)) (Fin 1 → S₊ (suc n))
  h = compIso (compIso (compIso
     ((PushoutAlongEquiv t _))
      (compIso (Σ-cong-iso (equivToIso t) λ _ → idIso) lUnit×Iso))
      (invIso (ΠUnitIso ( λ _ → S₊ (suc n)))))
    (domIso (equivToIso (invEquiv t)))

  m :  (x : _) (y : _) → Iso.fun h x y ≡ pickPetalSwap x y
  m (inl x) y = refl
  m (inr ((zero , tt) , x)) (zero , tt) = refl
  m (push (zero , tt) i) (zero , tt) = refl
isConnectedPickPetalSwap {n = n} {k = suc k} =
  subst (isConnectedFun (suc n +ℕ suc n))
    (λ i x y → g≡ (isConnectedPickPetalSwap {k = k}) x y i)
    (isConnectedg (isConnectedPickPetalSwap {k = k}))
  where
  module _ {ℓ ℓ' ℓ''} {A : Type ℓ} {A' : Type ℓ'} {B : Type ℓ''}
    (f : A → A') where 
    l : (b : _) → Iso (fiber (map-× f (idfun B)) b) (fiber f (fst b))
    l (a , b) =
      compIso (Σ-cong-iso-snd (λ _ → invIso ΣPathIsoPathΣ))
        (compIso Σ-assoc-Iso
           (Σ-cong-iso-snd
            (λ x → compIso (invIso Σ-assoc-Iso)
              (compIso (Σ-cong-iso-fst Σ-swap-Iso)
                (compIso Σ-assoc-Iso
                  (compIso (Σ-cong-iso-snd
                    (λ s →
                      compIso (Σ-cong-iso-snd
                        λ b → iso sym sym (λ _ → refl) (λ _ → refl))
                        (equivToIso (isContr→≃Unit
                        (isContrSingl _)))))
                    rUnit×Iso))))))
    ll : ∀ {n} → isConnectedFun n f → isConnectedFun n (map-× f (idfun B))
    ll cf b = isConnectedRetractFromIso _ (l b) (cf (fst b))

  module _ (ind : isConnectedFun (suc n +ℕ suc n) (pickPetalSwap {n = suc n} {suc k})) where
    g : SphereBouquet (suc n) (Fin (suc (suc k)))
        → Fin (suc (suc k)) → S₊ (suc n)
    g = Iso.inv (Fin→BreakOutFirst (suc k))
      ∘ map-× (pickPetalSwap {n = suc n} {suc k}) (idfun _)
      ∘ ⋁↪
      ∘ Iso.fun breakOut⋁

    g≡inl : (y : _) → g (inl tt) y ≡ pickPetalSwap (inl tt) y
    g≡inl (zero , y) = refl
    g≡inl (suc s , y) = refl

    g≡inr : (x : _) (y : _) → g (inr x) y ≡ pickPetalSwap (inr x) y
    g≡inr ((zero , t) , q) (zero , p) = refl
    g≡inr ((zero , t) , q) (suc x , p) = refl
    g≡inr ((suc s , t) , q) (zero , p) = refl
    g≡inr ((suc s , t) , q) (suc x , p) with (x ≟ᵗ s)
    ... | lt x₁ = refl
    ... | eq x₁ = refl
    ... | gt x₁ = refl

    g≡inlr : (x : _) (y : _)
      → Square (λ i → g (push x i) y) (λ i → pickPetalSwap (push x i) y)
               (g≡inl y) (g≡inr (x , ptSn (suc n)) y)
    g≡inlr (zero , t) (zero , p) = refl
    g≡inlr (suc s , t) (zero , p) = refl
    g≡inlr (zero , t) (suc x , p) = refl
    g≡inlr (suc s , t) (suc x , p) with (x ≟ᵗ s)
    ... | lt x₁ = refl
    ... | eq x₁ = refl
    ... | gt x₁ = refl

    g≡ : (x : _) (y : _) → g x y ≡ pickPetalSwap x y
    g≡ (inl x) = g≡inl
    g≡ (inr x) = g≡inr x
    g≡ (push x i) y j = g≡inlr x y j i
  
    isConnectedg : isConnectedFun (suc n +ℕ suc n) g
    isConnectedg =
      isConnectedComp (Iso.inv (Fin→BreakOutFirst (suc k))) _ _
        (isEquiv→isConnected _
          (isoToIsEquiv (invIso (Fin→BreakOutFirst (suc k)))) (suc n +ℕ suc n))
        (isConnectedComp
          (map-× (pickPetalSwap {n = suc n} {suc k}) (idfun _)) _ (suc n +ℕ suc n)
          (ll _ ind)
          (isConnectedComp ⋁↪ _ _
            (isConnected⋁↪
                isConnectedSphereBouquet' (sphereConnected (suc n)))
            (isEquiv→isConnected _ (isoToIsEquiv breakOut⋁) (suc n +ℕ suc n))))

open import Cubical.Algebra.Group.Instances.Pi


ΠGroupHom : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {G : A → Group ℓ'} {H : A → Group ℓ''}
  → ((a : _) → GroupHom (G a) (H a))
  → GroupHom (ΠGroup G) (ΠGroup H)
fst (ΠGroupHom fam) f a = fst (fam a) (f a)
snd (ΠGroupHom fam) =
  makeIsGroupHom λ f g
    → funExt λ a → IsGroupHom.pres· (snd (fam a)) _ _

ΠGroupIso : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {G : A → Group ℓ'} {H : A → Group ℓ''}
  → ((a : _) → GroupIso (G a) (H a))
  → GroupIso (ΠGroup G) (ΠGroup H)
Iso.fun (fst (ΠGroupIso fam)) = fst (ΠGroupHom λ a → GroupIso→GroupHom (fam a))
Iso.inv (fst (ΠGroupIso fam)) =
  fst (ΠGroupHom λ a → GroupIso→GroupHom (invGroupIso (fam a)))
Iso.rightInv (fst (ΠGroupIso fam)) f = funExt λ x → Iso.rightInv (fst (fam x)) _
Iso.leftInv (fst (ΠGroupIso fam)) f = funExt λ x → Iso.leftInv (fst (fam x)) _
snd (ΠGroupIso fam) = snd (ΠGroupHom λ a → GroupIso→GroupHom (fam a))


πₙΠSⁿ≅ℤ : (n k : ℕ)
  → GroupIso (π'Gr n ((Fin k → S₊ (suc n)) , (λ _ → ptSn (suc n))))
              (AbGroup→Group ℤ[Fin k ])
πₙΠSⁿ≅ℤ n k = compGroupIso H' H2
  where
  is1 : (n : ℕ) → Iso (S₊∙ (suc n) →∙ ((Fin k → S₊ (suc n)) , (λ _ → ptSn (suc n))))
            (Fin k → S₊∙ (suc n) →∙ S₊∙ (suc n))
  fst (Iso.fun (is1 n) (f , s) x) y = f y x
  snd (Iso.fun (is1 n) (f , s) x) = funExt⁻ s x
  fst (Iso.inv (is1 n) f) y x = f x .fst y
  snd (Iso.inv (is1 n) f) i x = f x .snd i
  Iso.rightInv (is1 n) f = refl
  Iso.leftInv (is1 n) f = refl

  open import Cubical.Axiom.Choice
  open import Cubical.Homotopy.Group.PinSn
  open import Cubical.ZCohomology.Groups.Sn
  

  H : (n : ℕ)
    → Iso (π'Gr n ((Fin k → S₊ (suc n)) , (λ _ → ptSn (suc n))) .fst)
           (Fin k → π'Gr n (S₊∙ (suc n)) .fst)
  H n = compIso (setTruncIso (is1 n))
         (compIso
           setTruncTrunc2Iso
           (compIso (equivToIso (_ , InductiveFinSatAC 2 k _))
             (codomainIso (invIso setTruncTrunc2Iso))))

  H' : GroupIso (π'Gr n ((Fin k → S₊ (suc n)) , (λ _ → ptSn (suc n))))
                (ΠGroup (λ (x : Fin k) → π'Gr n (S₊∙ (suc n))))
  fst H' = H n
  snd H' = makeIsGroupHom (ST.elim2
    (λ _ _ → isOfHLevelPath 2 (isSetΠ (λ _ → squash₂)) _ _)
    λ f g → funExt λ x → cong ∣_∣₂ (h n f g x))
    where
    h : (n : ℕ) 
      → (f g : S₊∙ (suc n) →∙ ((Fin k → S₊ (suc n)) , (λ _ → ptSn (suc n))))
      → (x : _) → Iso.fun (is1 n) (∙Π f g) x
                 ≡ ∙Π (Iso.fun (is1 n) f x) (Iso.fun (is1 n) g x)
    h zero f g x = ΣPathP ((funExt (λ { base → refl ; (loop i) → refl})) , refl)
    h (suc n) f g x =
      ΣPathP ((funExt (λ { north → refl ; south → refl ; (merid a i) → refl })) , refl)

  H2 : GroupIso (ΠGroup (λ (x : Fin k) → π'Gr n (S₊∙ (suc n))))
                (AbGroup→Group ℤ[Fin k ])
  H2 = ΠGroupIso λ _
    → compGroupIso (GroupEquiv→GroupIso (πₙSⁿ≅HⁿSⁿ n))
                    (Hⁿ-Sⁿ≅ℤ n)

πₙ⋁Sⁿ≅ℤ[] : (n k : ℕ)
  → GroupIso (π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k)))
              (AbGroup→Group ℤ[Fin k ])
πₙ⋁Sⁿ≅ℤ[] n k =
  compGroupIso
    (GroupEquiv→GroupIso (connected→π'Equiv (suc n)
      (pickPetalSwap , refl) (con k)))
    (πₙΠSⁿ≅ℤ (suc n) k)
  where
  con : (k : _) → isConnectedFun (suc (suc (suc (suc n)))) (pickPetalSwap {k = k})
  con zero b = ∣ (inl tt) , (funExt λ ()) ∣
    , TR.elim (λ _ → isOfHLevelPath _ (isOfHLevelTrunc (suc (suc (suc (suc n))))) _ _)
       λ {((inl tt) , q) → cong ∣_∣ₕ (ΣPathP (refl , cong funExt (funExt λ())))}
  con (suc k) b = isConnectedSubtr (suc (suc (suc (suc n)))) n
           (subst (λ p → isConnected p (fiber pickPetalSwap b))
             (cong suc (sym (+-suc _ _)) ∙ sym (+-suc _ _))
             (isConnectedPickPetalSwap b))

genπₙ⋁Sⁿ : {n k : ℕ} (x : Fin k) → π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k)) .fst
genπₙ⋁Sⁿ x = ∣ (λ s → inr (x , s)) , (sym (push x)) ∣₂

πₙ⋁Sⁿ≅ℤ[]Gen : (n k : ℕ) (x : Fin k)
  → Iso.fun (fst (πₙ⋁Sⁿ≅ℤ[] n k)) (genπₙ⋁Sⁿ x)
  ≡ ℤFinGenerator x
πₙ⋁Sⁿ≅ℤ[]Gen n k x = funExt pickPetalId
  where
  pickPetalId : (w : _)
    → degree (suc (suc n)) (λ z → pickPetalSwap (inr (x , z)) w) ≡
      ℤFinGenerator x w
  pickPetalId w with (fst x ≟ᵗ fst w) | (fst w ≟ᵗ fst x)
  ... | lt x | lt x₁ = degreeConst (suc (suc n))
  ... | lt p | eq q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst w) (sym q) p))
  ... | lt x | gt x₁ = degreeConst (suc (suc n))
  ... | eq p | lt q = ⊥.rec (⊥.rec (¬m<ᵗm (subst (fst w <ᵗ_) p q)))
  ... | eq x | eq x₁ = degreeIdfun (suc (suc n))
  ... | eq p | gt q = ⊥.rec (¬m<ᵗm (subst (fst x <ᵗ_) (sym p) q))
  ... | gt x | lt x₁ = degreeConst (suc (suc n))
  ... | gt p | eq q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst x) q p))
  ... | gt x | gt x₁ = degreeConst (suc (suc n))

πₙ⋁SⁿHomElim : {n k k' : ℕ}
  → (ϕ ψ : GroupHom (π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k))) (AbGroup→Group ℤ[Fin k' ]))
  → ((x  : Fin k) → fst ϕ (genπₙ⋁Sⁿ x) ≡ fst ψ (genπₙ⋁Sⁿ x))
  → ϕ ≡ ψ
πₙ⋁SⁿHomElim {n = n} {k} {k'} ϕ ψ ind =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _) (funExt λ x
    → cong (fst ϕ) (sym (Iso.leftInv (fst (πₙ⋁Sⁿ≅ℤ[] n k)) x))
    ∙ funExt⁻ (cong fst help) (Iso.fun (fst (πₙ⋁Sⁿ≅ℤ[] n k)) x)
    ∙ cong (fst ψ) (Iso.leftInv (fst (πₙ⋁Sⁿ≅ℤ[] n k)) x))
  where
  help : compGroupHom (GroupIso→GroupHom (invGroupIso (πₙ⋁Sⁿ≅ℤ[] n k))) ϕ
       ≡ compGroupHom (GroupIso→GroupHom (invGroupIso (πₙ⋁Sⁿ≅ℤ[] n k))) ψ
  help = agreeOnℤFinGenerator→≡
    λ x → cong (fst ϕ) (cong (Iso.inv (fst (πₙ⋁Sⁿ≅ℤ[] n k))) (sym (πₙ⋁Sⁿ≅ℤ[]Gen n k x))
                     ∙ Iso.leftInv (fst (πₙ⋁Sⁿ≅ℤ[] n k)) (genπₙ⋁Sⁿ x))
        ∙ ind x
        ∙ cong (fst ψ) (sym (Iso.leftInv (fst (πₙ⋁Sⁿ≅ℤ[] n k)) (genπₙ⋁Sⁿ x))
                    ∙ sym (cong (Iso.inv (fst (πₙ⋁Sⁿ≅ℤ[] n k))) (sym (πₙ⋁Sⁿ≅ℤ[]Gen n k x))))

open import Cubical.Homotopy.Group.LES
open import Cubical.Algebra.Group.IsomorphismTheorems
module πCofibBouquetMap (n k m : ℕ) (α : SphereBouquet∙ (suc (suc n)) (Fin m) →∙ SphereBouquet∙ (suc (suc n)) (Fin k)) where

  inr' : SphereBouquet∙ (suc (suc n)) (Fin k) →∙ (cofib (fst α) , inl tt)
  fst inr' = inr
  snd inr' = (λ i → inr (α .snd (~ i))) ∙ sym (push (inl tt))


  conα : isConnectedFun (suc (suc n)) (fst α)
  conα b =
    isOfHLevelRetractFromIso 0
      (compIso (truncOfΣIso (suc (suc n)))
        (mapCompIso (compIso (Σ-cong-iso-snd
          (λ _ → equivToIso (isContr→≃Unit
            (isConnectedPath (suc (suc n))
              (isConnectedSphereBouquet' {n = suc n}) _ _)))) rUnit×Iso)))
              (isConnectedSubtr (suc (suc n)) 1 isConnectedSphereBouquet')

  coninr : isConnectedFun (suc (suc (suc n))) (fst inr')
  coninr = inrConnected (suc (suc (suc n))) _ _
    (isConnected→isConnectedFun (suc (suc (suc n)))
      isConnectedSphereBouquet')

  open BlakersMassey□ (λ _ → tt) (fst α) (suc (suc n)) (suc n)
    (isConnected→isConnectedFun _ (isConnectedSphereBouquet' {n = suc n}))
    conα
  is1 : Iso (Σ (Unit × fst (SphereBouquet∙ (suc (suc n)) (Fin k))) PushoutPath×)
            (fiber (fst inr') (inl tt))
  Iso.fun is1 ((tt , s) , p) = s , (sym p)
  Iso.inv is1 (s , p) = (tt , s) , sym p
  Iso.rightInv is1 (s , p) = refl
  Iso.leftInv is1 ((tt , s) , p) = refl

  α∘inr : SphereBouquet∙ (suc (suc n)) (Fin m)
      →∙ (fiber (fst inr') (inl tt) , (inl tt) , inr' .snd)
  fst α∘inr x = (fst α x) , sym (push x)
  snd α∘inr = ΣPathP ((snd α)
            , (compPath-filler' (λ i → inr (α .snd (~ i))) (sym (push (inl tt)))))

  open πLES' inr'
  
  con' : isConnectedFun (suc (suc n +ℕ suc n)) (α∘inr .fst)
  con' = isConnectedComp _ _ _ (isEquiv→isConnected _ (isoToIsEquiv is1) _) isConnected-toPullback

  con'' : isSurjective (π'∘∙Hom (suc n) α∘inr)
  con'' =
    connected→π'Surj (suc n) _
      λ b → isConnectedSubtr' n (suc (suc (suc n)))
        (subst (λ n → isConnected (suc (suc n)) (fiber (fst α∘inr) b)) (+-suc n n) (con' b))

  surjectiveα : isSurjective (π'∘∙Hom (suc n) inr')
  surjectiveα = connected→π'Surj (suc n) _ coninr

  Iso1 : GroupIso (π'Gr (suc n) (cofib (fst α) , inl tt))
                  (π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k))
                  / kerNormalSubgroup (π'∘∙Hom (suc n) inr'))
  Iso1 = compGroupIso (invGroupIso (surjImIso (π'∘∙Hom (suc n) inr') surjectiveα))
                      (isoThm1 _)

  Imα⊂Kerinr : (x : _) → isInIm (π'∘∙Hom (suc n) α) x → isInKer (π'∘∙Hom (suc n) inr') x
  Imα⊂Kerinr x p = Im-fib→A⊂Ker-A→B (suc n) x
    (PT.rec squash₁ (uncurry (ST.elim (λ _ → isSetΠ λ _ → isProp→isSet squash₁)
      (λ a → J (λ x _ → isInIm (fib→A (suc n)) x)
        ∣ (π'∘∙Hom (suc n) α∘inr .fst ∣ a ∣₂)
        , (cong ∣_∣₂ (ΣPathP (refl , (sym (rUnit _)
        ∙ cong-∙ fst (ΣPathP ((cong (fst α) (snd a))
                    , λ i j → push (snd a i) (~ j))) _)))) ∣₁))) p)

  Kerinr⊂Imα : (x : _) → isInKer (π'∘∙Hom (suc n) inr') x → isInIm (π'∘∙Hom (suc n) α) x
  Kerinr⊂Imα x p =
    PT.rec squash₁
      (uncurry ( λ f → J (λ x _ → isInIm (π'∘∙Hom (suc n) α) x)
          (PT.rec squash₁ (uncurry
            (ST.elim (λ _ → isSetΠ λ _ → isProp→isSet squash₁)
              (λ g s → ∣ ∣ g ∣₂ , cong ∣_∣₂
                (ΣPathP (refl
                  , sym (cong-∙ fst (ΣPathP ((cong (fst α) (snd g))
                    , (λ i j → push (snd g i) (~ j)))) _) ∙ rUnit _))
                ∙ cong (fib→A (suc n) .fst) s ∣₁))) (con'' f))))
      (Ker-A→B⊂Im-fib→A (suc n) x p)

  Iso2 : GroupIso (π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k))
                  / kerNormalSubgroup (π'∘∙Hom (suc n) inr'))
                  (π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k))
                  / imNormalSubgroup (π'∘∙Hom (suc n) α) (π'-comm n))
  Iso2 = Hom/Iso idGroupIso (λ a b → Kerinr⊂Imα _) λ a b → Imα⊂Kerinr _

  open import Cubical.ZCohomology.Groups.Sn
  open import Cubical.Homotopy.Group.PinSn

  Iso3 : GroupIso ((π'Gr (suc n) (SphereBouquet∙ (suc (suc n)) (Fin k))
                  / imNormalSubgroup (π'∘∙Hom (suc n) α) (π'-comm n)))
                  (AbGroup→Group ℤ[Fin k ] / (imSubgroup (bouquetDegree (fst α))
                                             , isNormalIm _ λ f g i x → +Comm (f x) (g x) i ))
  Iso3 = (Hom/ImIso _ _ ( (πₙ⋁Sⁿ≅ℤ[] n m)) ( (πₙ⋁Sⁿ≅ℤ[] n k))
          (funExt⁻ (cong fst (πₙ⋁SⁿHomElim H1 H2
            λ s → funExt (λ x → sumFinℤId m (λ r → sym (degreeComp' (suc (suc n)) _ _))
                                ∙ sumFin-choose  _+_ 0 (λ _ → refl) +Comm _ _ s
                                  (cong (degree (suc (suc n)))
                                    (funExt (λ w → cong (pickPetal x ∘ fst α ∘ inr) (ΣPathP (refl , l1 s w)))))
                                  (λ w p → cong (degree (suc (suc n)))
                                      (funExt (λ r → cong (pickPetal x ∘ fst α) (p1 s x w r p)
                                                   ∙ (cong (pickPetal x) (snd α))))
                                    ∙ degreeConst (suc (suc n)))
                                ∙ cong (degree (suc (suc n))) refl)))))
      where
      l1 : (s : Fin m) (w : S₊ (suc (suc n))) → pickPetal s (inr (s , w)) ≡ w
      l1 s w with (fst s ≟ᵗ fst s)
      ... | lt x = ⊥.rec (¬m<ᵗm x)
      ... | eq x = refl
      ... | gt x = ⊥.rec (¬m<ᵗm x)
      H1 = compGroupHom (GroupIso→GroupHom (( (πₙ⋁Sⁿ≅ℤ[] n m)))) (bouquetDegree (fst α))
      H2 = compGroupHom  (π'∘∙Hom (suc n) α) ((GroupIso→GroupHom (πₙ⋁Sⁿ≅ℤ[] n k)))

      p1 : (s : Fin m) (x : Fin k) (w : Fin m) (r : Susp (S₊ (suc n))) (p : ¬ w ≡ s)
        → Path (SphereBouquet (suc (suc n)) (Fin m))
               (inr (w , pickPetalSwap (inr (s , r)) w)) (inl tt)
      p1 s x w r p with (fst w ≟ᵗ fst s)
      ... | lt x₁ = sym (push w)
      ... | eq x₁ = ⊥.rec (p (Σ≡Prop (λ _ → isProp<ᵗ) x₁))
      ... | gt x₁ = sym (push w)


-- Free/≅π₁ᵃᵇCofibBouquetMap

π'CofibBouquetMap≅ℤ[]/BouquetDegree : {n m k : ℕ}
  (α : SphereBouquet∙ (suc (suc n)) (Fin m)
   →∙ SphereBouquet∙ (suc (suc n)) (Fin k))
  → GroupIso (π'Gr (suc n) (cofib (fst α) , inl tt))
              (AbGroup→Group ℤ[Fin k ]
              / (imSubgroup (bouquetDegree (fst α)) , isNormalIm _ λ f g i x → +Comm (f x) (g x) i))
π'CofibBouquetMap≅ℤ[]/BouquetDegree {n = n} {m} {k} α =
  compGroupIso (compGroupIso (πCofibBouquetMap.Iso1 n k m α)
                             (πCofibBouquetMap.Iso2 n k m α))
                             (πCofibBouquetMap.Iso3 n k m α)


elimPropBouquet : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Bouquet A → Type ℓ'}
  (pr : (x : _) → isProp (B x))
  (b : B base)
  → (x  : Bouquet A) → B x
elimPropBouquet pr b base = b
elimPropBouquet {B = B} pr b (loop x i) =
  isProp→PathP {B = λ i → B (loop x i)} (λ _ → pr _) b b i

Iso-ΩS¹Bouquet-FreeGroup : {n : ℕ} → Iso (fst (Ω (Bouquet∙ (Fin n)))) (FreeGroup (Fin n))
Iso-ΩS¹Bouquet-FreeGroup =
  compIso
    (compIso (invIso (setTruncIdempotentIso (isOfHLevelPath' 2
      (isGroupoidBouquet DiscreteFin) _ _)))
             (equivToIso (TruncatedFamiliesEquiv base)))
    (equivToIso (invEquiv freeGroupTruncIdempotent≃))

open import Cubical.HITs.FreeGroupoid.Base as FGrp

InvIso-ΩS¹Bouquet-FreeGroupPresStr : {n : ℕ} (x y : FreeGroup (Fin n))
  → Iso.inv Iso-ΩS¹Bouquet-FreeGroup (FG._·_ x y)
   ≡ Iso.inv Iso-ΩS¹Bouquet-FreeGroup x ∙ Iso.inv Iso-ΩS¹Bouquet-FreeGroup y
InvIso-ΩS¹Bouquet-FreeGroupPresStr x y =
  cong (F ∘ G) (l1 x y) ∙ l2 (H x) (H y)
  where
  F = Iso.fun (setTruncIdempotentIso (isOfHLevelPath' 2 (isGroupoidBouquet DiscreteFin) _ _))
  G = invEq (TruncatedFamiliesEquiv base)
  H = fst freeGroupTruncIdempotent≃

  l2 : (x y : _) → F (G (ST.rec2 squash₂ (λ x y → ∣ x FGrp.· y ∣₂) x y))
                 ≡ F (G x) ∙ F (G y)
  l2 = ST.elim2 (λ _ _ → isOfHLevelPath 2
                 (isOfHLevelPath' 2 (isGroupoidBouquet DiscreteFin) _ _) _ _)
                 λ _ _ → refl

  l1 : (x t : _) → H (x FG.· t) ≡ ST.rec2 squash₂ (λ x y → ∣ x FGrp.· y ∣₂) (H x) (H t) 
  l1 x t = cong H (cong₂ FG._·_ (sym (retEq freeGroupTruncIdempotent≃ _))
                                (sym (retEq freeGroupTruncIdempotent≃ _)))
         ∙ cong H (sym (h (H x) (H t)))
         ∙ secEq freeGroupTruncIdempotent≃ _
    where
    h : (x y : _) → invEq freeGroupTruncIdempotent≃ (ST.rec2 squash₂ (λ x y → ∣ x FGrp.· y ∣₂) x y)
                  ≡ (invEq freeGroupTruncIdempotent≃ x FG.· invEq freeGroupTruncIdempotent≃ y)
    h = ST.elim2 (λ _ _ → isOfHLevelPath 2 trunc _ _) λ _ _ → refl

InvIso-ΩS¹Bouquet-FreeGroupPresInv : {n : ℕ} (x : FreeGroup (Fin n))
  → Iso.inv Iso-ΩS¹Bouquet-FreeGroup (FG.inv x)
   ≡ sym (Iso.inv Iso-ΩS¹Bouquet-FreeGroup x)
InvIso-ΩS¹Bouquet-FreeGroupPresInv {n = n} =
  morphLemmas.distrMinus FG._·_ _∙_ (Iso.inv (Iso-ΩS¹Bouquet-FreeGroup {n = n}))
    InvIso-ΩS¹Bouquet-FreeGroupPresStr ε refl inv sym
      (sym ∘ lUnit) (sym ∘ rUnit) FG.invl rCancel GLaws.assoc refl

module _ {ℓ} {A : Type ℓ} where
  SphereBouquet→Bouquet : SphereBouquet 1 A → Bouquet A
  SphereBouquet→Bouquet (inl x) = base
  SphereBouquet→Bouquet (inr (s , base)) = base
  SphereBouquet→Bouquet (inr (s , loop i)) = loop s i
  SphereBouquet→Bouquet (push a i) = base

  Bouquet→SphereBouquet : Bouquet A → SphereBouquet 1 A
  Bouquet→SphereBouquet base = inl tt
  Bouquet→SphereBouquet (loop x i) =
    (push x ∙∙ (λ i → inr (x , loop i)) ∙∙ sym (push x)) i

  Iso-SphereBouquet-Bouquet : Iso (SphereBouquet 1 A) (Bouquet A)
  Iso.fun Iso-SphereBouquet-Bouquet = SphereBouquet→Bouquet
  Iso.inv Iso-SphereBouquet-Bouquet = Bouquet→SphereBouquet
  Iso.rightInv Iso-SphereBouquet-Bouquet base = refl
  Iso.rightInv Iso-SphereBouquet-Bouquet (loop x i) j =
    SphereBouquet→Bouquet
      (doubleCompPath-filler (push x) (λ i → inr (x , loop i)) (sym (push x)) (~ j) i)
  Iso.leftInv Iso-SphereBouquet-Bouquet (inl x) = refl
  Iso.leftInv Iso-SphereBouquet-Bouquet (inr (s , base)) = push s
  Iso.leftInv Iso-SphereBouquet-Bouquet (inr (s , loop i)) j =
    doubleCompPath-filler (push s) (λ i → inr (s , loop i)) (sym (push s)) (~ j) i
  Iso.leftInv Iso-SphereBouquet-Bouquet (push a i) j = push a (i ∧ j)

  Bouquet≃∙SphereBouquet : SphereBouquet∙ 1 A ≃∙ Bouquet A , base
  fst Bouquet≃∙SphereBouquet = isoToEquiv (Iso-SphereBouquet-Bouquet)
  snd Bouquet≃∙SphereBouquet = refl

makeSphereBouquetFun : {m k : ℕ}
  → (Fin m → FreeGroup (Fin k))
    →  SphereBouquet∙ (suc zero) (Fin m)
    →∙ SphereBouquet∙ (suc zero) (Fin k)
fst (makeSphereBouquetFun F) (inl x) = inl tt
fst (makeSphereBouquetFun F) (inr (s , base)) = inl tt
fst (makeSphereBouquetFun F) (inr (s , loop i)) =
  cong Bouquet→SphereBouquet (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (F s)) i
fst (makeSphereBouquetFun F) (push a i) = inl tt
snd (makeSphereBouquetFun F) = refl

makeSphereBouquetFun' : {m k : ℕ}
  → (Fin m → FreeGroup (Fin k))
    →  Bouquet∙ (Fin m)
    →∙ Bouquet∙ (Fin k)
fst (makeSphereBouquetFun' f) base = base
fst (makeSphereBouquetFun' f) (loop x i) = Iso.inv Iso-ΩS¹Bouquet-FreeGroup (f x) i
snd (makeSphereBouquetFun' f) = refl

FAGAbGroup→AbGroupHom : ∀ {ℓ ℓ'} {A : Type ℓ} {G : AbGroup ℓ'}
  → (A → fst G) → AbGroupHom (FAGAbGroup {A = A}) G
fst (FAGAbGroup→AbGroupHom {G = G} f) =
  Rec.f (AbGroupStr.is-set (snd G)) f
    (AbGroupStr.0g (snd G)) (AbGroupStr._+_ (snd G)) (AbGroupStr.-_ (snd G))
    (AbGroupStr.+Assoc (snd G)) (AbGroupStr.+Comm (snd G))
    (AbGroupStr.+IdR (snd G)) (AbGroupStr.+InvR (snd G))
snd (FAGAbGroup→AbGroupHom {G = G} f) = makeIsGroupHom λ x y → refl

FAGAbGroupGroupHom≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {G : AbGroup ℓ'}(f g : AbGroupHom (FAGAbGroup {A = A}) G)
               → (∀ a → (fst f) (⟦ a ⟧) ≡ (fst g) (⟦ a ⟧)) → f ≡ g
FAGAbGroupGroupHom≡ {G = G} f g p =
  GroupHom≡ (funExt (ElimProp.f (AbGroupStr.is-set (snd G) _ _)
    p (IsGroupHom.pres1 (snd f) ∙ sym (IsGroupHom.pres1 (snd g)))
    (λ p q → IsGroupHom.pres· (snd f) _ _
            ∙ cong₂ (AbGroupStr._+_ (snd G)) p q
            ∙ sym (IsGroupHom.pres· (snd g) _ _))
    λ p → IsGroupHom.presinv (snd f) _
        ∙ cong (AbGroupStr.-_ (snd G)) p
        ∙ sym (IsGroupHom.presinv (snd g) _)))

module _ {ℓ} {A : Type ℓ} where
  freeGroup→freeAbGroup : GroupHom (freeGroupGroup A) (AbGroup→Group (FAGAbGroup {A = A}))
  freeGroup→freeAbGroup = FG.rec {Group = AbGroup→Group (FAGAbGroup {A = A})} ⟦_⟧

  AbelienizeFreeGroup→FreeAbGroup : AbGroupHom (AbelianizationAbGroup (freeGroupGroup A)) (FAGAbGroup {A = A})
  AbelienizeFreeGroup→FreeAbGroup = fromAbelianization FAGAbGroup freeGroup→freeAbGroup

  FreeAbGroup→AbelienizeFreeGroup : AbGroupHom (FAGAbGroup {A = A}) (AbelianizationAbGroup (freeGroupGroup A))
  FreeAbGroup→AbelienizeFreeGroup = FAGAbGroup→AbGroupHom λ a → η (η a)

  GroupIso-AbelienizeFreeGroup→FreeAbGroup :
    AbGroupIso (AbelianizationAbGroup (freeGroupGroup A)) (FAGAbGroup {A = A})
  Iso.fun (fst GroupIso-AbelienizeFreeGroup→FreeAbGroup) = AbelienizeFreeGroup→FreeAbGroup .fst
  Iso.inv (fst GroupIso-AbelienizeFreeGroup→FreeAbGroup) = FreeAbGroup→AbelienizeFreeGroup .fst
  Iso.rightInv (fst GroupIso-AbelienizeFreeGroup→FreeAbGroup) x i =
    FAGAbGroupGroupHom≡
      (compGroupHom FreeAbGroup→AbelienizeFreeGroup AbelienizeFreeGroup→FreeAbGroup)
      idGroupHom (λ _ → refl) i .fst x
  Iso.leftInv (fst GroupIso-AbelienizeFreeGroup→FreeAbGroup) = Abi.elimProp _ (λ _ → isset _ _)
    (funExt⁻ (cong fst (freeGroupHom≡
      {f = compGroupHom  freeGroup→freeAbGroup FreeAbGroup→AbelienizeFreeGroup }
      {g = AbelianizationGroupStructure.ηAsGroupHom (freeGroupGroup A)}
      λ _ → refl)))
  snd GroupIso-AbelienizeFreeGroup→FreeAbGroup = AbelienizeFreeGroup→FreeAbGroup .snd

open import Cubical.Foundations.Powerset
module _ {ℓ ℓ'} {A : Type ℓ} (B : Pointed ℓ') where
  BouquetFun∙→Ω : (Bouquet∙ A →∙ B) → (A → Ω B .fst)
  BouquetFun∙→Ω f x = sym (snd f) ∙∙ cong (fst f) (loop x) ∙∙ snd f

  Ω→BouquetFun∙ : (A → Ω B .fst) → (Bouquet∙ A →∙ B)
  fst (Ω→BouquetFun∙ f) base = pt B
  fst (Ω→BouquetFun∙ f) (loop x i) = f x i
  snd (Ω→BouquetFun∙ f) = refl

  CharacBouquetFun∙ : Iso (Bouquet∙ A →∙ B) (A → Ω B .fst)
  Iso.fun CharacBouquetFun∙ = BouquetFun∙→Ω
  Iso.inv CharacBouquetFun∙ = Ω→BouquetFun∙
  Iso.rightInv CharacBouquetFun∙ h =
    funExt λ x → sym (rUnit (h x))
  fst (Iso.leftInv CharacBouquetFun∙ h i) base = snd h (~ i)
  fst (Iso.leftInv CharacBouquetFun∙ h i) (loop x j) =
    doubleCompPath-filler (sym (snd h)) (cong (fst h) (loop x)) (snd h) (~ i) j
  snd (Iso.leftInv CharacBouquetFun∙ h i) j = snd h (~ i ∨ j)


CharacBouquet→∙Bouquet : {m k : ℕ}
  → Iso (Bouquet∙ (Fin m) →∙ Bouquet∙ (Fin k))
         (Fin m → FreeGroup (Fin k))
CharacBouquet→∙Bouquet = compIso (CharacBouquetFun∙ (Bouquet∙ (Fin _)))
  (codomainIso Iso-ΩS¹Bouquet-FreeGroup)

sphereBouqetMapIso : {m k : ℕ} → Iso (Bouquet∙ (Fin m) →∙ Bouquet∙ (Fin k))
 (SphereBouquet∙ (suc zero) (Fin m) →∙ SphereBouquet∙ (suc zero) (Fin k))
sphereBouqetMapIso =
 compIso (pre∘∙equiv (invEquiv∙ Bouquet≃∙SphereBouquet))
         (post∘∙equiv (invEquiv∙ Bouquet≃∙SphereBouquet))

module spB {m k : ℕ}
  (α' : Fin m → FreeGroup (Fin k)) where
  α :  Bouquet∙ (Fin m)
    →∙ Bouquet∙ (Fin k)
  α = Iso.inv CharacBouquet→∙Bouquet α'

  αSphereBouquet : SphereBouquet∙ (suc zero) (Fin m) →∙ SphereBouquet∙ (suc zero) (Fin k)
  αSphereBouquet = Iso.fun sphereBouqetMapIso α

  pickGens : GroupHom (freeGroupGroup (Fin m)) (freeGroupGroup (Fin k))
  pickGens = FG.rec α'

  pickGens' : AbGroupHom (AbelianizationAbGroup (freeGroupGroup (Fin m))) ((AbelianizationAbGroup (freeGroupGroup (Fin k))))
  pickGens' = AbelianizationFun pickGens

  _·f_ : ∀ {ℓ} {A : Type ℓ} → FreeGroup A → FreeGroup A → FreeGroup A
  _·f_ = FG._·_

  Free/Imα' : Group₀
  Free/Imα' = AbGroup→Group (AbelianizationAbGroup (freeGroupGroup (Fin k)))
            / (imSubgroup pickGens' , isNormalIm _ λ _ _ → AbelianizationGroupStructure.commAb _ _ _)

  Code' : Fin k → S¹ → Type₀
  Code' k base = Free/Imα' .fst
  Code' k (loop i) = ua (isoToEquiv (·GroupAutomorphismR (Free/Imα') [ η (η k) ])) i

  CodePre : Bouquet (Fin k) → Type
  CodePre base = Free/Imα' .fst
  CodePre (loop x i) = ua (isoToEquiv (·GroupAutomorphismR (Free/Imα') [ η (η x) ])) i


  substCodePre : (p : _) (x : _)
    → subst CodePre (Iso.inv Iso-ΩS¹Bouquet-FreeGroup p) [ η x ]
     ≡ [ η (x FG.· p)  ]
  substCodePre = FG.elimProp (λ _ → isPropΠ (λ _ → squash/ _ _))
    (λ a x i → [ η (transportRefl x i FG.· η (transportRefl a i)) ])
    (λ g1 g2 p q x
      → cong (λ P → subst CodePre P [ η x ])
             (InvIso-ΩS¹Bouquet-FreeGroupPresStr g1 g2)
      ∙ substComposite CodePre
         (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g1)
         (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g2) [ η x ]
      ∙ cong (subst CodePre (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g2))
             (p x)
      ∙ q (x FG.· g1)
      ∙ λ i → [ η (FG.assoc x g1 g2 (~ i)) ])
    (λ x i → [ η ((transportRefl x ∙ FG.idr x) i) ])
    λ g p x → cong (λ P → subst CodePre P [ η x ])
                (InvIso-ΩS¹Bouquet-FreeGroupPresInv g)
             ∙ cong (subst CodePre (sym (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g)))
                 (λ i → [ η ((FG.idr x
                           ∙ cong₂ FG._·_ refl (sym (FG.invl g))
                           ∙ (FG.assoc x (inv g) g)) i) ])
             ∙ sym (cong (subst CodePre (sym (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g)))
                     (p (x FG.· inv g)))
             ∙ subst⁻Subst CodePre (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g )
               [ η (x FG.· inv g) ]


  CodeCofibα : cofib (fst α) → Type
  CodeCofibα (inl x) = Free/Imα' .fst
  CodeCofibα (inr x) = CodePre x
  CodeCofibα (push base i) = Free/Imα' .fst
  CodeCofibα (push (loop x j) i) = H i j
    where
    open AbelianizationGroupStructure (freeGroupGroup (Fin k))
    H : refl ≡ cong (CodePre) (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (α' x))
    H = sym uaIdEquiv
          ∙ cong ua (Σ≡Prop (λ _ → isPropIsEquiv _)
            (funExt (SQ.elimProp (λ _ → squash/ _ _)
              (Abi.elimProp _ (λ _ → squash/ _ _)
                λ g → sym (substCodePre (α' x) g
                    ∙ eq/ _ _ ∣ (η (η x))
                             , (sym (ridAb (η (α' x)))
                             ∙ commAb (η (α' x)) 1Ab)
                             ∙ cong₂ _·Ab_ (sym (rinvAb (η g))) refl
                             ∙ sym (assocAb (η g) (η (inv g)) (η (α' x)))
                             ∙ cong₂ _·Ab_ refl (commAb (η (inv g)) (η (α' x)))
                             ∙ assocAb (η g) (η (α' x)) (η (inv g)) ∣₁)))))
          ∙ retEq univalence _


  isSetCodeCofibα : (x : _) → isSet (CodeCofibα x)
  isSetCodeCofibα =
    PO.elimProp _ (λ _ → isPropIsSet)
      (λ _ → GroupStr.is-set (Free/Imα' .snd))
      (elimPropBouquet
        (λ _ → isPropIsSet)
        (GroupStr.is-set (Free/Imα' .snd)))

  L : GroupHom (freeGroupGroup (Fin k))
      (πGr 0 (Pushout (λ _ → tt) (fst α) , inr base))
  fst L b = ∣ (λ i → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup b i)) ∣₂
  snd L = makeIsGroupHom λ a b
    → cong ∣_∣₂ ((λ i j → inr (InvIso-ΩS¹Bouquet-FreeGroupPresStr a b i j))
      ∙ cong-∙ inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup a)
                   (Iso.inv Iso-ΩS¹Bouquet-FreeGroup b))

  Lα : (x : Fin m) → Path (Path (cofib (fst α)) (inr base) (inr base))
                       (λ i → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (α' x) i))
                       refl
  Lα x i j = hcomp (λ k → λ {(i = i0) → push (loop x j) k
                           ; (i = i1) → push base k
                           ; (j = i0) → push base k
                           ; (j = i1) → push base k})
                  (inl tt)


  decodeCofibαinrFun : FreeGroup (Fin k) → ∥ _≡ᵃᵇ_ {A = cofib (fst α)} (inr base) (inr base) ∥₂
  decodeCofibαinrFun s = ∣ paths ((λ i → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup s i))) ∣₂

  decodeCofibαinlFun : FreeGroup (Fin k) → ∥ _≡ᵃᵇ_ {A = cofib (fst α)} (inr base) (inl tt) ∥₂
  decodeCofibαinlFun s = ·πᵃᵇ (decodeCofibαinrFun s) ∣ paths (sym (push base)) ∣₂

  decodeCofibαinr : Abelianization (freeGroupGroup (Fin k)) → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr base) ∥₂
  decodeCofibαinr = fst Abelianizeπ₁→π₁ᵃᵇ ∘ AbelianizationFun L .fst

  inr' : Bouquet (Fin k) → cofib (fst α)
  inr' = inr

  decodeCofibαinrHom : AbGroupHom (AbelianizationAbGroup (freeGroupGroup (Fin k)))
                                  (π₁ᵃᵇAbGroup (cofib (fst α) , inr base))
  decodeCofibαinrHom = compGroupHom (AbelianizationFun L) Abelianizeπ₁→π₁ᵃᵇ

  decodeCofibαinr≡ : (x : Abelianization (freeGroupGroup (Fin m))) → (a : FreeGroup (Fin k))
    → ·πᵃᵇ (decodeCofibαinr (pickGens' .fst x)) (decodeCofibαinr (η a)) ≡ decodeCofibαinr (η a)
  decodeCofibαinr≡ = Abi.elimProp _ (λ _ → isPropΠ λ _ → squash₂ _ _)
    (FG.elimProp (λ _ → isPropΠ λ _ → squash₂ _ _)
    (λ c a → (λ i → ·πᵃᵇ ∣ paths (Lα c i) ∣₂ (decodeCofibαinr (η a)))
                 ∙ cong ∣_∣₂ (cong paths (sym (lUnit _))))
    (λ g1 g2 p q a
      → cong₂ ·πᵃᵇ (cong decodeCofibαinr (IsGroupHom.pres· (snd pickGens') (η g1) (η g2))
                 ∙ IsGroupHom.pres· (snd (compGroupHom (AbelianizationFun L) (Abelianizeπ₁→π₁ᵃᵇ)))
                                    (fst pickGens' (η g1)) (fst pickGens' (η g2)))
               (λ _ → (decodeCofibαinr (η a)))
                    ∙ sym (·πᵃᵇassoc (decodeCofibαinr (pickGens' .fst (η g1)))
                                    (decodeCofibαinr (pickGens' .fst (η g2))) (decodeCofibαinr (η a)))
                    ∙ cong (·πᵃᵇ (decodeCofibαinr (pickGens' .fst (η g1)))) (q a)
                    ∙ p a)
      (λ a → ·πᵃᵇlUnit (decodeCofibαinr (η a)))
      λ g p a → cong₂ ·πᵃᵇ
                  (sym (sym (IsGroupHom.presinv (snd (compGroupHom (AbelianizationFun L)
                          (Abelianizeπ₁→π₁ᵃᵇ))) (pickGens' .fst (η g)))
                    ∙ cong decodeCofibαinr (IsGroupHom.presinv (snd pickGens') (η g))))
                  (sym (sym (IsGroupHom.presinv (snd (compGroupHom (AbelianizationFun L)
                          (Abelianizeπ₁→π₁ᵃᵇ))) (η (inv a)))
                ∙ cong (decodeCofibαinr ∘ η) (GroupTheory.invInv (freeGroupGroup (Fin k)) a)))
                ∙ sym (-πᵃᵇinvDistr (decodeCofibαinr (pickGens' .fst (η g))) (decodeCofibαinr (η (inv a))))
                ∙ cong -πᵃᵇ (p (inv a))
                ∙ sym (IsGroupHom.presinv (snd (compGroupHom (AbelianizationFun L)
                          (Abelianizeπ₁→π₁ᵃᵇ))) (η (inv a)))
                ∙ cong (decodeCofibαinr ∘ η) (GroupTheory.invInv (freeGroupGroup (Fin k)) a))

  h : (x : Abelianization (freeGroupGroup (Fin m))) (a b : FreeGroup (Fin k))
      (q : ·πᵃᵇ (decodeCofibαinr (pickGens' .fst x)) (decodeCofibαinr (η b)) ≡ decodeCofibαinr (η a))
     → Path (∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr base) ∥₂)
             (decodeCofibαinr (η a)) (decodeCofibαinr (η b))
  h x a b q = sym q ∙ decodeCofibαinr≡ x b


  decodeCofibαinl : Abelianization (freeGroupGroup (Fin k)) → ∥ (inr base) ≡ᵃᵇ inl tt ∥₂
  decodeCofibαinl = Abi.rec _ squash₂ decodeCofibαinlFun
   λ a b c → cong₂ ·πᵃᵇ (cong ∣_∣₂ (lem a b c)
                    ∙ cong (·πᵃᵇ (∣ paths (t a) ∣₂))
                           (·πᵃᵇcomm ∣ paths (t b) ∣₂ ∣ paths (t c) ∣₂)
                    ∙ sym (cong ∣_∣₂ (lem a c b)))
                        (λ _ → ∣ paths (sym (push base)) ∣₂)
    where
    t : (x : _) → Path (cofib (fst α)) _ _
    t x i = inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup x i)

    lem : (x y z : _)
      → Path (Pathᵃᵇ (cofib (fst α)) _ _)
          (paths (t (x ·f (y ·f z))))
          (paths (t x ∙ t y ∙ t z))

    lem x y z =
      cong paths (((λ j i → inr (InvIso-ΩS¹Bouquet-FreeGroupPresStr x (y ·f z) j i))
         ∙ cong-∙ inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup x)
                      (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (y ·f z)))
        ∙ cong₂ _∙_ refl ((λ j i → inr (InvIso-ΩS¹Bouquet-FreeGroupPresStr y z j i))
                        ∙ cong-∙ inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup y)
                                     (Iso.inv Iso-ΩS¹Bouquet-FreeGroup z)))


  InrHom : GroupHom Free/Imα' (AbGroup→Group (π₁ᵃᵇAbGroup (cofib (fst α) , inr base)))
  fst InrHom = SQ.rec squash₂ decodeCofibαinr main
    where
    main : (a b : _) (q : _) → _
    main = Abi.elimProp2 _ (λ _ _ → isPropΠ (λ _ → squash₂ _ _))
      λ a b → PT.elim (λ _ → squash₂ _ _)
        λ {(x , q)
          → h x a b (cong (λ s → ·πᵃᵇ s (decodeCofibαinr (η b)) )
                (cong decodeCofibαinr q ∙ IsGroupHom.pres· (snd decodeCofibαinrHom) (η a) (η (inv b)))
                ∙ (sym (·πᵃᵇassoc (decodeCofibαinr (η a)) (decodeCofibαinr (η (inv b))) (decodeCofibαinr (η b))))
                ∙ cong (·πᵃᵇ (decodeCofibαinr (η a)))
                   (cong₂ ·πᵃᵇ (IsGroupHom.presinv (snd decodeCofibαinrHom) (η b)) refl
                   ∙ ·πᵃᵇlCancel ((decodeCofibαinr (η b))))
                ∙ ·πᵃᵇrUnit (decodeCofibαinr (η a)))}
  snd InrHom =
    makeIsGroupHom (SQ.elimProp2
      (λ _ _ → squash₂ _ _)
      (IsGroupHom.pres· (snd decodeCofibαinrHom)))

  decodeCofibαInrFull : (x : _) → CodeCofibα (inr x) → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr x) ∥₂
  decodeCofibαInrFull base = fst InrHom
  decodeCofibαInrFull (loop x i) = help i
    where
    lem : (p : _)
     → transport (λ i₁ → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr (loop x i₁)) ∥₂)
                  (·πᵃᵇ p (-πᵃᵇ (decodeCofibαinr (η (η x))))) ≡ p
    lem = ST.elim (λ _ → isSetPathImplicit)
      (elimProp≡ᵃᵇ (λ _ → squash₂ _ _) λ p
        → (λ j → transp (λ i₁ → ∥ Pathᵃᵇ (cofib (fst α))
                                    (inr base) (inr (loop x (i₁ ∨ j))) ∥₂) j
                        ∣ paths (p ∙ (λ i₁ → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup (η x) (~ i₁ ∨ j)))) ∣₂)
       ∙ cong ∣_∣₂ (cong paths (sym (rUnit p))))

    help : PathP (λ i → ua (isoToEquiv (·GroupAutomorphismR Free/Imα' [ η (η x) ])) i
                      →  ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr (loop x i)) ∥₂)
                (fst InrHom) (fst InrHom)
    help = toPathP (funExt (SQ.elimProp (λ _ → squash₂ _ _)
      λ s → cong (transport (λ i → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (inr (loop x i)) ∥₂))
                  ((cong (fst InrHom)
                    (cong (Iso.inv (·GroupAutomorphismR Free/Imα' [ η (η x) ]))
                      (transportRefl [ s ]))
                   ∙ IsGroupHom.pres· (snd InrHom) [ s ] [ η (inv (η x)) ]
                   ∙ cong (·πᵃᵇ (decodeCofibαinr s)) (IsGroupHom.presinv (snd InrHom) [ η (η x) ])))
                ∙ lem (decodeCofibαinr s)))


  decodeCofibα : (x : _) → CodeCofibα x → ∥ (inr base) ≡ᵃᵇ x ∥₂
  decodeCofibα (inl x) p = ·πᵃᵇ (decodeCofibαInrFull base p) ∣ paths (sym (push base)) ∣₂
  decodeCofibα (inr x) = decodeCofibαInrFull x
  decodeCofibα (push a i) = help a i
    where
    help : (a : Bouquet (Fin m))
      → PathP (λ i → CodeCofibα (push a i) → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) (push a i) ∥₂)
               (λ p → ·πᵃᵇ (decodeCofibαInrFull base p) ∣ paths (sym (push base)) ∣₂)
               (decodeCofibαInrFull (Iso.inv CharacBouquet→∙Bouquet α' .fst a))
    help =
      elimPropBouquet (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → squash₂)) _ _)
        (funExt (SQ.elimProp (λ _ → isOfHLevelPathP' 1 squash₂ _ _)
          (Abi.elimProp _ (λ _ → isOfHLevelPathP' 1 squash₂ _ _)
            λ g → λ i → ∣ paths (compPath-filler
              (λ i₂ → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g i₂))
              (sym (push base)) (~ i)) ∣₂)))

  CodeCofibα+Inr : (x : _) → (CodeCofibα (inr base)) → CodeCofibα (inr x) → CodeCofibα (inr x)
  CodeCofibα+Inr base p q = GroupStr._·_ (snd Free/Imα') p q
  CodeCofibα+Inr (loop x i) p = help i
    where
    typecheck : ∀ {ℓ} (A B : Type ℓ) (p : A ≡ B)
      (f : A → A) (g : B → B) → ((x : _) → transport p (f (transport (sym p) x)) ≡ g x)
      → PathP (λ i → p i → p i) f g
    typecheck = λ A → J> λ f g p → funExt λ x → sym (transportRefl _ ∙ cong f (transportRefl x)) ∙ p x

    typecheck' : ∀ {ℓ} {A B : Type ℓ} (p : A ≃ B)
      {f : A → A} {g : B → B} → ((x : _) → fst p (f (invEq p x)) ≡ g x)
        → PathP (λ i → ua p i → ua p i) f g
    typecheck' p {f = f} {g} h =
      typecheck _ _ (ua p) f g λ b
        → transportRefl _ ∙ cong (fst p) (cong f (cong (invEq p) (transportRefl b))) ∙ h b

    help : PathP (λ i → ua (isoToEquiv (·GroupAutomorphismR Free/Imα' [ η (η x) ]))  i
           → ua (isoToEquiv (·GroupAutomorphismR Free/Imα' [ η (η x) ])) i)
           (GroupStr._·_ (snd Free/Imα') p)
           (GroupStr._·_ (snd Free/Imα') p)
    help = typecheck' (isoToEquiv (·GroupAutomorphismR Free/Imα' [ η (η x) ]))
      (SQ.elimProp (λ _ → squash/ _ _)
        (Abi.elimProp _ (λ _ → squash/ _ _)
          λ g → sym (GroupStr.·Assoc (snd Free/Imα') p
                  ((invEq (isoToEquiv (·GroupAutomorphismR Free/Imα' [ η (η x) ])) [ η g ]))
                  [ η (η x) ])
              ∙ cong (snd Free/Imα' GroupStr.· p)
                 (sym (GroupStr.·Assoc (snd Free/Imα')
                      [ η g ] [ η (inv (η x)) ]  [ η (η x) ])
                ∙ cong (snd Free/Imα' GroupStr.· [ η g ])
                  (GroupStr.·InvL (snd Free/Imα') [ η (η x) ])
                ∙ GroupStr.·IdR (snd Free/Imα') [ η g ])))


  CodeCofibα+ : (x : _) → (CodeCofibα (inr base)) → CodeCofibα x → CodeCofibα x
  CodeCofibα+ (inl x) p q = GroupStr._·_ (snd Free/Imα') p q
  CodeCofibα+ (inr x) = CodeCofibα+Inr x
  CodeCofibα+ (push x i) p = help x i
    where
    help : (x : Bouquet (Fin m))
      → PathP (λ i → CodeCofibα (push x i) → CodeCofibα (push x i))
              ((snd Free/Imα' GroupStr.· p))
              (CodeCofibα+Inr (α .fst x) p)
    help = elimPropBouquet
      (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → isSetCodeCofibα _)) _ _)
      refl

  preEncodeHom : (x : cofib (fst α)) (p : inr base ≡ x) (s t : Free/Imα' .fst)
    → subst CodeCofibα p (GroupStr._·_ (snd Free/Imα') s t)
    ≡ CodeCofibα+ x s (subst CodeCofibα p t )
  preEncodeHom = J> λ s t → transportRefl _
    ∙ cong (GroupStr._·_ (snd Free/Imα') s) (sym (transportRefl t))

  cono'Inr : (x : _) (p : Path (cofib (fst α)) (inr base) (inr x)) → hProp ℓ-zero
  cono'Inr base p = (∃[ r ∈ Path (Bouquet (Fin k)) base base ] p ≡ λ i → inr (r i)) , squash₁
  fst (cono'Inr (loop x i) p) =
    ∃[ r ∈ Path (Bouquet (Fin k)) base (loop x i) ] p ≡ λ i → inr (r i)
  snd (cono'Inr (loop x i) p) = squash₁

  cono : (x : cofib (fst α)) (p : inr base ≡ x) → Type
  cono (inl x) p = ∃[ r ∈ Path (Bouquet (Fin k)) base base ] p ≡ (λ i → inr (r i)) ∙ sym (push base)
  cono (inr x) p = fst (cono'Inr x p)
  cono (push a i) p = help a i p .fst
    where
    help : (a : Bouquet (Fin m))
      → PathP (λ i → Path (cofib (fst α))  (inr base) (push a i) → hProp ℓ-zero)
               (λ a → (∃[ r ∈ Path (Bouquet (Fin k)) base base ]
                 a ≡ (λ i → inr (r i)) ∙ sym (push base)) , squash₁)
               (cono'Inr (fst α a))
    help =
      elimPropBouquet (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → isSetHProp)) _ _)
        λ i p → (∃[ r ∈ Path (Bouquet (Fin k)) base base ]
              p ≡ compPath-filler (λ i → inr (r i)) (sym (push base)) (~ i))
              , squash₁

  toCono : (x : cofib (fst α)) (p : inr base ≡ x)  → cono x p
  toCono = J> ∣ refl , refl ∣₁


  encodeCofibαPre : (x : _) → Pathᵃᵇ (cofib (fst α)) (inr base) x → CodeCofibα x
  encodeCofibαPre x (paths q) = subst CodeCofibα q [ η ε ]
  encodeCofibαPre x (com p q r i) = ha _ q p r i
    where

    ha : (x : _) (q p r : inr base ≡ x)
      → subst CodeCofibα (p ∙ sym q ∙ r) [ η ε ]
       ≡ subst CodeCofibα (r ∙ sym q ∙ p) [ η ε ]
    ha = J> λ p q
      → cong (λ p → subst CodeCofibα p [ η ε ]) (cong (p ∙_) (sym (lUnit q)))
      ∙ substComposite CodeCofibα p q [ η ε ]
      ∙ PT.rec2 (squash/ _ _)
          (λ {(x' , xe) (y' , ye)
            → lem (Iso.fun Iso-ΩS¹Bouquet-FreeGroup x') (Iso.fun Iso-ΩS¹Bouquet-FreeGroup y')
                  p
                  (cong (cong inr') (Iso.leftInv Iso-ΩS¹Bouquet-FreeGroup x') ∙ sym xe)
                  q
                  (cong (cong inr') (Iso.leftInv Iso-ΩS¹Bouquet-FreeGroup y') ∙ sym ye)})
          (toCono _ p)
          (toCono _ q)
      ∙ sym (substComposite CodeCofibα q p [ η ε ])
      ∙ cong (λ p → subst CodeCofibα p [ η ε ]) (cong (q ∙_) (lUnit p))
      where
      lem : (x y : FreeGroup (Fin k)) (p : Path (cofib (fst α)) (inr base) (inr base))
            (s : (λ i → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup x i)) ≡ p)
            (q : Path (cofib (fst α)) (inr base) (inr base))
            (s' : (λ i → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup y i)) ≡ q)
         → subst CodeCofibα q (subst CodeCofibα p [ η ε ])
         ≡ subst CodeCofibα p (subst CodeCofibα q [ η ε ])
      lem x y =
        J> (J> cong (subst CodeCofibα y')
             (substCodePre x ε ∙ GroupStr.·IdL (snd Free/Imα') [ η x ])
         ∙ substCodePre y x
         ∙ cong [_] (AbelianizationGroupStructure.commAb
                     (freeGroupGroup (Fin k)) (η x) (η y))
         ∙ sym (substCodePre x y)
         ∙ cong (subst CodeCofibα x')
             (sym (substCodePre y ε ∙ GroupStr.·IdL (snd Free/Imα') [ η y ])) )
        where
        x' y' : Path (cofib (fst α)) (inr base) (inr base)
        x' =  (λ i₁ → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup x i₁))
        y' =  (λ i₁ → inr (Iso.inv Iso-ΩS¹Bouquet-FreeGroup y i₁))

  encodeCofibα : (x : _) → ∥ Pathᵃᵇ (cofib (fst α)) (inr base) x ∥₂ → CodeCofibα x
  encodeCofibα x = ST.rec (isSetCodeCofibα _) (encodeCofibαPre x)

  decodeEncodeCofibα : (x : _) (p : ∥ Pathᵃᵇ (cofib (fst α)) (inr base) x ∥₂)
    → decodeCofibα x (encodeCofibα x p) ≡ p
  decodeEncodeCofibα x = ST.elim (λ _ → isSetPathImplicit) (elimProp≡ᵃᵇ (λ _ → squash₂ _ _)
    (J (λ x p → decodeCofibα x (encodeCofibα x ∣ paths p ∣₂) ≡ ∣ paths p ∣₂)
      refl))

  encodeDecodeCofibα : (p : _) → encodeCofibα (inr base) (decodeCofibα (inr base) p) ≡ p
  encodeDecodeCofibα = SQ.elimProp (λ _ → squash/ _ _)
    (Abi.elimProp _ (λ _ → squash/ _ _)
      λ w → substCodePre w ε ∙ λ i → [ η (FG.idl w (~ i)) ])

  Free/≅π₁ᵃᵇCofibBouquetMap : GroupIso Free/Imα' (AbGroup→Group (π₁ᵃᵇAbGroup (cofib (fst α) , inr base)))
  Iso.fun (fst Free/≅π₁ᵃᵇCofibBouquetMap) = InrHom .fst
  Iso.inv (fst Free/≅π₁ᵃᵇCofibBouquetMap) = encodeCofibα (inr base)
  Iso.rightInv (fst Free/≅π₁ᵃᵇCofibBouquetMap) = decodeEncodeCofibα (inr base)
  Iso.leftInv (fst Free/≅π₁ᵃᵇCofibBouquetMap) = encodeDecodeCofibα
  snd Free/≅π₁ᵃᵇCofibBouquetMap = InrHom .snd

  Free/≅π₁ᵃᵇCofibBouquetMap' :
    GroupIso Free/Imα'
             (AbGroup→Group
               (AbelianizationAbGroup (πGr 0 (cofib (fst α) , inr base))))
  Free/≅π₁ᵃᵇCofibBouquetMap' =
    compGroupIso Free/≅π₁ᵃᵇCofibBouquetMap
      (invGroupIso (Abelianizeπ₁≅π₁ᵃᵇ (_ , inr base)))

  cofibIso' : Iso (cofib (fst α)) (cofib (fst αSphereBouquet))
  cofibIso' = pushoutIso _ _ _ _
    (invEquiv (Bouquet≃∙SphereBouquet .fst)) (idEquiv _)
    (invEquiv (Bouquet≃∙SphereBouquet .fst))
    (λ i x → tt)
    (funExt λ x → cong (invEq (isoToEquiv Iso-SphereBouquet-Bouquet))
      (cong (fst α) (sym (Iso.rightInv Iso-SphereBouquet-Bouquet x))))

  helpIso : GroupIso Free/Imα'
             (AbGroup→Group
               (AbelianizationAbGroup (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt))))
  helpIso =
    compGroupIso Free/≅π₁ᵃᵇCofibBouquetMap'
      (GroupEquiv→GroupIso (AbelianizationEquiv
        (compGroupEquiv (GroupIso→GroupEquiv (invGroupIso (π'Gr≅πGr 0 (cofib (fst α) , inr base))))
          (GroupIso→GroupEquiv (π'GrIso 0 (isoToEquiv (cofibIso') , sym (push (inl tt))))))))

  Free/Imα≅ℤ[]/ImBouquetDegree : GroupIso Free/Imα'
    (AbGroup→Group ℤ[Fin k ] / (imSubgroup (bouquetDegree (fst αSphereBouquet))
                               , isNormalIm _ λ f g i x → +Comm (f x) (g x) i))
  Free/Imα≅ℤ[]/ImBouquetDegree = Hom/ImIso _ _ (Is m) (Is k)
    (Abi.elimProp _ (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
      λ g i → help main i .fst g)
     where
     Is : (m : _) → _
     Is m = compGroupIso GroupIso-AbelienizeFreeGroup→FreeAbGroup
                            (invGroupIso (ℤFin≅FreeAbGroup m))
     H : (m : _) → _ 
     H m = GroupIso→GroupHom (Is m)

     help = freeGroupHom≡
       {f = compGroupHom (compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _) (H m))
             (bouquetDegree (fst αSphereBouquet))}
       {g = compGroupHom (compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _) pickGens') (H k)}

     main : (a : _) → _
     main a = funExt λ s
       → sumFin-choose _ _ (λ _ → refl) +Comm _ _ a
           (characdiag s)
            λ x p → cong₂ _·ℤ_ (charac¬  x p) refl
       where
       charac¬ : (x' : Fin m) → ¬ x' ≡ a
         → fst (H m) (η (η a)) x' ≡ pos 0
       charac¬ x' p with (fst a ≟ᵗ fst x')
       ... | lt x = refl
       ... | eq x = ⊥.rec (p (Σ≡Prop (λ _ → isProp<ᵗ) (sym x)))
       ... | gt x = refl

       lem : ℤFinGenerator a a ≡ 1
       lem with (fst a ≟ᵗ fst a)
       ... | lt x = ⊥.rec (¬m<ᵗm x)
       ... | eq x = refl
       ... | gt x = ⊥.rec (¬m<ᵗm x)

       l2 : (x : FreeGroup (Fin k)) (y : S¹)
         → fst (SphereBouquet∙ 1 (Fin k))
       l2 b base = inl tt
       l2 b (loop i) = Bouquet→SphereBouquet (Iso.inv Iso-ΩS¹Bouquet-FreeGroup b i)

       lema : (x : _) → fst αSphereBouquet (inr (a , x))
                       ≡ l2 (α' a) x
       lema base = refl
       lema (loop i) = refl

       characdiagMain : (w : _) 
         → (λ s → degree (suc zero) (λ x → pickPetal s (l2 w x))) ≡ fst (H k) (η w)
       characdiagMain =
         funExt⁻ (cong fst (freeGroupHom≡ {Group = AbGroup→Group ℤ[Fin k ]}
           {f = _ , makeIsGroupHom λ f g
             → funExt λ t → cong (degree 1)
               (funExt (λ { base → refl
                          ; (loop i) j → K t f g j i}))
               ∙ (degreeHom {n = 0}
                 ((λ x → pickPetal t (l2 f x)) , refl)
                 ((λ x → pickPetal t (l2 g x)) , refl))}
           {g = _ , compGroupHom (AbelianizationGroupStructure.ηAsGroupHom _) (H k) .snd}
           λ s → funExt λ w → final s w ∙ ℤFinGeneratorComm w s))
         where
         final : (s w : Fin k) → degree 1 (λ x → pickPetal w (l2 (η s) x))
                            ≡ ℤFinGenerator w s
         final s w with (fst w ≟ᵗ fst s)
         ... | lt x = refl
         ... | eq x = refl
         ... | gt x = refl

         K : (t : _) (f g : FreeGroup (Fin k))
           → cong (pickPetal t ∘ l2 (f FG.· g)) loop
           ≡ (cong (pickPetal t ∘ l2 f) loop ∙ refl)
            ∙ cong (pickPetal t ∘ l2 g) loop ∙ refl
         K t f g =
            cong (cong (pickPetal t ∘ Bouquet→SphereBouquet))
               (InvIso-ΩS¹Bouquet-FreeGroupPresStr f g)
           ∙ cong-∙ (pickPetal t ∘ Bouquet→SphereBouquet)
               (Iso.inv Iso-ΩS¹Bouquet-FreeGroup f)
               (Iso.inv Iso-ΩS¹Bouquet-FreeGroup g)
           ∙ cong₂ _∙_ (rUnit _) (rUnit _)

       characdiag : (s : _) →
            ℤFinGenerator a a 
         ·ℤ degree 1 (λ x → pickPetal s (fst αSphereBouquet (inr (a , x))))
         ≡ fst (H k) (fst pickGens' (η (η a))) s
       characdiag s = cong₂ _·ℤ_ lem refl
                    ∙ cong (degree (suc zero)) (funExt λ x → cong (pickPetal s) (lema x))
                    ∙ funExt⁻ (characdiagMain (α' a))  s

  π'BoquetFunCofib≅Free/Imα>1 :
    GroupIso (AbGroup→Group (AbelianizationAbGroup (π'Gr 0 (cofib (fst αSphereBouquet) , inl tt))))
             (AbGroup→Group ℤ[Fin k ] / (imSubgroup (bouquetDegree (fst αSphereBouquet))
                               , isNormalIm _ λ f g i x → +Comm (f x) (g x) i))
  π'BoquetFunCofib≅Free/Imα>1 = compGroupIso (invGroupIso helpIso) Free/Imα≅ℤ[]/ImBouquetDegree
