{-# OPTIONS --cubical --allow-unsolved-metas --lossy-unification #-}
{-
Contains facts about the degree map Sⁿ → Sⁿ
-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)

open import Cubical.HITs.Sn
open import Cubical.HITs.S1 renaming (_·_ to _*_)
open import Cubical.HITs.Susp
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.ZAction
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Properties

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.PinSn
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Sn


open import prelude
open import freeabgroup


module degree where

--- preliminaries: to be moved to main lib in relevant folders
ℤ·-negsuc : ∀ {ℓ} (G : Group ℓ) (a : ℕ) (g : fst G)
  → (negsuc a ℤ[ G ]· g) ≡ GroupStr.inv (snd G) ((pos (suc a)) ℤ[ G ]· g)
ℤ·-negsuc G zero g = sym (cong (GroupStr.inv (snd G)) (GroupStr.·IdR (snd G) _))
ℤ·-negsuc G (suc a) g =
    (distrℤ· G g (negsuc a) (negsuc zero))
  ∙ cong₂ (GroupStr._·_ (snd G)) (ℤ·-negsuc G a g) refl
  ∙ sym (GroupTheory.invDistr G g ((pos (suc a)) ℤ[ G ]· g))

gen∈Im→isEquiv : ∀ (G : Group₀) (e : GroupEquiv ℤGroup G)
          (H : Group₀) (e' : GroupEquiv ℤGroup H)
       → (h₀ : fst H)
       → 1 ≡ invEq (fst e') h₀
       → (h : GroupHom G H)
       → isInIm (_ , snd h) h₀
       → isEquiv (fst h)
gen∈Im→isEquiv G e H =
  GroupEquivJ (λ H e'
    → (h₀ : fst H)
       → 1 ≡ invEq (fst e') h₀
       → (h : GroupHom G H)
       → isInIm (_ , snd h) h₀
       → isEquiv (fst h))
     (J> 1∈Im→isEquiv G e)


----------- main part ------------
degree : (n : ℕ) → (S₊ n → S₊ n) → ℤ
degree zero f = 0
degree (suc n) f = Iso.fun ((Hⁿ-Sⁿ≅ℤ n) .fst) ∣ (λ x → ∣ f x ∣) ∣₂

degree∙ : (n : ℕ) → (S₊∙ n →∙ S₊∙ n) → ℤ
degree∙ zero f = 0
degree∙ (suc n) f = Iso.fun ((Hⁿ-Sⁿ≅ℤ n) .fst) ∣ (λ x → ∣ fst f x ∣) ∣₂

degree-const : (n : ℕ) → degree n (λ _ → ptSn n) ≡ 0
degree-const zero = refl
degree-const (suc n) = IsGroupHom.pres1 (Hⁿ-Sⁿ≅ℤ n .snd) 

-- Generator of HⁿSⁿ
HⁿSⁿ-gen : (n : ℕ) → Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n)) ∣ ∣_∣ₕ ∣₂ ≡ 1
HⁿSⁿ-gen zero = refl
HⁿSⁿ-gen (suc n) = cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n))) main ∙ HⁿSⁿ-gen n
  where
  lem : Iso.inv (fst (suspensionAx-Sn n n)) ∣ ∣_∣ₕ ∣₂ ≡ ∣ ∣_∣ₕ ∣₂
  lem = cong ∣_∣₂
    (funExt λ { north → refl
              ; south i → ∣ merid (ptSn (suc n)) i ∣ₕ
              ; (merid a i) j → ∣ compPath-filler (merid a) (sym (merid (ptSn (suc n)))) (~ j) i ∣ₕ})

  main : Iso.fun (fst (suspensionAx-Sn n n)) ∣ ∣_∣ₕ ∣₂ ≡ ∣ ∣_∣ₕ ∣₂
  main = (sym (cong (Iso.fun (fst (suspensionAx-Sn n n))) lem)
     ∙ Iso.rightInv (fst (suspensionAx-Sn n n)) ∣ ∣_∣ₕ ∣₂)

private
  makePted : (n : ℕ) (fn : S₊ (2 +ℕ n)) → ∥ fn ≡ north ∥₂
  makePted n fn =
    TR.rec (isOfHLevelPlus' 2 squash₂) ∣_∣₂
        (isConnectedPathSⁿ (suc n) fn north .fst)
  makePted-eq : (n : ℕ) (fn : S₊ (2 +ℕ n)) (p : fn ≡ north) → makePted n fn ≡ ∣ p ∣₂
  makePted-eq n fn p j =
    TR.rec (isOfHLevelPlus' 2 squash₂) ∣_∣₂ (isConnectedPathSⁿ (suc n) fn north .snd ∣ p ∣ j)

-- Forgetting pointedness gives iso
πₙSⁿ-unpoint : (n : ℕ) → (π'Gr n (S₊∙ (suc n)) .fst) → ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂
πₙSⁿ-unpoint n = ST.map fst

isIso-πₙSⁿ-unpointIso : (n : ℕ) → isIso (πₙSⁿ-unpoint n)
fst (isIso-πₙSⁿ-unpointIso zero) =
  ST.map λ f → (λ x → f x * (invLooper (f base)))
                , sym (rCancelS¹ (f base))
fst (snd (isIso-πₙSⁿ-unpointIso zero)) =
  ST.elim (λ _ → isSetPathImplicit)
      λ f → PT.rec (squash₂ _ _)
      (λ q → cong ∣_∣₂ (funExt λ x → cong (f x *_)
        (cong invLooper (sym q)) ∙ rUnitS¹ (f x)))
      (isConnectedS¹ (f base))
snd (snd (isIso-πₙSⁿ-unpointIso zero)) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → cong ∣_∣₂
      (ΣPathP ((funExt (λ r → cong (fst f r *_) (cong invLooper (snd f))
                                               ∙ rUnitS¹ (fst f r)))
    , help _ (sym (snd f))))
  where
  help : (x : _) (p : base ≡ x)
    → PathP (λ i → ((λ j → x * invLooper (p (~ j))) ∙ rUnitS¹ x) i ≡ base)
             (sym (rCancelS¹ x)) (sym p)
  help = J> λ i j → rCancel (λ _ → base) j i
fst (isIso-πₙSⁿ-unpointIso (suc n)) = ST.rec squash₂ λ f → ST.map (λ p → f , p) (makePted n (f north))
fst (snd (isIso-πₙSⁿ-unpointIso (suc n))) =
  ST.elim (λ _ → isSetPathImplicit)
    λ f → ST.rec isSetPathImplicit
      (λ p j → πₙSⁿ-unpoint (suc n) (ST.map (λ p₁ → f , p₁) (makePted-eq n (f north) p j)))
           (makePted n (f north))
snd (snd (isIso-πₙSⁿ-unpointIso (suc n))) =
  ST.elim (λ _ → isSetPathImplicit)
      λ f i → ST.map (λ p → fst f , p) (makePted-eq n _ (snd f) i)

πₙSⁿ-unpointIso : (n : ℕ) → Iso ∥ (S₊∙ (suc n) →∙ S₊∙ (suc n)) ∥₂ ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂
Iso.fun (πₙSⁿ-unpointIso n) = πₙSⁿ-unpoint n
Iso.inv (πₙSⁿ-unpointIso n) = isIso-πₙSⁿ-unpointIso n .fst
Iso.rightInv (πₙSⁿ-unpointIso n) = isIso-πₙSⁿ-unpointIso n .snd .fst
Iso.leftInv (πₙSⁿ-unpointIso n) = isIso-πₙSⁿ-unpointIso n .snd .snd

πₙSⁿ→HⁿSⁿ-fun : (n : ℕ) → π'Gr n (S₊∙ (suc n)) .fst → coHom (suc n) (S₊ (suc n))
πₙSⁿ→HⁿSⁿ-fun n = ST.map λ f x → ∣ fst f x ∣

module suspensionLemmas (n : ℕ) where
  makeSn-fun : ((f : S₊ (suc n) → Ω (S₊∙ (suc (suc n))) .fst) → S₊ (suc (suc n)) → S₊ (suc (suc n)))
  makeSn-fun f north = north
  makeSn-fun f south = north
  makeSn-fun f (merid a i) = f a i

  makeSn-fun-σ : (f : S₊∙ (suc n) →∙ Ω (S₊∙ (suc (suc n))))
    → (x : _)
    → cong (makeSn-fun (fst f)) (σ (suc n) x) ≡ fst f x
  makeSn-fun-σ f x =
      cong-∙ (makeSn-fun (fst f)) (merid x) (sym (merid _))
    ∙ cong (λ z → fst f x ∙ sym z) (snd f)
    ∙ sym (rUnit _)

  makeSnEq : (f : _) → ∥ Σ[ g ∈ (S₊∙ (suc n) →∙ Ω (S₊∙ (suc (suc n)))) ] f ≡ makeSn-fun (fst g) ∥₂
  makeSnEq f =
    ST.map
      (λ p → ((λ x → (sym p ∙ cong f (merid x) ∙ (cong f (sym (merid (ptSn _))) ∙ p)))
              , (cong (sym p ∙_) (assoc _ _ _ ∙ cong (_∙ p) (rCancel (cong f (merid (ptSn _))))
                               ∙ sym (lUnit p))
               ∙ lCancel p))
            , funExt (λ { north → p
                        ; south → cong f (sym (merid (ptSn _))) ∙ p
                        ; (merid a i) j → compPath-filler' (sym p)
                                           (compPath-filler (cong f (merid a))
                                             (cong f (sym (merid (ptSn _))) ∙ p) j) j i}))
      (makePted n (f north))

  makeSnEq∙ : (f : (S₊∙ (2 +ℕ n)) →∙ S₊∙ (2 +ℕ n))
    → ∃[ g ∈ _ ] f ≡ (makeSn-fun (fst g) , refl)
  makeSnEq∙ f =
    ST.rec (isProp→isSet squash₁)
      (uncurry (λ g q → TR.rec (isProp→isOfHLevelSuc n squash₁)
        (λ r → ∣ g , ΣPathP (q , (sym r ◁ (λ i j → q (i ∨ j) north))) ∣₁)
        (isConnectedPath _
          (isConnectedPathSⁿ (suc n) (fst f north) north) (funExt⁻ q north) (snd f) .fst )))
      (makeSnEq (fst f))

πₙSⁿ→HⁿSⁿ : (n : ℕ) → GroupHom (π'Gr n (S₊∙ (suc n))) (coHomGr (suc n) (S₊ (suc n)))
fst (πₙSⁿ→HⁿSⁿ n) = πₙSⁿ→HⁿSⁿ-fun n
snd (πₙSⁿ→HⁿSⁿ zero) =
  makeIsGroupHom
    (ST.elim2 (λ _ _ → isSetPathImplicit)
      λ f g → subst2 P (sym (S¹-fun-charac f .snd)) (sym (S¹-fun-charac g .snd))
                (main (S¹-fun-charac f .fst) (S¹-fun-charac g .fst)))
    where
    mkfun : fst (Ω (S₊∙ 1)) → S¹ → S¹
    mkfun p base = base
    mkfun p (loop i) = p i

    main : (a b : Ω (S₊∙ 1) .fst)
      → πₙSⁿ→HⁿSⁿ-fun zero (·π' zero ∣ mkfun a , refl ∣₂ ∣ mkfun b , refl ∣₂)
       ≡ πₙSⁿ→HⁿSⁿ-fun zero ∣ mkfun a , refl ∣₂
       +ₕ πₙSⁿ→HⁿSⁿ-fun zero ∣ mkfun b , refl ∣₂
    main a b = cong ∣_∣₂ (funExt
      λ { base → refl
       ; (loop i) j → ((λ i j → ∣ (rUnit a (~ i) ∙ rUnit b (~ i)) j ∣ₕ)
                    ∙∙ cong-∙ ∣_∣ₕ a b
                    ∙∙ ∙≡+₁ (cong ∣_∣ₕ a) (cong ∣_∣ₕ b)) j i})

    S¹-fun-charac : (f : S₊∙ 1 →∙ S₊∙ 1)
      → Σ[ g ∈ Ω (S₊∙ 1) .fst ] f ≡ (mkfun g , refl)
    S¹-fun-charac (f , p) = (sym p ∙∙ cong f loop ∙∙ p)
      , ΣPathP ((funExt (λ { base → p
                           ; (loop i) j → doubleCompPath-filler (sym p) (cong f loop) p j i}))
      , λ i j → p (i ∨ j))

    P : (f g : _) → Type
    P f g = πₙSⁿ→HⁿSⁿ-fun zero (·π' zero ∣ f ∣₂ ∣ g ∣₂)
          ≡ (πₙSⁿ→HⁿSⁿ-fun zero ∣ f ∣₂) +ₕ (πₙSⁿ→HⁿSⁿ-fun zero ∣ g ∣₂)

snd (πₙSⁿ→HⁿSⁿ (suc n)) = makeIsGroupHom isGrHom
  where
  open suspensionLemmas n
  isGrHom : (f g : _) → πₙSⁿ→HⁿSⁿ-fun (suc n) (·π' _ f g) ≡ πₙSⁿ→HⁿSⁿ-fun (suc n) f +ₕ πₙSⁿ→HⁿSⁿ-fun (suc n) g
  isGrHom = ST.elim2 (λ _ _ → isSetPathImplicit)
              λ f g → PT.rec2 (squash₂ _ _)
                (uncurry (λ g' gp → uncurry λ h hp
                  → (λ i → πₙSⁿ→HⁿSⁿ-fun (suc n) (·π' (suc n) ∣ gp i ∣₂ ∣ hp i ∣₂) )
                  ∙∙ cong ∣_∣₂ (funExt
                    (λ { north → refl
                       ; south → refl
                       ; (merid a i) j
                       → hcomp (λ k → λ {(i = i0) → 0ₖ (2 +ℕ n)
                                        ; (i = i1) → 0ₖ (2 +ℕ n)
                                        ; (j = i0) → ∣ (rUnit (makeSn-fun-σ g' a (~ k)) k ∙ rUnit (makeSn-fun-σ h a (~ k)) k) i ∣ₕ
                                        ; (j = i1) → ∙≡+₂ _ (cong ∣_∣ₕ (g' .fst a)) (cong ∣_∣ₕ (h .fst a)) k i})
                                (cong-∙ ∣_∣ₕ (g' .fst a) (h .fst a) j i)}))
                  ∙∙ λ i → πₙSⁿ→HⁿSⁿ-fun (suc n) ∣ gp (~ i) ∣₂ +ₕ πₙSⁿ→HⁿSⁿ-fun (suc n) ∣ hp (~ i) ∣₂))
                 (makeSnEq∙ f) (makeSnEq∙ g)


πₙSⁿ≅HⁿSⁿ : (n : ℕ) → GroupEquiv (π'Gr n (S₊∙ (suc n))) (coHomGr (suc n) (S₊ (suc n)))
fst (fst (πₙSⁿ≅HⁿSⁿ n)) = fst (πₙSⁿ→HⁿSⁿ n)
snd (fst (πₙSⁿ≅HⁿSⁿ zero)) =
  subst isEquiv (sym funid) (isoToIsEquiv (compIso is1 is2))
  where
  is1 : Iso (π' 1 (S₊∙ 1)) ∥ (S¹ → S¹) ∥₂
  is1 = πₙSⁿ-unpointIso 0

  is2 : Iso ∥ (S¹ → S¹) ∥₂ (coHom 1 S¹)
  is2 = setTruncIso (codomainIso (invIso (truncIdempotentIso 3 isGroupoidS¹)))

  funid : πₙSⁿ→HⁿSⁿ-fun zero ≡ Iso.fun is2 ∘ Iso.fun is1
  funid = funExt (ST.elim (λ _ → isSetPathImplicit) λ _ → refl)

snd (fst (πₙSⁿ≅HⁿSⁿ (suc n))) =
  gen∈Im→isEquiv _ (GroupIso→GroupEquiv (invGroupIso (πₙ'Sⁿ≅ℤ (suc n)))) _
                               (GroupIso→GroupEquiv (invGroupIso (Hⁿ-Sⁿ≅ℤ (suc n))))
                               ∣ ∣_∣ₕ ∣₂
                               (sym (HⁿSⁿ-gen (suc n)))
                               (πₙSⁿ→HⁿSⁿ (suc n))
                               ∣ ∣ idfun∙ _ ∣₂ , refl ∣₁
snd (πₙSⁿ≅HⁿSⁿ n) = snd (πₙSⁿ→HⁿSⁿ n)


-- degree can be stated as an iso
module _ (n : ℕ) where
  degreeIso : Iso ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂ ℤ
  degreeIso = compIso (invIso (πₙSⁿ-unpointIso n))
                (compIso (equivToIso (πₙSⁿ≅HⁿSⁿ n .fst)) (fst (Hⁿ-Sⁿ≅ℤ n)))

  degree∥₂ : ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂ → ℤ
  degree∥₂ = ST.rec isSetℤ (degree (suc n))

  degree∥₂≡ : degree∥₂ ≡ Iso.fun degreeIso
  degree∥₂≡ = funExt (λ f → cong degree∥₂ (sym (Iso.rightInv (πₙSⁿ-unpointIso n) f))
                          ∙∙ help (Iso.inv (πₙSⁿ-unpointIso n) f)
                          ∙∙ cong (Iso.fun degreeIso) (Iso.rightInv (πₙSⁿ-unpointIso n) f))
    where
    help : (g : _) → degree∥₂ (Iso.fun (πₙSⁿ-unpointIso n) g)
                    ≡ Iso.fun degreeIso (Iso.fun (πₙSⁿ-unpointIso n) g)
    help = ST.elim (λ _ → isOfHLevelPath 2 isSetℤ _ _)
           λ g → cong (Iso.fun (compIso (equivToIso (πₙSⁿ≅HⁿSⁿ n .fst)) (fst (Hⁿ-Sⁿ≅ℤ n))))
                   (sym (Iso.leftInv (πₙSⁿ-unpointIso n) ∣ g ∣₂))

  degree∥₂Iso : Iso ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂ ℤ
  Iso.fun degree∥₂Iso = degree∥₂
  Iso.inv degree∥₂Iso = Iso.inv degreeIso
  Iso.rightInv degree∥₂Iso p =
    funExt⁻ degree∥₂≡ (Iso.inv degreeIso p) ∙ Iso.rightInv degreeIso p
  Iso.leftInv degree∥₂Iso p =
    cong (Iso.inv degreeIso) (funExt⁻ degree∥₂≡ p) ∙ Iso.leftInv degreeIso p

πₙSⁿ : (n : ℕ) → Group₀
πₙSⁿ n = π'Gr n (S₊∙ (suc n))

-- the multiplications
module _ (n : ℕ) where
  multSⁿ↬ : (f g : ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂)
   → ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂
  multSⁿ↬ = ST.rec2 squash₂ λ f g → ∣ f ∘ g ∣₂

  multπₙ : (f g : πₙSⁿ n .fst) → πₙSⁿ n .fst
  multπₙ = ST.rec2 squash₂ λ f g → ∣ f ∘∙ g ∣₂

  premultHⁿSⁿ : (f g : S₊ (suc n) → coHomK (suc n)) → (S₊ (suc n) → coHomK (suc n))
  premultHⁿSⁿ f g x = TR.rec (isOfHLevelTrunc (3 +ℕ n)) f (g x)

  multHⁿSⁿ : (f g : coHom (suc n) (S₊ (suc n))) → coHom (suc n) (S₊ (suc n))
  multHⁿSⁿ = ST.rec2 squash₂ (λ f g → ∣ premultHⁿSⁿ f g ∣₂)

-- preservation of multiplication under relevant isos
multπₙ-pres : (n : ℕ) (f g : πₙSⁿ n .fst)
  → Iso.fun (πₙSⁿ-unpointIso n) (multπₙ n f g)
   ≡ multSⁿ↬ n (Iso.fun (πₙSⁿ-unpointIso n) f) (Iso.fun (πₙSⁿ-unpointIso n) g)
multπₙ-pres n = ST.elim2 (λ _ _ → isSetPathImplicit) λ f g → refl

multπₙ-pres' : (n : ℕ) (f g : ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂)
  → Iso.inv (πₙSⁿ-unpointIso n) (multSⁿ↬ n f g)
   ≡ multπₙ n (Iso.inv (πₙSⁿ-unpointIso n) f) (Iso.inv (πₙSⁿ-unpointIso n) g)
multπₙ-pres' n f g =
    (λ i → isIso-πₙSⁿ-unpointIso n .fst
             (multSⁿ↬ n (Iso.rightInv (πₙSⁿ-unpointIso n) f (~ i))
                         (Iso.rightInv (πₙSⁿ-unpointIso n) g (~ i))))
  ∙∙ sym (cong (Iso.inv (πₙSⁿ-unpointIso n))
       (multπₙ-pres n (Iso.inv (πₙSⁿ-unpointIso n) f) (Iso.inv (πₙSⁿ-unpointIso n) g)))
  ∙∙ Iso.leftInv (πₙSⁿ-unpointIso n) _

multHⁿSⁿ-pres : (n : ℕ) (f g : πₙSⁿ n .fst)
  → πₙSⁿ→HⁿSⁿ-fun n (multπₙ n f g)
   ≡ multHⁿSⁿ n (πₙSⁿ→HⁿSⁿ-fun n f) (πₙSⁿ→HⁿSⁿ-fun n g)
multHⁿSⁿ-pres n = ST.elim2 (λ _ _ → isSetPathImplicit) λ f g → refl

-- properties of multiplication on Hⁿ(Sⁿ)
module mult-props (m : ℕ) where
  private
    hlev-imp : ∀ {x y : coHomK (suc m)} → isOfHLevel (3 +ℕ m) (x ≡ y)
    hlev-imp = isOfHLevelPath (3 +ℕ m) (isOfHLevelTrunc (3 +ℕ m)) _ _

    cohom-im-elim : ∀ {ℓ} (n : ℕ)
         (P : coHomK (suc n) → Type ℓ)
      → ((x : _) → isOfHLevel (3 +ℕ n) (P x))
      → (f : S₊ (suc n) → coHomK (suc n))
      → (t : S₊ (suc n))
      → ((r : S₊ (suc n)) → f t ≡ ∣ r ∣ → P ∣ r ∣)
      → P (f t)
    cohom-im-elim n P hlev f t ind = l (f t) refl
      where
      l : (x : _) → f t ≡ x → P x
      l = TR.elim (λ x → isOfHLevelΠ (3 +ℕ n) λ _ → hlev _) ind


  multHⁿSⁿ-0ₗ : (f : _) → multHⁿSⁿ m (0ₕ (suc m)) f ≡ 0ₕ (suc m)
  multHⁿSⁿ-0ₗ =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → cong ∣_∣₂
        (funExt λ x → cohom-im-elim m (λ s → rec₊ (isOfHLevelTrunc (3 +ℕ m)) (λ _ → 0ₖ (suc m)) s ≡ 0ₖ (suc m))
        (λ _ → hlev-imp)
        f
        x
        λ _ _ → refl)

  multHⁿSⁿ-1ₗ : (f : _) → multHⁿSⁿ m (∣ ∣_∣ₕ ∣₂) f ≡ f
  multHⁿSⁿ-1ₗ =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → cong ∣_∣₂
        (funExt λ x → cohom-im-elim m (λ s → rec₊ (isOfHLevelTrunc (3 +ℕ m)) ∣_∣ₕ s ≡ s)
        (λ _ → hlev-imp)
        f
        x
        λ _ _ → refl)

  multHⁿSⁿ-invₗ : (f g : _) → multHⁿSⁿ m (-ₕ f) g ≡ -ₕ (multHⁿSⁿ m f g)
  multHⁿSⁿ-invₗ = ST.elim2 (λ _ _ → isSetPathImplicit)
    λ f g → cong ∣_∣₂
      (funExt λ x → cohom-im-elim m
        (λ gt → rec₊ (isOfHLevelTrunc (3 +ℕ m)) (λ x₁ → -ₖ-syntax (suc m) (f x₁)) gt
               ≡ -ₖ (rec₊ (isOfHLevelTrunc (3 +ℕ m)) f gt))
        (λ _ → hlev-imp)
        g x
        λ r s → refl)

  multHⁿSⁿ-distrₗ : (f g h : _) → multHⁿSⁿ m (f +ₕ g) h ≡ (multHⁿSⁿ m f h) +ₕ (multHⁿSⁿ m g h)
  multHⁿSⁿ-distrₗ = ST.elim3 (λ _ _ _ → isSetPathImplicit)
    λ f g h → cong ∣_∣₂ (funExt λ x → cohom-im-elim m
      (λ ht → rec₊ (isOfHLevelTrunc (3 +ℕ m)) (λ x → f x +ₖ g x) ht
            ≡ rec₊ (isOfHLevelTrunc (3 +ℕ m)) f ht +ₖ rec₊ (isOfHLevelTrunc (3 +ℕ m)) g ht)
      (λ _ → hlev-imp) h x λ _ _ → refl)

open mult-props
grr'-nice-pos : (m : ℕ) (a : ℕ) (f g : _)
  → multHⁿSⁿ m ((pos a) ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· f) g
  ≡ (pos a) ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· (multHⁿSⁿ m f g)
grr'-nice-pos m zero f g = multHⁿSⁿ-0ₗ m g
grr'-nice-pos m (suc a) f g =
    multHⁿSⁿ-distrₗ _ f (((pos a) ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· f)) g
  ∙ cong (multHⁿSⁿ m f g +ₕ_) (grr'-nice-pos m a f g)


distrleft : (m : ℕ) (a : ℤ) (f g : _)
  → multHⁿSⁿ m (a ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· f) g
  ≡ a ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· (multHⁿSⁿ m f g)
distrleft m (pos a) = grr'-nice-pos m a
distrleft m (negsuc nn) f g =
     (λ i → multHⁿSⁿ m (ℤ·-negsuc (coHomGr (suc m) (S₊ (suc m))) nn f i) g)
  ∙∙ multHⁿSⁿ-invₗ m (pos (suc nn) ℤ[ coHomGr (suc m) (S₊ (suc m)) ]· f) g
  ∙ cong -ₕ_ (grr'-nice-pos m (suc nn) f g)
  ∙∙ sym (ℤ·-negsuc (coHomGr (suc m) (S₊ (suc m)) ) nn (multHⁿSⁿ m f g))

Hⁿ-Sⁿ≅ℤ-pres-mult : (n : ℕ) (f g : _)
  → Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n)) (multHⁿSⁿ n f g)
   ≡ Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n)) f ·ℤ Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n)) g
Hⁿ-Sⁿ≅ℤ-pres-mult n f g =
    cong ϕ
      (cong₂ (multHⁿSⁿ n) (sym (repl f)) (sym (repl g))
      ∙ distrleft n (ϕ f) (∣ ∣_∣ₕ ∣₂) (ϕ g ℤ[ H ]· ∣ ∣_∣ₕ ∣₂))
    ∙ (homPresℤ· (_ , snd (Hⁿ-Sⁿ≅ℤ n)) (multHⁿSⁿ n ∣ ∣_∣ₕ ∣₂ (ϕ g ℤ[ H ]· ∣ ∣_∣ₕ ∣₂)) (ϕ f)
    ∙ sym (ℤ·≡· (ϕ f) _))
    ∙ cong (ϕ f ·ℤ_)
        (cong ϕ (multHⁿSⁿ-1ₗ n (ϕ g ℤ[ H ]· ∣ ∣_∣ₕ ∣₂))
      ∙ homPresℤ· (_ , snd (Hⁿ-Sⁿ≅ℤ n)) ∣ ∣_∣ₕ ∣₂ (ϕ g)
      ∙ sym (ℤ·≡· (ϕ g) _)
      ∙ cong (ϕ g ·ℤ_) (HⁿSⁿ-gen n)
      ∙ ·Comm (ϕ g) 1)
  where
  ϕ = Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n))
  ϕ⁻ = Iso.inv (fst (Hⁿ-Sⁿ≅ℤ n))

  H = coHomGr (suc n) (S₊ (suc n))

  repl : (f : H .fst) → (ϕ f ℤ[ H ]· ∣ ∣_∣ₕ ∣₂) ≡ f
  repl f = sym (Iso.leftInv (fst (Hⁿ-Sⁿ≅ℤ n)) _)
        ∙∙ cong ϕ⁻ lem
        ∙∙ Iso.leftInv (fst (Hⁿ-Sⁿ≅ℤ n)) f
    where
    lem : ϕ (ϕ f ℤ[ H ]· ∣ ∣_∣ₕ ∣₂) ≡ ϕ f
    lem = homPresℤ· (_ , snd (Hⁿ-Sⁿ≅ℤ n)) ∣ ∣_∣ₕ ∣₂ (ϕ f)
        ∙ sym (ℤ·≡· (ϕ f) (fst (Hⁿ-Sⁿ≅ℤ n) .Iso.fun ∣ (λ a → ∣ a ∣) ∣₂))
        ∙ cong (ϕ f ·ℤ_) (HⁿSⁿ-gen n)
        ∙ ·Comm (ϕ f) 1

-- main result --
degree-comp : (n : ℕ) (f g : (S₊ n → S₊ n))
  → degree n (f ∘ g)
   ≡ degree n f ·ℤ degree n g
degree-comp zero f g = refl
degree-comp (suc n) f g =
     (λ i → degree∥₂≡ n i ∣ f ∘ g ∣₂)
  ∙∙ deg-comp-help n ∣ f ∣₂ ∣ g ∣₂
  ∙∙ cong₂ _·ℤ_ (sym (funExt⁻ (degree∥₂≡ n) ∣ f ∣₂))
                (sym (funExt⁻ (degree∥₂≡ n) ∣ g ∣₂))
  where
  deg-comp-help : (n : ℕ) (f g : ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂)
     → Iso.fun (degreeIso n) (multSⁿ↬ n f g)
     ≡ (Iso.fun (degreeIso n) f) ·ℤ Iso.fun (degreeIso n) g
  deg-comp-help n f g =
    cong (Iso.fun (compIso (equivToIso (πₙSⁿ≅HⁿSⁿ n .fst)) (fst (Hⁿ-Sⁿ≅ℤ n))))
          (multπₙ-pres' n f g)
     ∙ cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n)))
        (multHⁿSⁿ-pres n (isIso-πₙSⁿ-unpointIso n .fst f) (isIso-πₙSⁿ-unpointIso n .fst g))
     ∙ Hⁿ-Sⁿ≅ℤ-pres-mult
          n (πₙSⁿ→HⁿSⁿ-fun n (isIso-πₙSⁿ-unpointIso n .fst f))
            (πₙSⁿ→HⁿSⁿ-fun n (isIso-πₙSⁿ-unpointIso n .fst g))

degree-comp' : (n : ℕ) (f g : (S₊ n → S₊ n))
  → degree n (f ∘ g)
   ≡ degree n g ·ℤ degree n f
degree-comp' n f g = degree-comp n f g ∙ ·Comm _ _

comp-comm : (n : ℕ) (f g : (S₊ (suc n) → S₊ (suc n))) → ∥ f ∘ g ≡ g ∘ f ∥₁
comp-comm n f g = PT.map (idfun _) (Iso.fun PathIdTrunc₀Iso
  (sym (Iso.leftInv (degree∥₂Iso n) (∣ f ∘ g ∣₂))
  ∙ cong (Iso.inv (degreeIso n))
     (degree-comp (suc n) f g ∙ ·Comm _ _ ∙ sym (degree-comp (suc n) g f))
  ∙ Iso.leftInv (degree∥₂Iso n) (∣ g ∘ f ∣₂)))

suspFunS∙ : {n : ℕ} → (S₊ n → S₊ n) → S₊∙ (suc n) →∙ S₊∙ (suc n)
suspFunS∙ {n = zero} f with (f true)
... | false = invLooper , refl
... | true = idfun S¹ , refl
suspFunS∙ {n = suc n} f = suspFun f , refl

degree-susp : (n : ℕ) (f : (S₊ (suc n) → S₊ (suc n)))
            → degree (suc n) f ≡ degree (suc (suc n)) (suspFun f)
degree-susp n f =
  cong (Iso.fun (Hⁿ-Sⁿ≅ℤ n .fst))
    (sym (Iso.rightInv (fst (suspensionAx-Sn n n)) _)
    ∙ cong (Iso.fun (suspensionAx-Sn n n .fst)) lem)
  where
  lem : Iso.inv (suspensionAx-Sn n n .fst) ∣ ∣_∣ₕ ∘ f ∣₂
       ≡ ∣ ∣_∣ₕ ∘ suspFun f ∣₂
  lem = cong ∣_∣₂ (funExt
    λ { north → refl
      ; south → cong ∣_∣ₕ (merid (ptSn (suc n)))
      ; (merid a i) j →
        ∣ compPath-filler (merid (f a)) (sym (merid (ptSn (suc n)))) (~ j) i ∣ₕ})
