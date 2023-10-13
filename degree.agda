{-# OPTIONS --cubical --allow-unsolved-metas #-}
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


degree : (n : ℕ) → (S₊ n → S₊ n) → ℤ
degree zero f = 0
degree (suc n) f = Iso.fun ((Hⁿ-Sⁿ≅ℤ n) .fst) ∣ (λ x → ∣ f x ∣) ∣₂

degree∙ : (n : ℕ) → (S₊∙ n →∙ S₊∙ n) → ℤ
degree∙ zero f = 0
degree∙ (suc n) f = Iso.fun ((Hⁿ-Sⁿ≅ℤ n) .fst) ∣ (λ x → ∣ fst f x ∣) ∣₂


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

  -- move somewhere
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

multSⁿ↬ : (n : ℕ) (f g : ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂)
 → ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂ 
multSⁿ↬ n = ST.rec2 squash₂ λ f g → ∣ f ∘ g ∣₂

πₙSⁿ : (n : ℕ) → Group₀
πₙSⁿ n = π'Gr n (S₊∙ (suc n))

multπₙ : (n : ℕ) → (f g : πₙSⁿ n .fst) → πₙSⁿ n .fst
multπₙ n = ST.rec2 squash₂ λ f g → ∣ f ∘∙ g ∣₂

premultHⁿSⁿ : (n : ℕ) → (f g : S₊ (suc n) → coHomK (suc n)) → (S₊ (suc n) → coHomK (suc n)) 
premultHⁿSⁿ n f g x = TR.rec (isOfHLevelTrunc (3 +ℕ n)) f (g x)

multHⁿSⁿ : (n : ℕ) → (f g : coHom (suc n) (S₊ (suc n))) → coHom (suc n) (S₊ (suc n))
multHⁿSⁿ n = ST.rec2 squash₂ (λ f g → ∣ premultHⁿSⁿ n f g ∣₂)

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

grr' : (m : ℕ) (f g h : _) → multHⁿSⁿ m (f +ₕ g) h ≡ (multHⁿSⁿ m f h) +ₕ (multHⁿSⁿ m g h)
grr' m = ST.elim3 (λ _ _ _ → isSetPathImplicit)
  λ f g h → cong ∣_∣₂ (funExt λ t → lem f g h t _ refl)
  where
  lem : (f g h : S₊ (suc m) → coHomK (suc m))
    → (t : _) (ht : _)
    → h t ≡ ht
    → premultHⁿSⁿ m (λ x → +ₖ-syntax (suc m) (f x) (g x)) h t ≡
      +ₖ-syntax (suc m) (premultHⁿSⁿ m f h t) (premultHⁿSⁿ m g h t)
  lem f g h t =
    TR.elim (λ _ → isOfHLevelΠ (3 +ℕ m) λ _
    → isOfHLevelPath (3 +ℕ m) (isOfHLevelTrunc (3 +ℕ m)) _ _)
     λ ht q →
          (λ i → TR.rec (isOfHLevelTrunc (3 +ℕ m)) (λ x → f x +ₖ g x) (q i))
        ∙ cong₂ _+ₖ_ (λ i → TR.rec (isOfHLevelTrunc (3 +ℕ m)) f (q (~ i)))
                     λ i → TR.rec (isOfHLevelTrunc (3 +ℕ m)) g (q (~ i))


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

coHomGenInd : ∀ {ℓ} (n : ℕ) (P : coHom (suc n) (S₊ (suc n)) → Type ℓ)
            → ((a : ℤ) → P (a ℤ[ coHomGr (suc n) (S₊ (suc n)) ]· ∣ ∣_∣ₕ ∣₂))
            → (x : _) → P x
coHomGenInd = {!!}

coHomGenInd2 : ∀ {ℓ} (n : ℕ) (P : coHom (suc n) (S₊ (suc n)) → Type ℓ)
            → (P (∣ ∣_∣ₕ ∣₂))
            → ((f : _) → P f → P (∣ ∣_∣ₕ ∣₂ +ₕ f))
            → ((f : _) → P f → P (-ₕ f))
            → (x : _) → P x
coHomGenInd2 = {!!}


module mult-props (m : ℕ) where
  private
    hlev-imp : ∀ {x y : coHomK (suc m)} → isOfHLevel (3 +ℕ m) (x ≡ y)
    hlev-imp = isOfHLevelPath (3 +ℕ m) (isOfHLevelTrunc (3 +ℕ m)) _ _

  multHⁿSⁿ-0ₗ : (f : _) → multHⁿSⁿ m (0ₕ (suc m)) f ≡ 0ₕ (suc m)
  multHⁿSⁿ-0ₗ =
    ST.elim (λ _ → isSetPathImplicit)
      λ f → cong ∣_∣₂
        (funExt λ x → cohom-im-elim m (λ s → rec₊ (isOfHLevelTrunc (3 +ℕ m)) (λ _ → 0ₖ (suc m)) s ≡ 0ₖ (suc m))
        (λ _ → hlev-imp)
        f
        x
        λ _ _ → refl)

  multHⁿSⁿ-0ᵣ : (f : _) → multHⁿSⁿ m f (0ₕ (suc m)) ≡ 0ₕ (suc m)
  multHⁿSⁿ-0ᵣ = ST.elim (λ _ → isSetPathImplicit)
    λ f → TR.rec (isProp→isOfHLevelSuc m (squash₂ _ _)) (λ p i → ∣ (λ _ → p i) ∣₂)
      (isConnectedPath _ (isConnectedKn _) (f (ptSn _)) (0ₖ _) .fst)

  multHⁿSⁿ-invₗ : (f g : _) → multHⁿSⁿ m (-ₕ f) g ≡ -ₕ (multHⁿSⁿ m f g)
  multHⁿSⁿ-invₗ = ST.elim2 (λ _ _ → isSetPathImplicit)
    λ f g → cong ∣_∣₂
      (funExt λ x → cohom-im-elim m
        (λ gt → rec₊ (isOfHLevelTrunc (3 +ℕ m)) (λ x₁ → -ₖ-syntax (suc m) (f x₁)) gt
               ≡ -ₖ (rec₊ (isOfHLevelTrunc (3 +ℕ m)) f gt))
        (λ _ → hlev-imp)
        g x
        λ r s → refl)

  multHⁿSⁿ-invᵣ : (g f : _) → multHⁿSⁿ m f (-ₕ g) ≡ -ₕ (multHⁿSⁿ m f g)
  multHⁿSⁿ-invᵣ = ST.elim (λ _ → isSetΠ (λ _ → isSetPathImplicit))
    λ g → coHomGenInd2 m _
           (cong ∣_∣₂ (funExt λ x → {!!}))
           {!!}
           {!!}
    {-
    λ f → coHomGenInd m _ λ a → {!multHⁿSⁿ m ∣ f ∣₂
      (-ₕ (a ℤ[ coHomGr (suc m) (S₊ (suc m)) ]· ∣ (λ a₁ → ∣ a₁ ∣) ∣₂))!}-}
    {-
      (funExt λ x → cohom-im-elim m
        (λ gt → rec₊ (isOfHLevelTrunc (3 +ℕ m)) f (-ₖ gt)
               ≡ -ₖ (rec₊ (isOfHLevelTrunc (3 +ℕ m)) f gt))
        (λ _ → hlev-imp)
        g x
        λ r s → {!!} ∙∙ {!!} ∙∙ {!!})
-}

grr'-nice-pos : (n m : ℕ) (a : ℕ) (f g : _)
  → multHⁿSⁿ m ((pos a) ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· f) g
  ≡ (pos a) ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· (multHⁿSⁿ m f g)
grr'-nice-pos n m zero f g = mult-props.multHⁿSⁿ-0ₗ m g
grr'-nice-pos n m (suc a) f g =
     (λ _ → multHⁿSⁿ m (f +ₕ ((pos a) ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· f)) g)
  ∙∙ grr' _ f (((pos a) ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· f)) g
  ∙∙ cong (multHⁿSⁿ m f g +ₕ_) (grr'-nice-pos n m a f g)

grr'-nice : (n m : ℕ) (a : ℤ) (f g : _)
  → multHⁿSⁿ m (a ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· f) g
  ≡ a ℤ[ (coHomGr (suc m) (S₊ (suc m))) ]· (multHⁿSⁿ m f g)
grr'-nice n m (pos a) = grr'-nice-pos n m a
grr'-nice n m (negsuc n₁) f g = {!!}

-- deg-comp : (n : ℕ) (f g : ∥ (S₊ (suc n) → S₊ (suc n)) ∥₂)
--    → Iso.fun (degreeIso n) (multSⁿ↬ n f g)
--    ≡ (Iso.fun (degreeIso n) f) ·ℤ Iso.fun (degreeIso n) g
-- deg-comp n f g =
--   cong (Iso.fun (compIso (equivToIso (πₙSⁿ≅HⁿSⁿ n .fst)) (fst (Hⁿ-Sⁿ≅ℤ n))))
--         (multπₙ-pres' n f g)
--    ∙ cong (Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n)))
--       (multHⁿSⁿ-pres n (isIso-πₙSⁿ-unpointIso n .fst f) (isIso-πₙSⁿ-unpointIso n .fst g))
--    ∙ ma (πₙSⁿ→HⁿSⁿ-fun n (isIso-πₙSⁿ-unpointIso n .fst f))
--         (πₙSⁿ→HⁿSⁿ-fun n (isIso-πₙSⁿ-unpointIso n .fst g))
--   where
--   ϕ = Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n))
--   ϕ⁻ = Iso.inv (fst (Hⁿ-Sⁿ≅ℤ n))

--   H = coHomGr (suc n) (S₊ (suc n))

--   repl : (f : H .fst) → (ϕ f ℤ[ H ]· ∣ ∣_∣ₕ ∣₂) ≡ f
--   repl f = sym (Iso.leftInv (fst (Hⁿ-Sⁿ≅ℤ n)) _)
--         ∙∙ cong ϕ⁻ lem
--         ∙∙ Iso.leftInv (fst (Hⁿ-Sⁿ≅ℤ n)) f 
--     where
--     lem : ϕ (ϕ f ℤ[ H ]· ∣ ∣_∣ₕ ∣₂) ≡ ϕ f
--     lem = homPresℤ· (_ , snd (Hⁿ-Sⁿ≅ℤ n)) ∣ ∣_∣ₕ ∣₂ (ϕ f)
--         ∙ sym (ℤ·≡· (ϕ f) (fst (Hⁿ-Sⁿ≅ℤ n) .Iso.fun ∣ (λ a → ∣ a ∣) ∣₂))
--         ∙ cong (ϕ f ·ℤ_) (HⁿSⁿ-gen n)
--         ∙ ·Comm (ϕ f) 1

--   ma : (f g : _) → Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n)) (multHⁿSⁿ n f g)
--                   ≡ Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n)) f ·ℤ Iso.fun (fst (Hⁿ-Sⁿ≅ℤ n)) g
--   ma f g = {!!}

-- multHⁿSⁿ-pres↑ : (n : ℕ)  (f g : coHom (suc n) (S₊ (suc n)))
--   → Iso.inv (fst (suspensionAx-Sn n n)) (multHⁿSⁿ n f g)
--   ≡ multHⁿSⁿ (suc n) (Iso.inv (fst (suspensionAx-Sn n n)) f)
--                     (Iso.inv (fst (suspensionAx-Sn n n)) g)
-- multHⁿSⁿ-pres↑ n = ST.elim2 (λ _ _ → isSetPathImplicit)
--   λ f g → TR.rec (isProp→isOfHLevelSuc n (squash₂ _ _))
--     (λ fp → cong ∣_∣₂ (funExt λ { north → refl
--                              ; south → refl
--                              ; (merid a i) j → help f g fp a _ refl j i}))
--                   (isConnectedPath _ (isConnectedKn n) (f (ptSn (suc n))) (0ₖ _) .fst)
--   where
--   T : (f : S₊ (suc n) → coHomK (suc n)) → Susp _ → _
--   T f = (Iso.fun funSpaceSuspIso) (0ₖ (2 +ℕ n) , 0ₖ (2 +ℕ n)
--       , λ x → Kn→ΩKn+1 (suc n) (f x))

--   help : (f g : S₊ (suc n) → coHomK (suc n)) (fpt : f (ptSn (suc n)) ≡ 0ₖ _)
--      (a : S₊ (suc n))
--     → (w : _)
--     → (g a ≡ w)
--       → Kn→ΩKn+1 (suc n) (premultHⁿSⁿ n f g a)
--        ≡ cong (premultHⁿSⁿ (suc n) (T f) (T g)) (merid a)
--   help f g fp a =
--     TR.elim (λ _ → isOfHLevelΠ (3 +ℕ n)
--       λ _ → isOfHLevelPath (3 +ℕ n) (isOfHLevelTrunc (4 +ℕ n) _ _) _ _)
--       λ ga' p
--       → (cong (Kn→ΩKn+1 (suc n)) (cong (TR.rec (isOfHLevelTrunc (3 +ℕ n)) f) p)
--     ∙ rUnit _
--     ∙ cong (cong (T f) (merid ga') ∙_) (sym (cong sym (Kn→ΩKn+10ₖ (suc n)))
--                                      ∙ λ i → sym (Kn→ΩKn+1 (suc n) (fp (~ i))))
--     ∙ sym (cong-∙ (T f) (merid ga') (sym (merid (ptSn (suc n))))))
--     ∙ λ j i → TR.rec (isOfHLevelTrunc (4 +ℕ n)) (T f) (Kn→ΩKn+1 (suc n) (p (~ j)) i)

-- test : {!!}
-- test = {!!}

-- multπₙSⁿ : (n : ℕ) (f g h : _)
--   → multπₙ n f (multπₙ n g h) ≡ multπₙ n (multπₙ n f g) h
-- multπₙSⁿ n =
--   ST.elim3 (λ _ _ _ → isSetPathImplicit)
--     λ f g h → cong ∣_∣₂ (sym (∘∙-assoc f g h))


-- open import Cubical.Foundations.Univalence
-- multHⁿSⁿassoc : (n : ℕ) (f g h : _)
--   → multHⁿSⁿ n f (multHⁿSⁿ n g h) ≡ multHⁿSⁿ n (multHⁿSⁿ n f g) h
-- multHⁿSⁿassoc n = transport (λ i → isAssoc (PP (~ i))) (multπₙSⁿ n)
--   where
--   PP : PathP (λ i → (f g : ua (πₙSⁿ≅HⁿSⁿ n .fst) (~ i)) → ua (πₙSⁿ≅HⁿSⁿ n .fst) (~ i)) (multHⁿSⁿ n) (multπₙ n)
--   PP = toPathP (funExt λ f → funExt λ g
--     → (λ i → (invEq (fst (πₙSⁿ≅HⁿSⁿ n)) (transportRefl
--                (multHⁿSⁿ n (transportRefl (fst (fst (πₙSⁿ≅HⁿSⁿ n)) f) i)
--                           (transportRefl (fst (fst (πₙSⁿ≅HⁿSⁿ n)) g) i)) i)))
--      ∙ sym (cong (invEq (πₙSⁿ≅HⁿSⁿ n .fst)) (multHⁿSⁿ-pres n f g))
--      ∙ retEq (πₙSⁿ≅HⁿSⁿ n .fst) (multπₙ n f g))

--   isAssoc : ∀ {ℓ} {A : Type ℓ} → (f : A → A → A) → Type ℓ
--   isAssoc f = (x y z : _) → f x (f y z) ≡ f (f x y) z

-- grr : (n m : ℕ) (f g : _) → multHⁿSⁿ m (∣ ∣_∣ ∣₂ +ₕ f) g ≡ g +ₕ multHⁿSⁿ m f g
-- grr n m = ST.elim2 (λ _ _ → isSetPathImplicit)
--   λ f g → cong ∣_∣₂ (funExt λ t → gt f g t _ refl)
--   where
--   gt : (f g : S₊ (suc m) → coHomK (suc m))
--     → (t : _) (gt : _)
--     → g t ≡ gt
--     → premultHⁿSⁿ m (λ x₁ → +ₖ-syntax (suc m) ∣ x₁ ∣ (f x₁)) g t ≡
--       +ₖ-syntax (suc m) (g t) (premultHⁿSⁿ m f g t)
--   gt f g t = TR.elim (λ _ → isOfHLevelΠ (3 +ℕ m) λ _
--     → isOfHLevelPath (3 +ℕ m) (isOfHLevelTrunc (3 +ℕ m)) _ _)
--        λ gt q
--     → (λ i → TR.rec (isOfHLevelTrunc (3 +ℕ m)) (λ x → ∣ x ∣ₕ +ₖ f x ) (q i))
--      ∙ cong₂ _+ₖ_ (sym q) λ i → rec₊ (isOfHLevelTrunc (3 +ℕ m)) f (q (~ i))

-- Sⁿ↬HⁿSⁿ : (x y : ℤ)
--   → Iso.inv (fst (Hⁿ-Sⁿ≅ℤ 0)) (x ·ℤ y)
--    ≡ multHⁿSⁿ 0  (Iso.inv (fst (Hⁿ-Sⁿ≅ℤ 0)) x) (Iso.inv (fst (Hⁿ-Sⁿ≅ℤ 0)) y)
-- Sⁿ↬HⁿSⁿ (pos zero) y = {!!}
-- Sⁿ↬HⁿSⁿ (pos (suc n)) y = IsGroupHom.pres· ((invGroupIso H¹-S¹≅ℤ) .snd) y (pos n ·ℤ y)
--                        ∙∙ cong₂ _+ₕ_ (λ _ → Iso.inv (fst (Hⁿ-Sⁿ≅ℤ 0)) y) (Sⁿ↬HⁿSⁿ (pos n) y)
--                        ∙∙ {!multHⁿSⁿassoc 0 (Iso.inv (fst (Hⁿ-Sⁿ≅ℤ 0)) y) (Iso.inv (fst (Hⁿ-Sⁿ≅ℤ 0)) (pos n)) (Iso.inv (fst (Hⁿ-Sⁿ≅ℤ 0)) y)!}
-- Sⁿ↬HⁿSⁿ (negsuc n) y = {!!}
