{-# OPTIONS --cubical --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset

open import Cubical.CW.Base
open import Cubical.CW.ChainComplex

open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int renaming (_+_ to _+ℤ_)
open import Cubical.Data.Fin.Inductive.Base

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.SetQuotients renaming (elimProp to Quotient-elimProp)
open import Cubical.HITs.PropositionalTruncation renaming (rec to ∥∥-rec)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.Algebra.ChainComplex
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

-- First, we equip the 0-dimensional sphere (i.e. the booleans) with a CW structure
BoolSkel : ℕ → Type
BoolSkel 0 = ⊥
BoolSkel (suc n) = Fin 2

BoolCells : ℕ → ℕ
BoolCells 0 = 2
BoolCells (suc n) = 0

BoolAttachingMap : (n : ℕ) → Fin (BoolCells n) × S⁻ n → BoolSkel n
BoolAttachingMap zero ()
BoolAttachingMap (suc n) ()

BoolPushout : (n : ℕ) → BoolSkel (suc n) ≃ Pushout (BoolAttachingMap n) (λ r → fst r)
BoolPushout zero = isoToEquiv (iso inr pushoutToBool pushoutSection (λ b → refl))
  where
    pushoutToBool : Pushout (BoolAttachingMap zero) (λ r → fst r) → Fin 2
    pushoutToBool (inr x) = x

    pushoutSection : (b : Pushout (BoolAttachingMap zero) (λ r → fst r)) → inr (pushoutToBool b) ≡ b
    pushoutSection (inr x) = refl
BoolPushout (suc n) = isoToEquiv (iso inl pushoutToBool pushoutSection (λ b → refl))
  where
    pushoutToBool : Pushout (BoolAttachingMap (suc n)) (λ r → fst r) → Fin 2
    pushoutToBool (inl x) = x

    pushoutSection : (b : Pushout (BoolAttachingMap (suc n)) (λ r → fst r)) → inl (pushoutToBool b) ≡ b
    pushoutSection (inl x) = refl

BoolCW : CWskel Agda.Primitive.lzero
BoolCW = BoolSkel , BoolCells , BoolAttachingMap , (λ x → x) , BoolPushout

open ChainComplex

-- Then, we identify the chain complex associated to the CW structure
BoolChainComplex : ChainComplex ℓ-zero
BoolChainComplex .chain zero = ℤ[Fin 1 ]
BoolChainComplex .chain (suc zero) = ℤ[Fin 2 ]
BoolChainComplex .chain (suc (suc n)) = ℤ[Fin 0 ]
BoolChainComplex .bdry zero = sumCoefficients 2
BoolChainComplex .bdry (suc zero) = trivGroupHom
BoolChainComplex .bdry (suc (suc n)) = trivGroupHom
BoolChainComplex .bdry²=0 zero = GroupHom≡ refl
BoolChainComplex .bdry²=0 (suc zero) = GroupHom≡ refl
BoolChainComplex .bdry²=0 (suc (suc n)) = GroupHom≡ refl

ChainComplex-simpl : CW-AugChainComplex BoolCW ≡ BoolChainComplex
ChainComplex-simpl = aux
  where
    c1 = CW-AugChainComplex BoolCW
    c2 = BoolChainComplex

    ℤ[0]-triv : (x : ℤ[Fin 0 ] .fst) → x ≡ AbGroupStr.0g (ℤ[Fin 0 ] .snd)
    ℤ[0]-triv x = funExt λ { () }

    ℤ[0]-init : (n : ℕ) → (f : AbGroupHom ℤ[Fin 0 ] ℤ[Fin n ]) → f ≡ trivGroupHom
    ℤ[0]-init n f = GroupHom≡ (funExt λ x → cong (fst f) (ℤ[0]-triv x)
                         ∙ IsGroupHom.pres1 (snd f))

    chaineq-hprop : (n : ℕ) → (e1 e2 : compGroupHom (c2 .bdry (suc n)) (c2 .bdry n) ≡ trivGroupHom) → e1 ≡ e2
    chaineq-hprop n e1 e2 = isSetGroupHom (compGroupHom (c2 .bdry (suc n)) (c2 .bdry n)) trivGroupHom e1 e2

    aux : CW-AugChainComplex BoolCW ≡ BoolChainComplex
    aux i .chain zero = ℤ[Fin 1 ]
    aux i .chain (suc zero) = ℤ[Fin 2 ]
    aux i .chain (suc (suc n)) = ℤ[Fin 0 ]
    aux i .bdry zero = augmentation.ϵ-alt BoolCW i
    aux i .bdry (suc zero) = ℤ[0]-init 2 (∂ BoolCW 0) i
    aux i .bdry (suc (suc n)) = ℤ[0]-init 0 (∂ BoolCW (suc n)) i
    aux i .bdry²=0 zero =
      hcomp (λ j → λ { (i = i0) → c1 .bdry²=0 zero
                     ; (i = i1) → chaineq-hprop zero
                                   (transp (λ j → (compGroupHom (aux j .bdry (suc zero)) (aux j .bdry zero) ≡ trivGroupHom))
                                           i0 (c1 .bdry²=0 zero)) (c2 .bdry²=0 zero) j })
            (transp (λ j → (compGroupHom (aux (j ∧ i) .bdry (suc zero)) (aux (j ∧ i) .bdry zero) ≡ trivGroupHom))
                    (~ i) (c1 .bdry²=0 zero))
    aux i .bdry²=0 (suc zero) =
      hcomp (λ j → λ { (i = i0) → c1 .bdry²=0 (suc zero)
                     ; (i = i1) → chaineq-hprop (suc zero)
                                   (transp (λ j → (compGroupHom (aux j .bdry (suc (suc zero))) (aux j .bdry (suc zero)) ≡ trivGroupHom))
                                           i0 (c1 .bdry²=0 (suc zero))) (c2 .bdry²=0 (suc zero)) j })
            (transp (λ j → (compGroupHom (aux (j ∧ i) .bdry (suc (suc zero))) (aux (j ∧ i) .bdry (suc zero)) ≡ trivGroupHom))
                    (~ i) (c1 .bdry²=0 (suc zero)))
    aux i .bdry²=0 (suc (suc n)) =
      hcomp (λ j → λ { (i = i0) → c1 .bdry²=0 (suc (suc n))
                     ; (i = i1) → chaineq-hprop (suc (suc n))
                                   (transp (λ j → (compGroupHom (aux j .bdry (suc (suc (suc n)))) (aux j .bdry (suc (suc n))) ≡ trivGroupHom))
                                           i0 (c1 .bdry²=0 (suc (suc n)))) (c2 .bdry²=0 (suc (suc n))) j })
            (transp (λ j → (compGroupHom (aux (j ∧ i) .bdry (suc (suc (suc n)))) (aux (j ∧ i) .bdry (suc (suc n))) ≡ trivGroupHom))
                    (~ i) (c1 .bdry²=0 (suc (suc n))))

-- Finally, we compute the homology of the chain complex
BoolHomologyZero : (homology 0 BoolChainComplex) ≡ ℤGroup
BoolHomologyZero = uaGroup (GroupIso→GroupEquiv (compGroupIso (invGroupIso iso2) iso1))
  where
    ker = ker∂n zero BoolChainComplex
    im = img∂+1⊂ker∂n zero BoolChainComplex

    ker→ℤ : GroupHom ker ℤGroup
    ker→ℤ .fst (x , xε) = x fzero
    ker→ℤ .snd = makeIsGroupHom (λ x y → refl)

    ℤ→ker : GroupHom ℤGroup ker
    ℤ→ker .fst x = (λ { (0 , _) → x ; (1 , _) → - x })
                     , funExt (λ _ → -Cancel' x)
    ℤ→ker .snd = makeIsGroupHom (λ x y → kerGroup≡ (BoolChainComplex .bdry zero)
                                                       (funExt λ { (0 , _) → refl ; (1 , _) → -Dist+ x y }))

    ker→ℤ→ker : ∀ x → ℤ→ker .fst (ker→ℤ .fst x) ≡ x
    ker→ℤ→ker x = kerGroup≡
                  (BoolChainComplex .bdry zero)
                  (funExt λ { (0 , _) → refl
                            ; (1 , _) → sym (-≡0 (x .fst (fsuc fzero)) (- x .fst fzero)
                                                 (cong ((x .fst (fsuc fzero)) +ℤ_) (-Involutive (x .fst fzero))
                                                  ∙ funExt⁻ (x .snd) fzero)) })

    iso1 : GroupIso ker ℤGroup
    iso1 = (iso (ker→ℤ .fst) (ℤ→ker .fst) (λ b → refl) ker→ℤ→ker) , ker→ℤ .snd

    imSingleton : ∀ x → x ∈ im .fst .fst → x ≡ GroupStr.1g (snd ker)
    imSingleton x h = ∥∥-rec (GroupStr.is-set (snd ker) x (GroupStr.1g (snd ker)))
                             (λ { (e , he) → sym he ∙ kerGroup≡ (BoolChainComplex .bdry zero) refl })
                             h

    contrIm : (x y : fst ker) → _~_ ker (fst im) (snd im) x y → x ≡ y
    contrIm x y h = GroupTheory.invUniqueL ker {x} {GroupStr.inv (snd ker) y} (imSingleton _ h)
                  ∙ GroupTheory.invInv ker y

    iso2 : GroupIso ker (homology 0 BoolChainComplex)
    iso2 = trivialRelIso im contrIm

BoolHomologySuc : (n : ℕ) → (homology (suc n) BoolChainComplex) ≡ UnitGroup₀
BoolHomologySuc n = uaGroup (GroupIso→GroupEquiv isoH)
  where
    ker = ker∂n (suc n) BoolChainComplex
    im = img∂+1⊂ker∂n (suc n) BoolChainComplex
    Hn+1 = homology (suc n) BoolChainComplex

    kerHProp : ∀ (x y : ker .fst) → x ≡ y
    kerHProp (x₀ , x₁) (y₀ , y₁) = kerGroup≡ (BoolChainComplex .bdry (suc n)) (funExt λ { () })

    HSingleton : ∀ (x : fst Hn+1) → x ≡ GroupStr.1g (snd Hn+1)
    HSingleton x = Quotient-elimProp (λ x → GroupStr.is-set (snd Hn+1) x (GroupStr.1g (snd Hn+1)))
                                     (λ a → cong [_] (kerHProp a _)) x

    isoH : GroupIso Hn+1 UnitGroup₀
    isoH = (iso (λ _ → tt) (λ _ → GroupStr.1g (snd Hn+1)) (λ { tt → refl }) λ x → sym (HSingleton x))
           , makeIsGroupHom λ _ _ → refl

-- We obtain the Eilenberg-Steenrod dimension axiom for H̃ˢᵏᵉˡ

ESDimensionZero : H̃ˢᵏᵉˡ BoolCW 0 ≡ ℤGroup
ESDimensionZero = cong (homology zero) ChainComplex-simpl ∙ BoolHomologyZero

ESDimensionSuc : (n : ℕ) → H̃ˢᵏᵉˡ BoolCW (suc n) ≡ UnitGroup₀
ESDimensionSuc n = cong (homology (suc n)) ChainComplex-simpl ∙ (BoolHomologySuc n)
