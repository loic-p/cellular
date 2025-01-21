{-# OPTIONS --cubical --lossy-unification #-}
module Hurewicz.Map where

open import Hurewicz.SubcomplexNew
open import Hurewicz.random

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws as GL
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.Connected
open import Cubical.CW.Homology
open import Cubical.CW.Approximation
open import Cubical.CW.ChainComplex

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Bool
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Sigma
open import Cubical.Data.FinSequence
open import Cubical.Data.Int
open import Cubical.Data.Unit

open import Cubical.HITs.S1
open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.HITs.Susp
open import Cubical.HITs.Pushout
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.SetQuotients as SQ renaming (_/_ to _/s_)
open import Cubical.HITs.Wedge

open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Connected

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Abelianization.Base
open import Cubical.Algebra.Group.Abelianization.Properties as Abi
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Relation.Nullary

open import Hurewicz.SnNew
open import Hurewicz.SphereBouquetCofib2
open import Hurewicz.SphereBouquetCofibHomotopy
open import Hurewicz.SphereBouquetCofibHomotopyP2
open import Cubical.HITs.Bouquet
open import Cubical.HITs.FreeGroup.Base

open import Hurewicz.SphereBouquetCofib2
open import Hurewicz.SphereBouquetCofibHomotopy
open import Hurewicz.SphereBouquetCofibHomotopyP2
open import Cubical.HITs.Bouquet
open import Cubical.HITs.FreeGroup.Base


open import Cubical.Homotopy.Connected
open import Cubical.HITs.Truncation as TR
open import Cubical.CW.Properties


private
  module _ {k : ℕ} (w : Fin k) (x : _) where
    ℤFinGenerator* : lockUnit {ℓ-zero} → ℤ
    ℤFinGenerator* unlock = ℤFinGenerator w x

    mainockℤ : (l : _) → ¬ (fst w ≡ fst x) → ℤFinGenerator* l ≡ pos 0
    mainockℤ unlock nope with (fst w ≟ᵗ fst x)
    ... | (lt ineq) = refl
    ... | (eq p) = ⊥.rec (nope p)
    ... | (gt ineq) = refl

    mainockℤ' : (l : _) → (fst w ≡ fst x) → ℤFinGenerator* l ≡ pos 1
    mainockℤ' unlock aye with (fst w ≟ᵗ fst x)
    ... | (lt ineq) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst x) aye ineq))
    ... | (eq p) = refl
    ... | (gt ineq) = ⊥.rec (¬m<ᵗm (subst (fst x <ᵗ_) aye ineq))

-- todo : fix univ levels
groupHom→AbelianisationGroupHom : ∀ {ℓ} {A : Group ℓ} {B : Group ℓ}
  → (ϕ : GroupHom A B)
  → ((x y : fst B) → GroupStr._·_ (snd B) x y ≡ GroupStr._·_ (snd B) y x)
  → GroupHom (AbGroup→Group (AbelianizationAbGroup A))
              B
fst (groupHom→AbelianisationGroupHom {B = B} ϕ commB) =
  Abi.rec _ (GroupStr.is-set (snd B)) (ϕ .fst)
            λ a b c → IsGroupHom.pres· (ϕ .snd) _ _
            ∙ cong₂ (GroupStr._·_ (snd B)) refl
                    (IsGroupHom.pres· (ϕ .snd) _ _
                   ∙ commB _ _
                   ∙ sym (IsGroupHom.pres· (ϕ .snd) _ _))
            ∙ sym (IsGroupHom.pres· (ϕ .snd) _ _)
snd (groupHom→AbelianisationGroupHom {B = B} ϕ commB) =
  makeIsGroupHom (Abi.elimProp2 _
    (λ _ _ → GroupStr.is-set (snd B) _ _)
    λ a b → IsGroupHom.pres· (ϕ .snd) _ _)

isInducedAbelianisationGroupEquiv : ∀ {ℓ} (A : Group ℓ) (B : Group ℓ)
  → ((x y : fst B) → GroupStr._·_ (snd B) x y ≡ GroupStr._·_ (snd B) y x)
  → (f : fst A → fst B)
  → Type ℓ
isInducedAbelianisationGroupEquiv A B iscomm f =
  Σ[ ishom ∈ IsGroupHom (snd A) f (snd B) ]
    isEquiv (fst (groupHom→AbelianisationGroupHom (f , ishom) iscomm))

isPropIsInducedAbelianisationGroupEquiv : ∀ {ℓ} {A : Group ℓ} {B : Group ℓ}
  → {isc : (x y : fst B) → GroupStr._·_ (snd B) x y ≡ GroupStr._·_ (snd B) y x}
  → {f : fst A → fst B} → isProp (isInducedAbelianisationGroupEquiv A B isc f)
isPropIsInducedAbelianisationGroupEquiv =
  isPropΣ (isPropIsGroupHom _ _) λ _ → isPropIsEquiv _




-- todo: update universe level after fixing it in abelianisaion file
module _ where
  preHurewiczMap : {n : ℕ} (X : CW ℓ-zero) (x : fst X) (f : S₊∙ (suc n) →∙ (fst X , x))
    → GroupHom (H̃ᶜʷ (Sᶜʷ (suc n)) (suc n)) (H̃ᶜʷ X (suc n))
  preHurewiczMap {n = n} X x f = H̃ᶜʷ→ {C = Sᶜʷ (suc n)} {D = X} (suc n) (fst f)

  HurewiczMapUntrunc :  {n : ℕ} (X : CW ℓ-zero) (x : fst X)
    (f : S₊∙ (suc n) →∙ (fst X , x)) → H̃ᶜʷ X (suc n) .fst
  HurewiczMapUntrunc {n = n} X x f = preHurewiczMap X x f .fst (genHₙSⁿ n)

  HurewiczMap : {n : ℕ} (X : CW ℓ-zero) (x : fst X)
    → π' (suc n) (fst X , x)
    → fst (H̃ᶜʷ X (suc n))
  HurewiczMap X x = ST.rec (GroupStr.is-set (snd (H̃ᶜʷ X _))) (HurewiczMapUntrunc X x)



  HurewiczMapHom :  {n : ℕ} (X : CW ℓ-zero) (x : fst X) (f g : π' (suc n) (fst X , x))
    → isConnected 2 (fst X)
     → HurewiczMap X x (·π' n f g)
      ≡ GroupStr._·_ (snd (H̃ᶜʷ X (suc n)))
          (HurewiczMap X x f) (HurewiczMap X x g)
  HurewiczMapHom {n = n} = uncurry λ X → PT.elim
    (λ x → isPropΠ4 λ _ _ _ _ → GroupStr.is-set (snd (H̃ᶜʷ (X , x) (suc n))) _ _)
    (uncurry λ Xsk → EquivJ (λ X y → (x : X) (f g : π' (suc n) (X , x)) →
      isConnected 2 X →
      HurewiczMap (X , ∣ Xsk , y ∣₁) x (·π' n f g) ≡
      (snd (H̃ᶜʷ (X , ∣ Xsk , y ∣₁) (suc n)) GroupStr.·
       HurewiczMap (X , ∣ Xsk , y ∣₁) x f)
      (HurewiczMap (X , ∣ Xsk , y ∣₁) x g))
      (λ x → TR.rec (isPropΠ3 (λ _ _ _ → squash/ _ _))
        (uncurry λ x₀ → resch Xsk x x₀ x)
        (isConnected-CW↪∞ 1 Xsk x .fst)))
    where
    module _ (Xsk : CWskel ℓ-zero) (x : realise Xsk) where
      ∥x₀∥ : hLevelTrunc 1 (Xsk .fst 1)
      ∥x₀∥ = TR.map fst (isConnected-CW↪∞ 1 Xsk x .fst)

      X' : CW ℓ-zero
      X' = realise Xsk , ∣ Xsk , idEquiv (realise Xsk) ∣₁


      resch : (x₁ : fst Xsk 1) (x : realise Xsk) (y : CW↪∞ Xsk 1 x₁ ≡ x)
        (f g : π' (suc n) (realise Xsk , x))
        → isConnected 2 (realise Xsk)
        → HurewiczMap X' x (·π' n f g)
        ≡ GroupStr._·_ (snd (H̃ᶜʷ X' (suc n)))
           (HurewiczMap X' x f) (HurewiczMap X' x g)
      resch x₀ = J> ST.elim2 (λ _ _ → isSetΠ λ _ → isProp→isSet (squash/ _ _))
        λ f g t → PT.rec2 (squash/ _ _)
          (λ {(f' , fp) (g' , gp) → lem f' g' f fp g gp})
          (approxSphereMap∙ Xsk x₀ n f)
          (approxSphereMap∙ Xsk x₀ n g)
       where
       X∙ : Pointed₀
       X∙ = fst Xsk (suc (suc n)) , CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)

       X* : (n : ℕ) → Pointed₀
       X* n = fst Xsk (suc (suc n)) , CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)

       GoalTy : (f g : S₊∙ (suc n) →∙ (realise Xsk , CW↪∞ Xsk 1 x₀)) → Type _
       GoalTy f g =
         HurewiczMap X' (CW↪∞ Xsk 1 x₀) (·π' n ∣ f ∣₂ ∣ g ∣₂)
             ≡ GroupStr._·_ (snd (H̃ᶜʷ X' (suc n)))
               (HurewiczMap X' (CW↪∞ Xsk 1 x₀) ∣ f ∣₂)
               (HurewiczMap X' (CW↪∞ Xsk 1 x₀) ∣ g ∣₂)
       module _ (f' g' : S₊∙ (suc n) →∙ X∙) where
         multCellMap : finCellApprox (Sˢᵏᵉˡ (suc n)) Xsk (fst (∙Π (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g')) ∘
           invEq (isCWSphere (suc n) .snd))
                        (suc (suc (suc (suc n))))
         multCellMap =  betterFinCellApproxS Xsk (suc n) x₀ (∙Π f' g') (∙Π (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g'))
                            (λ x → funExt⁻ (cong fst (∙Π∘∙ n f' g' (incl∙ Xsk x₀))) x ∙ refl) (suc (suc (suc (suc n))))

         G : (n : ℕ) → _
         G n = BouquetFuns.CTB (suc n) (CWskel-fields.card Xsk (suc n))
                                 (CWskel-fields.α Xsk (suc n))
                                 (CWskel-fields.e Xsk (suc n))


         fEq : (n : ℕ) (f' : S₊∙ (suc n) →∙ X* n) (q : _) (x : _) (a : _)
           → f' .fst ((invEq (SαEqGen (suc n) (suc n) (eq x) q) ∘ inl) a) ≡ CWskel∙ Xsk x₀ (suc n)
         fEq n f' (lt x₁) x a = snd f'
         fEq n f' (eq x₁) x a = ⊥.rec (¬m<ᵗm (subst (_<ᵗ_ (suc n)) ((sym x₁) ∙ cong predℕ x) <ᵗsucm)) --
         fEq n f' (gt x₁) x a = ⊥.rec (¬-suc-n<ᵗn (subst (_<ᵗ_ (suc (suc n))) (λ i → predℕ ( (x i))) x₁)) --

         alt : (n : ℕ) (f : S₊∙ (suc n) →∙ X* n) (p : _) (q : _)
           → cofib (invEq (SαEqGen (suc n) (suc n) p q) ∘ inl) → cofibCW (suc n) Xsk
         alt n f p q (inl x) = inl x
         alt n f (lt x₁) q (inr x) = inl tt
         alt n f (eq x₁) p (inr x) = inr (f .fst x)
         alt n f (gt x₁) q (inr x) = inl tt
         alt n f (lt x) q (push a i) = inl tt
         alt n f (eq x) q (push a i) = (push (CWskel∙ Xsk x₀ n) ∙ λ i → inr (fEq n f q x a (~ i))) i
         alt n f (gt x) q (push a i) = inl tt

-- G n (alt n f' p q
         F : (n : ℕ) (f : S₊∙ (suc n) →∙ X* n) (p : _) (q : _) (x : _) → _
         F n f' p q x =  G n (alt n f' p q (BouquetFuns.BTC (suc n)
                                  (ScardGen (suc n) (suc n) p)
                                  (SαGen (suc n) (suc n) p q)
                                  (SαEqGen (suc n) (suc n) p q)
                                  x))

         module _ (f' : S₊∙ (suc n) →∙ X∙) (Q : _) where
           private
             fbet = (betterFinCellApproxS Xsk (suc n) x₀ f'
                 (incl∙ Xsk x₀ ∘∙ f') Q (suc (suc (suc (suc n)))))

           alt≡inr : (x : _)
             → prefunctoriality.fn+1/fn (suc (suc (suc (suc n)))) (fbet .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) (inr x)
             ≡ alt n f' (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n)) (inr x)
           alt≡inr x with (n ≟ᵗ n)
           ... | lt x₁ = ⊥.rec (¬m<ᵗm x₁)
           ... | eq x₁ = λ i → inr ((cong (λ p → subst (fst Xsk) p (fst f' x))
             (cong sym (isSetℕ _ _ (cong suc (cong suc x₁)) refl))
             ∙ transportRefl (fst f' x)) i)
           ... | gt x₁ = ⊥.rec (¬m<ᵗm x₁)

           alt≡push : (a : _) → Square refl (alt≡inr (CW↪ (Sˢᵏᵉˡ (suc n)) (suc n) a))
             (push (makeFinSequenceMapGen Xsk (suc n) x₀ (fst f') (snd f') (suc n) (Trichotomyᵗ-suc (n ≟ᵗ suc n)) a)
               ∙ (λ i → inr (makeFinSequenceMapComm Xsk (suc n) x₀ (fst f') (snd f') (suc n)
                               (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n)) a (~ i))))
             (cong (alt n f' (Trichotomyᵗ-suc (Trichotomyᵗ-suc (n ≟ᵗ n))) (Trichotomyᵗ-suc (n ≟ᵗ suc n))) (push a))
           alt≡push a with (n ≟ᵗ n)
           ... | lt x = ⊥.rec (¬m<ᵗm x)
           ... | eq x = flipSquare (help (cong suc (cong suc x)) (sym (isSetℕ _ _ _ _)))
             where

             cool : makeFinSequenceMapGen∙ Xsk _ x₀ (fst f') (snd f') (suc n) (eq refl)
                  ≡ transportRefl _ ∙ snd f'
             cool = cong₂ _∙_ (λ j i → subst (fst Xsk) (isSet→isGroupoid isSetℕ _ _ _ _ (isSetℕ (suc (suc n)) _ refl refl) refl j i)
                              (snd f' i)) (transportRefl _)
                  ∙ λ i → (λ j → transportRefl (snd f' (j ∧ ~ i)) (j ∧ i))
                         ∙ λ j → transportRefl (snd f' (~ i ∨ j)) (i ∨ j)

             help : (w : suc (suc n) ≡ suc (suc n)) (t : refl ≡ w)
               → Square ((push (makeFinSequenceMapGen Xsk (suc n) x₀ (fst f') (snd f') (suc n) (Trichotomyᵗ-suc (n ≟ᵗ suc n)) a)
                         ∙ (λ i → inr (makeFinSequenceMapComm Xsk (suc n) x₀ (fst f') (snd f') (suc n)
                                         (eq w) (suc n ≟ᵗ suc (suc n)) a (~ i)))))
                          (λ i → alt n f' (eq w)
                            (Trichotomyᵗ-suc (n ≟ᵗ suc n)) (push a i))
                          (λ _ → inl tt)
                          λ i → inr ((cong (λ p → subst (fst Xsk) p (fst f' (invEq (SαEqGen (suc n) (suc n) (eq w)
                                           (Trichotomyᵗ-suc (n ≟ᵗ suc n))) (inl a))))
                                     (sym (cong sym t)) ∙ transportRefl _) i)
             help with (n ≟ᵗ suc n)
             ... | lt w =
               J> (cong₂ _∙_ refl ((λ j i → inr ((lUnit (cool j) (~ j)) (~ i)))
                                              ∙ cong sym (cong-∙ inr (transportRefl _)
                                                         (snd f'))
                                              ∙ symDistr _ _)
                        ∙ GL.assoc _ _ _)
                        ◁ flipSquare (flipSquare (symP (compPath-filler
                                     (push (CWskel∙ Xsk x₀ n)
                                     ∙ (λ i₁ → inr (snd f' (~ i₁))))
                                     (sym (transportRefl (inr (f' .snd i0))))))
                        ▷ λ j i → inr (lUnit (transportRefl (fst f' (ptSn (suc n)))) j i))
             ... | eq x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) x <ᵗsucm))
             ... | gt x = ⊥.rec (¬-suc-n<ᵗn x)
           ... | gt x = ⊥.rec (¬m<ᵗm x)

           alt≡ : (x : _) → prefunctoriality.fn+1/fn (suc (suc (suc (suc n)))) (fbet .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) x
                          ≡ alt n f' (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n)) x
           alt≡ (inl x) = refl
           alt≡ (inr x) = alt≡inr x
           alt≡ (push a i) = alt≡push a i

           bouquetFunct≡ : prefunctoriality.bouquetFunct (suc (suc (suc (suc n)))) (fbet .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm))
                         ≡ F n f' (suc (suc n) ≟ᵗ suc (suc n)) (suc n ≟ᵗ suc (suc n))
           bouquetFunct≡ = funExt (λ x → cong (G n) (alt≡ _))


         fbet = (betterFinCellApproxS Xsk (suc n) x₀ f'
                        (incl∙ Xsk x₀ ∘∙ f') (λ _ → refl) (suc (suc (suc (suc n)))))
         gbet = (betterFinCellApproxS Xsk (suc n) x₀ g'
                        (incl∙ Xsk x₀ ∘∙ g') (λ _ → refl) (suc (suc (suc (suc n)))))


         wraplem : ∀ {ℓ} {A : Type ℓ} {x : A} (y : A) (p : x ≡ y) (l1 l2 : y ≡ y)
           → p ∙∙ (l1 ∙ l2) ∙∙ sym p
           ≡ (p ∙∙ l1 ∙∙ sym p) ∙ (p ∙∙ l2 ∙∙ sym p)
         wraplem = J> λ l1 l2 → sym (rUnit _) ∙ cong₂ _∙_ (rUnit l1) (rUnit l2)

         itMain : (n : ℕ) (f' g' : _) (p : _) (q : _) (x : _)
           → F n (∙Π f' g') p q x
           ≡ SphereBouquet∙Π (F n f' p q , refl)
                             (F n g' p q , refl) .fst x
         itMain n f' g' (lt x₁) q x = ⊥.rec (¬m<ᵗm x₁)
         itMain n f' g' (eq x₁) (lt x₂) (inl x) = refl
         itMain zero f' g' (eq x₁) (lt x₂) (inr (t , base)) = refl
         itMain zero f' g' (eq x₁) (lt x₂) (inr ((zero , tt) , loop i)) j = M j i
           where
           L : (h : S₊∙ 1 →∙ X* zero)
             → cong (alt zero h (eq x₁) (lt x₂)
                                 ∘ inr ∘ invEq (SαEqGen 1 1 (eq x₁) (lt x₂)))
                                 (push (fzero , false) ∙ sym (push (fzero , true)))
             ≡ λ i → inr (fst h (loop i))
           L h = cong-∙  (alt zero h (eq x₁) (lt x₂)
                        ∘ inr ∘ invEq (SαEqGen 1 1 (eq x₁) (lt x₂)))
                          (push (fzero , false)) (sym (push (fzero , true)))
               ∙ cong₂ _∙_ (λ i j → inr (h .fst (SuspBool→S¹ (merid (subst S₊ (isSetℕ _ _ (cong (predℕ ∘ predℕ) x₁) refl i) false) j))))
                           (λ i j → inr (h .fst (SuspBool→S¹ (merid (subst S₊ (isSetℕ _ _ (cong (predℕ ∘ predℕ) x₁) refl i) true) (~ j)))))
               ∙ sym (rUnit _)
           w = cong (F zero f' (eq x₁) (lt x₂)) (sym (push fzero)) ∙ refl
           M : cong (F zero (∙Π f' g') (eq x₁) (lt x₂)) (λ i → inr (fzero , loop i))
             ≡ (sym w ∙∙ cong (F zero f' (eq x₁) (lt x₂)) (λ i → inr (fzero , loop i)) ∙∙ w)
             ∙ (sym w ∙∙ cong (F zero g' (eq x₁) (lt x₂)) (λ i → inr (fzero , loop i)) ∙∙ w)
           M = cong (cong (G zero)) (cong-∙∙ (alt zero (∙Π f' g') (eq x₁) (lt x₂)) _ _ _
                                    ∙ cong₃ _∙∙_∙∙_ (sym (rUnit (push x₀))) (L (∙Π f' g')
                                    ∙ cong-∙ inr _ _)
                                    (cong sym (sym (rUnit (push x₀))))
                                    ∙ wraplem _ _ _ _)
             ∙ (cong-∙ (G zero) _ _
             ∙ cong₂ _∙_ (cong (cong (G zero))
               λ i → compPath-filler (push x₀) (λ t → inr (sym (snd f') t)) i
                   ∙∙ (λ j → inr (doubleCompPath-filler (sym (snd f')) (cong (fst f') loop) (snd f') (~ i) j))
                   ∙∙ sym (compPath-filler (push x₀) (λ t → inr (sym (snd f') t)) i))
               λ i → (cong (G zero))
                     (compPath-filler (push x₀) (λ t → inr (sym (snd g') t)) i
                   ∙∙ (λ j → inr (doubleCompPath-filler (sym (snd g')) (cong (fst g') loop) (snd g') (~ i) j))
                   ∙∙ sym (compPath-filler (push x₀) (λ t → inr (sym (snd g') t)) i)))
             ∙ cong₂ _∙_ (sym (cong (cong (G zero)) (cong-∙∙ (alt zero f' (eq x₁) (lt x₂)) _ _ _
                                    ∙ cong₃ _∙∙_∙∙_ refl (L f') refl))
                                    ∙ rUnit (cong (F zero f' (eq x₁) (lt x₂)) (λ i → inr (fzero , loop i)))
                       ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
                         (sym (cong (cong (G zero)) (cong-∙∙ (alt zero g' (eq x₁) (lt x₂)) _ _ _
                                    ∙ cong₃ _∙∙_∙∙_ refl (L g') refl))
                         ∙ rUnit (cong (F zero g' (eq x₁) (lt x₂)) (λ i → inr (fzero , loop i)))
                       ∙ cong₃ _∙∙_∙∙_ (rUnit refl) refl (rUnit refl))
         itMain (suc n) f' g' (eq x₁) (lt x₂) (inr (t , north)) = refl
         itMain (suc n) f' g' (eq x₁) (lt x₂) (inr (t , south)) = refl
         itMain (suc n) f' g' (eq x₁) (lt x₂) (inr ((zero , tt) , merid a i)) j = M j i
           where
           H : (x : _) → transport (λ i₂ → S₊ (predℕ (predℕ (x₁ i₂)))) x ≡ x
           H x = cong (λ p → transport p x) (cong (cong S₊) (isSetℕ _ _ _ refl))
               ∙ transportRefl x

           Lelem : (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) (a : _)
             → _
           Lelem h a = (push (CWskel∙ Xsk x₀ (suc n))
                    ∙∙ (λ i → inr ((sym (snd h) ∙∙ cong (fst h) (σS a) ∙∙ snd h) i))
                    ∙∙ sym (push (CWskel∙ Xsk x₀ (suc n))))

           L : (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) (a : _)
             → cong (F (suc n) h (eq x₁) (lt x₂)) (λ i → inr (fzero , merid a i))
             ≡ cong (G (suc n)) (Lelem h a)
           L h a = cong (cong (G (suc n)))
               (cong-∙∙ (alt (suc n) h (eq x₁) (lt x₂)) _ _ _
             ∙ cong₃ _∙∙_∙∙_ refl
                (cong-∙ (alt (suc n) h (eq x₁) (lt x₂)
                              ∘ inr
                              ∘ invEq (SαEqGen (suc (suc n)) (suc (suc n)) (eq x₁) (lt x₂)))
                               (push (fzero , a)) (sym (push (fzero , ptSn (suc n))))
                       ∙ cong₂ _∙_ (λ j i → inr (h .fst (merid (H a j) i)))
                                   (λ j i → inr (h .fst (merid (H (ptSn (suc n)) j) (~ i))))
                       ∙ sym (cong-∙ (λ x → inr (h .fst x)) (merid a) (sym (merid (ptSn (suc n)))))) refl
             ∙ λ i → compPath-filler (push (CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)))
                                      (λ i → inr (snd h (~ i))) (~ i)
               ∙∙ (λ j → inr (doubleCompPath-filler (sym (snd h))
                                (λ i → fst h (σS a i))
                                (snd h) i j))
               ∙∙ sym (compPath-filler (push (CW↪ Xsk (suc n) (CWskel∙ Xsk x₀ n)))
                                       (λ i → inr (snd h (~ i))) (~ i)))

           L∙ : (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) → cong (F (suc n) h (eq x₁) (lt x₂))
                (λ i → inr (fzero , merid (ptSn (suc n)) i))
              ≡ refl
           L∙ h = L h (ptSn (suc n)) ∙ cong (cong (G (suc n)))
             (cong₃ _∙∙_∙∙_ refl
               ((λ j i → inr ((cong₃ _∙∙_∙∙_ refl (cong (cong (fst h)) σS∙) refl
                             ∙ ∙∙lCancel (snd h)) j i))) refl
             ∙ ∙∙lCancel _)

           L' : (h : S₊∙ (suc (suc n)) →∙ X* (suc n)) (a : _)
             → cong (F (suc n) h (eq x₁) (lt x₂)) (λ i → inr (fzero , σS a i)) ≡ L h a i1
           L' h a = cong-∙ (λ q → F (suc n) h (eq x₁) (lt x₂) (inr (fzero , q)))
                           (merid a) (sym (merid (ptSn (suc n))))
                  ∙ cong₂ _∙_ (L h a) (cong sym (L∙ h))
                  ∙ sym (rUnit (L h a i1))

           Lelem≡ : (a : _) → Lelem (·Susp (S₊∙ (suc n)) f' g') a ≡ Lelem f' a ∙ Lelem g' a
           Lelem≡ a =
             cong₃ _∙∙_∙∙_ refl
                   (λ i j → inr ((sym (rUnit (cong (fst (·Susp (S₊∙ (suc n)) f' g')) (σS a)))
                                ∙ cong-∙ (fst (·Susp (S₊∙ (suc n)) f' g'))
                                         (merid a) (sym (merid (ptSn (suc n))))
                                ∙ cong₂ _∙_ refl (cong sym
                                  (cong₂ _∙_
                                    (cong₃ _∙∙_∙∙_ refl
                                       (cong (cong (fst f')) (rCancel (merid (ptSn (suc n))))) refl
                                      ∙ ∙∙lCancel (snd f'))
                                    (cong₃ _∙∙_∙∙_ refl
                                       (cong (cong (fst g')) (rCancel (merid (ptSn (suc n))))) refl
                                      ∙ ∙∙lCancel (snd g'))
                                  ∙ sym (rUnit refl)))
                                ∙ sym (rUnit _)) i j)) refl
             ∙ cong₃ _∙∙_∙∙_ refl (cong-∙ inr _ _) refl
             ∙ wraplem _ _ _ _

           w = cong (F (suc n) f' (eq x₁) (lt x₂)) (sym (push fzero)) ∙ refl
           M : cong (F (suc n) (∙Π f' g') (eq x₁) (lt x₂)) (λ i → inr (fzero , merid a i))
             ≡ (sym w ∙∙ cong (F (suc n) f' (eq x₁) (lt x₂)) (λ i → inr (fzero , σS a i)) ∙∙ w)
             ∙ (sym w ∙∙ cong (F (suc n) g' (eq x₁) (lt x₂)) (λ i → inr (fzero , σS a i)) ∙∙ w)
           M = ((L (∙Π f' g') a
              ∙ cong (cong (G (suc n))) (Lelem≡ a))
              ∙ cong-∙ (G (suc n)) (Lelem f' a) (Lelem g' a))
             ∙ cong₂ _∙_
                 (rUnit _ ∙ cong₃ _∙∙_∙∙_ (rUnit refl) (sym (L' f' a)) (rUnit refl))
                 (rUnit _ ∙ cong₃ _∙∙_∙∙_ (rUnit refl) (sym (L' g' a)) (rUnit refl))

         itMain zero f' g' (eq x₁) (lt x₂) (push a i) = refl
         itMain (suc n) f' g' (eq x₁) (lt x₂) (push a i) = refl
         itMain n f' g' (eq x₁) (eq x₂) x = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) x₂ <ᵗsucm))
         itMain n f' g' (eq x₁) (gt x₂) x = ⊥.rec (¬-suc-n<ᵗn x₂)
         itMain n f' g' (gt x₁) q x = ⊥.rec (¬m<ᵗm x₁)

         it : (x : _) → prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
                (multCellMap .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) x
            ≡ SphereBouquet∙Π
               (prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
                 (fbet .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) , refl)
               (prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
                 (gbet .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) , refl) .fst x

         it x = funExt⁻ (bouquetFunct≡ (∙Π f' g') λ _ → refl) x
           ∙ itMain n f' g' _ _ x
           ∙ λ i → SphereBouquet∙Π
                     (bouquetFunct≡ f' (λ _ → refl) (~ i) , (λ _ → inl tt))
                     (bouquetFunct≡ g' (λ _ → refl) (~ i) , (λ _ → inl tt)) .fst x

         main : GoalTy (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g')
         main = funExt⁻ (cong fst (H̃ˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) Xsk (suc n)
             {f = (fst (∙Π (incl∙ Xsk x₀ ∘∙ f') (incl∙ Xsk x₀ ∘∙ g')) ∘
                invEq (isCWSphere (suc n) .snd))} multCellMap)) (genHₙSⁿ n)
              ∙ cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
                ((λ i → bouquetDegree (λ x → it x i) .fst (λ _ → pos 1))
                   ∙ funExt⁻ (cong fst (bouquetDegree+ _ _ _
                      (prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
                        (fbet .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) , refl)
                      (prefunctoriality.bouquetFunct (suc (suc (suc (suc n))))
                        (gbet .fst) (suc n , <ᵗ-trans-suc (<ᵗ-trans <ᵗsucm <ᵗsucm)) , refl)))
                      λ _ → pos 1))
              ∙ cong₂ (GroupStr._·_ (snd (H̃ᶜʷ X' (suc n))))
                      (funExt⁻ (cong fst (sym (H̃ˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) Xsk (suc n)
                        {f = incl ∘ fst f' ∘ invEq (isCWSphere (suc n) .snd)} fbet))) (genHₙSⁿ n))
                      ((funExt⁻ (cong fst (sym (H̃ˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) Xsk (suc n)
                        {f = incl ∘ fst g' ∘ invEq (isCWSphere (suc n) .snd)} gbet))) (genHₙSⁿ n)))

         lem : (f : _) (fp : incl∙ Xsk x₀ ∘∙ f' ≡ f)
               (g : _) (gp : incl∙ Xsk x₀ ∘∙ g' ≡ g)
           → GoalTy f g
         lem = J> (J> main) -- J> (J> main)


  HurewiczHom : {n : ℕ} (X : CW ℓ-zero) (x : fst X) (conX : isConnected 2 (fst X))
              → GroupHom (π'Gr n (fst X , x)) (H̃ᶜʷ X (suc n))
  fst (HurewiczHom {n = n} X x conX) = HurewiczMap X x
  snd (HurewiczHom {n = n} X x conX) = makeIsGroupHom λ f g → HurewiczMapHom X x f g conX

HurewiczMapNat : {n : ℕ} (X Y : CW ℓ-zero) (x : fst X) (y : fst Y)
                    (g : (fst X , x) →∙ (fst Y , y))
    → H̃ᶜʷ→ {C = X} {D = Y} (suc n) (fst g) .fst ∘ HurewiczMap X x
    ≡ HurewiczMap Y y ∘ π'∘∙Hom n g .fst
HurewiczMapNat {n = n} X Y x y g =
  funExt (ST.elim (λ _ → isOfHLevelPath 2 (GroupStr.is-set (H̃ᶜʷ Y (suc n) .snd)) _ _)
    λ f → funExt⁻ (sym (cong fst (H̃ᶜʷ→comp
             {C = Sᶜʷ (suc n)} {D = X} {E = Y} (suc n) (fst g) (fst f))))
             (genHₙSⁿ n))

H̃ˢᵏᵉˡ-comm : ∀ {ℓ} {n : ℕ} {X : CWskel ℓ} (x y : H̃ˢᵏᵉˡ X (suc n) .fst)
  → GroupStr._·_ (H̃ˢᵏᵉˡ X (suc n) .snd) x y ≡ GroupStr._·_ (H̃ˢᵏᵉˡ X (suc n) .snd) y x
H̃ˢᵏᵉˡ-comm = SQ.elimProp2 (λ _ _ → GroupStr.is-set (H̃ˢᵏᵉˡ _ _ .snd) _ _)
  λ a b → cong [_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
    (funExt λ _ → +Comm _ _))

H̃ᶜʷ-comm : ∀ {ℓ} {n : ℕ} (X : CW ℓ) (x y : H̃ᶜʷ X (suc n) .fst)
  → GroupStr._·_ (H̃ᶜʷ X (suc n) .snd) x y ≡ GroupStr._·_ (H̃ᶜʷ X (suc n) .snd) y x
H̃ᶜʷ-comm {n = n} = uncurry λ X
  → PT.elim (λ _ → isPropΠ2 λ _ _ → GroupStr.is-set (H̃ᶜʷ (X , _) (suc n) .snd) _ _)
            λ x → H̃ˢᵏᵉˡ-comm

H̃ᶜʷAb : ∀ {ℓ} → CW ℓ → ℕ → AbGroup ℓ-zero
H̃ᶜʷAb X n = Group→AbGroup (H̃ᶜʷ X (suc n)) (H̃ᶜʷ-comm X)

HurewiczHomAb : (X : CW ℓ-zero) (x : fst X) (isC : isConnected 2 (fst X))
  (n : ℕ) → AbGroupHom (AbelianizationAbGroup (π'Gr n (fst X , x))) (H̃ᶜʷAb X n)
fst (HurewiczHomAb X x isC n) =
  Abi.rec _ (AbGroupStr.is-set (snd (H̃ᶜʷAb X n)))
            (HurewiczHom X x isC .fst)
            ish
  where
  ish : (a b c : _) → _
  ish a b c = IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _
            ∙ cong₂ (GroupStr._·_ (H̃ᶜʷ X (suc n) .snd)) refl
                (IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _
                ∙ AbGroupStr.+Comm (snd (H̃ᶜʷAb X n)) _ _
                ∙ sym (IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _))
            ∙ sym (IsGroupHom.pres· (HurewiczHom X x isC .snd) _ _)
snd (HurewiczHomAb X x isC n) =
  makeIsGroupHom (Abi.elimProp2 _ (λ _ _ → GroupStr.is-set (snd (H̃ᶜʷ X (suc n))) _ _)
    (IsGroupHom.pres· (HurewiczHom X x isC .snd)))


HurewiczMapCofibEquiv : ∀ {n m k : ℕ}
  → (α : (SphereBouquet∙ (suc n) (Fin m)) →∙ SphereBouquet∙ (suc n) (Fin k))
  → (isC : _)
  → isEquiv (fst (HurewiczHomAb (SphereBouquet/ᶜʷ (fst α)) (inl tt) isC n))
HurewiczMapCofibEquiv {n = n} {m} {k} α isC =
  Badoo! α (HurewiczHomAb (SphereBouquet/ᶜʷ (fst α)) (inl tt) isC n)
    λ w → (λ _ → H̃ˢᵏᵉˡ→ {C = Sˢᵏᵉˡ (suc n)} {D = SphereBouquet/ˢᵏᵉˡ (fst α)} (suc n)
                   (fst (isCWSphereBouquet/ (fst α) .snd)
                  ∘ preπSphereBouquet/Generator α w .fst
                  ∘ invEq (isCWSphere (suc n) .snd)) .fst (genHₙSⁿ n))
         ∙ funExt⁻ (cong fst (H̃ˢᵏᵉˡ→β (Sˢᵏᵉˡ (suc n)) (SphereBouquet/ˢᵏᵉˡ (fst α)) (suc n) {f = ff w}
                   (bst'' w) -- (bst w)
                   ))
                   (genHₙSⁿ n)
         ∙ cong [_] (Σ≡Prop (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → isSetℤ)) _ _)
                ((λ i x → sumFinℤ (λ a → degree (suc n)
               λ asd → pickPetal x (F1 n α RR QQ (BaOH≡' w (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) (F2 n α RR QQ a .fst asd) (~ i)))))
              ∙  funExt λ x → sumFin-choose _+_ 0 (λ _ → refl) +Comm
                 (λ a → degree (suc n)
                   λ s → pickPetal x (F1 n α RR QQ (BaOH n α w (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) RR QQ (F2 n α RR QQ a .fst s ))))
                 (ℤFinGenerator (fin→SphereBouquet/Cell (fst α) RR QQ w) x)
                 (F→ n RR)
                 (nonVanish n α _ _ x w)
                 λ x' q → ⊥.rec (www RR x' q)))
         {-
         cong [_] (Σ≡Prop (λ _ → isOfHLevelPathP' 1 (isSetΠ (λ _ → isSetℤ)) _ _)
             ((λ i x → sumFinℤ (λ a → degree (suc n)
               λ asd → pickPetal x (F1 n α RR QQ (BaOH≡ w (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) (F2 n α RR QQ a .fst asd) (~ i)))))
             ∙ funExt λ x → sumFin-choose _+_ 0 (λ _ → refl) +Comm
                 (λ a → degree (suc n)
                   λ s → pickPetal x (F1 n α RR QQ (BaOH n α w (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) RR QQ (F2 n α RR QQ a .fst s ))))
                 (ℤFinGenerator (fin→SphereBouquet/Cell (fst α) RR QQ w) x)
                 (F→ n RR)
                 (nonVanish n α _ _ x w)
                 λ x' q → ⊥.rec (www RR x' q)))
                 -}
  where

  F→ : (n : ℕ) (RR : _) → Fin (ScardGen (suc n) (suc n) (Trichotomyᵗ-suc RR))
  F→ n (lt x₁) = ⊥.rec (¬m<ᵗm x₁)
  F→ n (eq x₁) = fzero
  F→ n (gt x₁) = ⊥.rec (¬m<ᵗm x₁)

  www : (RR : _) (s : Fin (ScardGen (suc n) (suc n) (Trichotomyᵗ-suc RR))) → ¬ s ≡ F→ n RR → ⊥
  www (eq x) (zero , tt) s = s refl

  module _ (n : ℕ) (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k)) where
    F1 : (RR : _) (QQ : _) → _
    F1 RR QQ = BouquetFuns.CTB (suc n)
           (SphereBouquet/Card* m k (suc n) RR QQ)
           (SphereBouquet/α* m k (fst α) (suc n) RR QQ)
           (SphereBouquet/Eq* m k (suc n) (fst α) (Trichotomyᵗ-suc RR) RR QQ)

    F1* : (RR : _) (QQ : _) → _
    F1* RR QQ = Pushout→Bouquet (suc n)
           (SphereBouquet/Card* m k (suc n) RR QQ)
           (SphereBouquet/α* m k (fst α) (suc n) RR QQ)
           (SphereBouquet/Eq* m k (suc n) (fst α) (Trichotomyᵗ-suc RR) RR QQ)
           ∘ fst (SphereBouquet/Eq* m k (suc n) (fst α) (Trichotomyᵗ-suc RR) RR QQ)

    F1** : (RR : _) (QQ : _) → _
    F1** RR QQ = Pushout→Bouquet (suc n)
           (SphereBouquet/Card* m k (suc n) RR QQ)
           (SphereBouquet/α* m k (fst α) (suc n) RR QQ)
           (SphereBouquet/Eq* m k (suc n) (fst α) (Trichotomyᵗ-suc RR) RR QQ)

    F2 : (RR : _) (QQ : _) → _
    F2 RR QQ = preBTC (suc n)
                    (ScardGen (suc n) (suc n) (Trichotomyᵗ-suc RR))
                    (λ t → Sgen.Sfam∙ (suc n) n QQ)
                    (SαEqGen (suc n) (suc n) (Trichotomyᵗ-suc RR) QQ)

  RR = (Trichotomyᵗ-suc (n ≟ᵗ n))
  QQ = (Trichotomyᵗ-suc (n ≟ᵗ suc n))

  ff : (w : Fin k) → _
  ff w = (fst (isCWSphereBouquet/ (fst α) .snd)
                  ∘ preπSphereBouquet/Generator α w .fst
                  ∘ invEq (isCWSphere (suc n) .snd))

  F : {n : ℕ} (m k : _) (α : SphereBouquet∙ (suc n) (Fin m)
      →∙ SphereBouquet∙ (suc n) (Fin k))
      (w : Fin k) (r : _) (P : _)
      → Sgen.Sfam (suc n) r P → SphereBouquet/Fam* m k (fst α) r P
  F m k α w (suc r) (lt x) s = tt
  F m k α w (suc r) (eq x) s = inr (w , s)
  F m k α w (suc r) (gt x) s = inr (inr (w , s))

  FH : {n : ℕ} (m k : _) (α : SphereBouquet∙ (suc n) (Fin m)
      →∙ SphereBouquet∙ (suc n) (Fin k))
      (w : Fin k) (r : _) (P : _) (Q : _) (x : Sgen.Sfam (suc n) r Q)
      → invEq (SphereBouquet/Eq* m k r (fst α)
               (Trichotomyᵗ-suc P) P Q) (inl (F m k α w r Q x))
      ≡ F m k α w (suc r) (Trichotomyᵗ-suc P)
          (invEq (SαEqGen (suc n) r (Trichotomyᵗ-suc P) Q) (inl x))
  FH m k α w (suc r) (lt x₁) Q x = refl
  FH m k α w (suc r) (eq x₁) (lt x₂) x = push w
  FH m k α w (suc r) (eq x₁) (eq x₂) x = ⊥.rec (falseDichotomies.eq-eq (x₁ , x₂))
  FH m k α w (suc r) (eq x₁) (gt x₂) x =
    ⊥.rec (¬-suc-n<ᵗn (transport (λ i → x₁ (~ i) <ᵗ r) x₂))
  FH m k α w (suc r) (gt x₁) (lt x₂) x = ⊥.rec (¬squeeze (x₂ , x₁))
  FH m k α w (suc r) (gt x₁) (eq x₂) x = refl
  FH m k α w (suc r) (gt x₁) (gt x₂) x = refl

  module _ (n : ℕ) (α : SphereBouquet∙ (suc n) (Fin m) →∙ SphereBouquet∙ (suc n) (Fin k)) where
    BaOH : (w : _) (n' : Fin (suc (suc (suc n)))) (P : _) (Q : _)
         → cofib (invEq (SαEqGen (suc n) (fst n') (Trichotomyᵗ-suc P) Q) ∘ inl)
         → cofib (invEq (SphereBouquet/Eq* m k (fst n') (fst α) (Trichotomyᵗ-suc P) P Q) ∘ inl)
    BaOH w n' P Q (inl x) = inl tt
    BaOH w n' P Q (inr x) = inr (F m k α w (suc (fst n')) (Trichotomyᵗ-suc P) x)
    BaOH w n' P Q (push a i) =
       (push (F m k α w (fst n') Q a)
      ∙ λ i → inr (FH m k α w (fst n') P Q a i)) i

    module _ (n : ℕ) (w : Fin k) (x : _) (p : Path (S₊ (suc n)) (ptSn (suc n)) (ptSn (suc n))) where
      teGen : ¬ (fst w ≡ fst x)
        → (cong (pickPetal x) (push w) ∙∙
           (λ i → pickPetal x (inr (w , p i))) ∙∙
           cong (pickPetal x) (sym (push w))) ≡ refl
      teGen nope with (fst x ≟ᵗ fst w)
      ... | lt x = sym (rUnit refl)
      ... | eq x = ⊥.rec (nope (sym x))
      ... | gt x = sym (rUnit refl)

      teGen' : (fst w ≡ fst x)
        → (cong (pickPetal x) (push w) ∙∙
           (λ i → pickPetal x (inr (w , p i))) ∙∙
           cong (pickPetal x) (sym (push w))) ≡ p
      teGen' aye with (fst x ≟ᵗ fst w)
      ... | lt ine = ⊥.rec (¬m<ᵗm (subst (fst x <ᵗ_) aye ine))
      ... | eq x = sym (rUnit p)
      ... | gt ine = ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst x) aye ine))

  nonVanish : (n : ℕ) (α : _) (RR : _) (QQ : _) (x : Fin _) (w : _)
    → degree (suc n)
      (λ s →
         pickPetal x
         (F1 n α RR QQ
          (BaOH n α w (suc n , <ᵗ-trans <ᵗsucm <ᵗsucm) RR QQ
           (F2 n α RR QQ (F→ n RR) .fst s))))
      ≡ ℤFinGenerator (fin→SphereBouquet/Cell (fst α) RR QQ w) x
  nonVanish zero α (eq x₁) (lt x₂) x w =
    cong (degree (suc zero))
      (funExt (λ asd → cong (pickPetal x)
        λ i → F1 zero α (eq (isSetℕ _ _ x₁ refl i)) (lt x₂)
      (BaOH zero α w (1 , tt) (eq (isSetℕ _ _ x₁ refl i)) (lt x₂)
       (F2 zero α (eq (isSetℕ _ _ x₁ refl i)) (lt x₂) fzero .fst asd))))
     ∙ main MF refl
    where
    MF = pickPetal x
        ∘ F1 zero α (eq refl) (lt x₂)
        ∘ BaOH zero α w (1 , tt) (eq refl) (lt x₂)
        ∘ F2 zero α (eq refl) (lt x₂) fzero .fst

    F1B = F1 zero α (eq refl) (lt x₂) ∘ BaOH zero α w (1 , <ᵗ-trans <ᵗsucm <ᵗsucm) (eq refl) (lt x₂)
    l1 : cong (F2 zero α (eq refl) (lt x₂) fzero .fst) loop
      ≡ (push tt ∙∙ (λ i → inr (loop i)) ∙∙ sym (push tt))
    l1 = cong (λ p → push tt ∙∙ p ∙∙ sym (push tt))
              ((λ j i → inr (cong-∙ (invEq (SαEqGen 1 1 (Trichotomyᵗ-suc (eq refl)) (lt x₂)))
                      (push (fzero , false)) (sym (push (fzero , true))) j i))
              ∙ λ j i → inr (rUnit loop (~ j) i)
           )

    l2' : cong (fst (SphereBouquet/Eq* m k (suc zero) (fst α)
               (Trichotomyᵗ-suc (eq refl)) (eq refl) (lt x₂)))
               (λ i → inr (w , loop i))
        ≡ (push (w , false) ∙ sym (push (w , true)))
    l2' = (λ j i → transportRefl (SphereBouquet/EqBottomMain* m k (fst α) .fst (inr (w , loop i))) j)
        ∙ cong-∙ (λ K → ⋁→cofibFst (λ _ → Bool , true) (inr (w , K)))
                  (merid false) (sym (merid true))

    l2 : cong (pickPetal x ∘ F1 zero α (eq refl) (lt x₂))
              (λ i → inr (inr (w , loop i)))
            ≡ (cong (pickPetal x) (push w )
            ∙∙ (λ i → pickPetal x (inr (w , σSn 0 false i)))
            ∙∙ cong (pickPetal x) (sym (push w)))
    l2 = (cong (cong (pickPetal x))
          ((λ _ i → F1* zero α (eq refl) (lt x₂) (inr (w , loop i)))
          ∙ (λ j i → F1** zero α (eq refl) (lt x₂) (l2' j i))
          ∙ cong-∙ (F1** zero α (eq refl) (lt x₂))
                   (push (w , false)) (sym (push (w , true)))
          ∙ cong₂ _∙_ refl (sym (rUnit _))
          ∙ sym (GL.assoc _ _ _) ∙ sym (doubleCompPath≡compPath _ _ _))
          ∙ cong-∙∙ (pickPetal x) (push w) (λ i → (inr (w , σSn 0 false i))) (sym (push w))
          ∙ refl)

    lemp1 : cong (fst (SphereBouquet/Eq* m k (suc zero) (fst α)
               (Trichotomyᵗ-suc (eq refl)) (eq refl) (lt x₂)))
               (push w)
          ≡ refl
    lemp1 = sym (rUnit _)

    comm∙∙S¹ : ∀ (p q : ΩS¹) → p ∙∙ q ∙∙ sym p ≡ q
    comm∙∙S¹ p q = doubleCompPath≡compPath p q (sym p)
                 ∙ comm-ΩS¹ p _
                 ∙ sym (GL.assoc _ _ _)
                 ∙ cong (q ∙_) (lCancel p)
                 ∙ sym (rUnit q)


    lem : cong MF loop
     ≡ (cong (pickPetal x) (push w) ∙∙
       (λ i → pickPetal x (inr (w , σSn 0 false i))) ∙∙
       cong (pickPetal x) (sym (push w)))
    lem = cong (cong (pickPetal x ∘ F1B)) l1
     ∙ cong-∙∙ (pickPetal x ∘ F1B) (push tt) (λ i₁ → inr (loop i₁)) (sym (push tt))
     ∙ cong₃ _∙∙_∙∙_ refl
                     l2
                     refl
     ∙ comm∙∙S¹ _ _

    mainock : ¬ (fst w ≡ fst x) → (r : _) → MF r ≡ base
    mainock nope base = refl
    mainock nope (loop i) j = (lem ∙ teGen _ α zero w x (σS false) nope) j i

    mainockq : (fst w ≡ fst x) → (r : _) → MF r ≡ r
    mainockq aye base = refl
    mainockq aye (loop i) j = (lem ∙ teGen' _ α zero w x (σS false) aye) j i

    main : (MF' : _) → MF ≡ MF' → degree 1 MF' ≡ ℤFinGenerator w x
    main MF' p with (fst w ≟ᵗ fst x)
    ... | lt wa = cong (degree (suc zero))
                   (sym p ∙ funExt (λ d → mainock (λ s → ¬m<ᵗm (subst (_<ᵗ fst x) s wa)) d))
                 ∙ degreeConst (suc zero)
    ... | eq x = (cong (degree (suc zero)) (sym p)
               ∙ cong (degree 1) (funExt (mainockq x)))
               ∙ degreeIdfun (suc zero)
    ... | gt wa = cong (degree (suc zero))
                   (sym p ∙ funExt (λ d → mainock (λ s → ¬m<ᵗm (subst (fst x <ᵗ_) s wa)) d))
                 ∙ degreeConst (suc zero)

  nonVanish (suc n) α (eq x₁) (lt x₂) x w =
    cong (degree (suc (suc n)))
      (funExt (λ asd → cong (pickPetal x)
        λ i → F1 (suc n) α (eq (isSetℕ _ _ x₁ refl i)) (lt x₂)
      (BaOH (suc n) α w (suc (suc n) , <ᵗ-trans <ᵗsucm <ᵗsucm) (eq (isSetℕ _ _ x₁ refl i)) (lt x₂)
       (F2 (suc n) α (eq (isSetℕ _ _ x₁ refl i)) (lt x₂) fzero .fst asd))))
      ∙ TR.rec (isProp→isOfHLevelSuc n (isSetℤ _ _))
          (λ hyp → main hyp (discreteℕ _ _) unlock)
          (isConnectedPath _
            (isConnectedPath _ (sphereConnected (suc (suc n))) _ _)
             (cong (λ x₃ → pickPetal x (F1B x₃)) (push tt)) refl .fst)
    where
    MF = pickPetal x
        ∘ F1 (suc n) α (eq refl) (lt x₂)
        ∘ BaOH (suc n) α w (suc (suc n) , <ᵗ-trans <ᵗsucm <ᵗsucm) (eq refl) (lt x₂)
        ∘ F2 (suc n) α (eq refl) (lt x₂) fzero .fst

    F1B = F1 (suc n) α (eq refl) (lt x₂) ∘ BaOH (suc n) α w (suc (suc n) , <ᵗ-trans <ᵗsucm <ᵗsucm) (eq refl) (lt x₂)

    module _ (hyp : cong (λ x₃ → pickPetal x (F1B x₃)) (push tt) ≡ refl) where
      l1 : (a : _) → cong (F2 (suc n) α (eq refl) (lt x₂) fzero .fst) (merid a)
                   ≡ (push tt ∙∙ (λ i → inr (σS a i)) ∙∙ sym (push tt))
      l1 a = cong (λ p → push tt ∙∙ p ∙∙ sym (push tt))
               λ j i → inr ((cong-∙ (invEq
            (SαEqGen (suc (suc n)) (suc (suc n)) (Trichotomyᵗ-suc (eq refl))
             (lt x₂))) (push (fzero , a)) (sym (push (fzero , ptSn (suc n))))
           ∙ cong₂ _∙_ (cong merid (transportRefl a)) (cong (sym ∘ merid) (transportRefl (ptSn (suc n))))) j i)

      transportRefl-transportRefl : ∀ {ℓ} {A : Type ℓ} (x : A)
        → Square {A = A} (λ i → transportRefl (transportRefl x i) (~ i))
                          refl refl refl
      transportRefl-transportRefl x =
        (gen _ _ _ _ _ _ _ _
          (λ i j → transportRefl (transportRefl x i) j)
        ∙ rCancel _)
       where
       gen : ∀ {ℓ} {A : Type ℓ} (x y : A) (p : x ≡ y)
         (z : A) (l : x ≡ z) (w : A) (r : y ≡ w) (q : z ≡ w)
         (P : Square p q l r) → (λ i → P i (~ i)) ≡ r ∙ sym q
       gen x = J> (J> (J> (J> rUnit refl)))

      l2 : (a : _) → cong (F1* (suc n) α (eq refl) (lt x₂)) (λ i → inr (w , merid a i))
                   ≡ (push w)
                   ∙∙ (λ i → (inr (w , σS a i)))
                   ∙∙ λ i → (inr (transportRefl w (~ i) , north))
      l2 a =
        (cong (cong (F1** (suc n) α (eq refl) (lt x₂)))
                   (λ j i → transport refl (push (w , a) i))
                 ∙ cong (cong (F1** (suc n) α (eq refl) (lt x₂)))
                   (cong₂ _∙_ refl refl)
                 ∙ cong-∙ (F1** (suc n) α (eq refl) (lt x₂)) _ _
                 ∙ cong₃ _∙∙_∙∙_ refl
                   (cong₂ _∙_ refl refl)
                   refl
                 ∙ cong₂ _∙_ refl
                   (λ j i → inr (transportRefl-transportRefl w j i , north))
                 ∙ sym (GL.assoc _ _ _)

                 ∙ (λ j → push (transportRefl w j)
                   ∙ (λ i → inr (transportRefl w j
                          , σS (transportRefl a j) i))
                   ∙ λ i → inr (transp (λ i₁ → Fin k) (j ∧ ~ i) w , north))
                   ∙ sym (doubleCompPath≡compPath _ _ _))

      pathLem : ∀ {ℓ} {A : Type ℓ} {x : A}
        (y : A) (p : x ≡ y) (q : y ≡ y) (z : A) (r : y ≡ z)
        (q2 : y ≡ y) → refl ≡ q2
          → (p ∙∙ q ∙∙ r) ∙ (sym r ∙∙ sym q2 ∙∙ sym p)
          ≡ (p ∙∙ q ∙∙ sym p)
      pathLem = J> λ q → J> (J> cong₂ _∙_ (sym (rUnit q)) (sym (rUnit refl)))

      maiin : (a : _) → cong MF (merid a)
        ≡ cong (pickPetal x) (push w)
        ∙∙ cong (pickPetal x) (λ i → inr (w , σS a i))
        ∙∙ cong (pickPetal x) (sym (push w))
      maiin a = cong (cong (pickPetal x ∘ F1B)) (l1 a)
              ∙ cong-∙∙ (pickPetal x ∘ F1B) _ _ _
              ∙ cong₃ _∙∙_∙∙_
                  hyp
                  (cong (cong (pickPetal x))
                    (cong-∙ (λ z → F1B (inr z))
                      (merid a) (sym (merid (ptSn (suc n))))
                  ∙ cong₂ _∙_ (l2 a) (cong sym (l2 (ptSn (suc n))))
                  ∙ pathLem _ (push w) (λ i → inr (w , σS a i)) _
                                       (λ i → inr (transportRefl w (~ i) , north))
                                       (λ i → inr (w , σS (ptSn (suc n)) i))
                                       λ j i → inr (w , rCancel (merid (ptSn (suc n))) (~ j) i))
                  ∙ cong-∙∙ (pickPetal x) _ _ _)
                  (cong sym hyp)
              ∙ sym (rUnit _)




      mainock : ¬ (fst w ≡ fst x) → (r : _) → MF r ≡ north
      mainock nope north = refl
      mainock nope south = refl
      mainock nope (merid a i) j = (maiin a ∙ teGen _ α (suc n) w x (σS a) nope) j i

      mainockq : (fst w ≡ fst x) → (r : _) → MF r ≡ r
      mainockq aye north = refl
      mainockq aye south = merid (ptSn (suc n))
      mainockq aye (merid a i) j =
        ((maiin a ∙ teGen' _ α (suc n) w x (σS a) aye)
        ◁ symP (compPath-filler (merid a) (sym (merid (ptSn (suc n)))))) j i

      main : Dec (fst w ≡ fst x) → (l : _)
                        → degree (suc (suc n)) MF ≡ ℤFinGenerator* w x l
      main (yes p₁) l =
        cong (degree (suc (suc n))) (funExt (mainockq p₁))
        ∙ degreeIdfun (suc (suc n))
        ∙ sym (mainockℤ' w x l p₁)
      main (no ¬p) l  =
        cong (degree (suc (suc n))) (funExt (mainock ¬p))
        ∙ degreeConst (suc (suc n))
        ∙ sym (mainockℤ w x l ¬p)

  nonVanish n α (eq x₁) (eq x₂) x w =
    ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) x₂ <ᵗsucm))
  nonVanish n α (eq x₁) (gt x₂) x w =
    ⊥.rec (¬-suc-n<ᵗn x₂)
  nonVanish n α (gt x₁) QQ x w = ⊥.rec (¬m<ᵗm x₁)


  bst : (w : _) → finCellApprox (Sˢᵏᵉˡ (suc n)) (SphereBouquet/ˢᵏᵉˡ (fst α))
                      (ff w) (suc (suc (suc n)))
  FinSequenceMap.fmap (fst (bst w)) (r , s) =
    F m k α w r (r ≟ᵗ suc (suc n))
  FinSequenceMap.fcomm (fst (bst w)) (r , s) =
    FH m k α w r _ _
  snd (bst w) =
    →FinSeqColimHomotopy _ _ λ s → cong (incl {n = suc (suc (suc n))})
      (aoh _ s
      ∙ cong (SphereBouquet/FamTopElement* m k (suc (suc (suc n))) (fst α)
              <ᵗsucm (suc (suc (suc n)) ≟ᵗ suc (suc n)) .fst
             ∘ preπSphereBouquet/Generator α w .fst) (sym (baoh s)))
    where
    BO : (P : _) → Sgen.Sfam (suc n) (suc (suc (suc n))) P → S₊ (suc n)
    BO (lt x₁) x = ptSn _
    BO (eq x₁) x = x
    BO (gt x₁) x = x

    aoh : (P : _) (s : _) → F m k α w (suc (suc (suc n))) P s
      ≡
      SphereBouquet/FamTopElement* m k (suc (suc (suc n))) (fst α) <ᵗsucm P .fst
      (preπSphereBouquet/Generator α w .fst
       (invEq
        (SfamGenTopElement (suc n) (suc (suc (suc n)))
         (<ᵗ-trans <ᵗsucm <ᵗsucm) P)
        s))
    aoh (lt x) = λ _ → refl
    aoh (eq x) = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) (λ i → predℕ (x (~ i))) <ᵗsucm))
    aoh (gt x) = λ _ → refl

    baoh : (x : Sfam (suc n) (suc (suc (suc n))))
      → invEq (isCWSphere (suc n) .snd) (incl x)
      ≡ invEq (SfamGenTopElement (suc n) (suc (suc (suc n)))
        (<ᵗ-trans {n = n} {m = suc n} {k = suc (suc n)} <ᵗsucm <ᵗsucm)
        (suc (suc (suc n)) ≟ᵗ suc (suc n))) x -- BO _ x
    baoh x = cong (invEq (isCWSphere (suc n) .snd)) maa
           ∙ retEq (isCWSphere (suc n) .snd) _
      where
      maa : incl x
        ≡ fst (isCWSphere (suc n) .snd) (invEq (SfamGenTopElement (suc n) (suc (suc (suc n)))
             (<ᵗ-trans {n = n} {m = suc n} {k = suc (suc n)} <ᵗsucm <ᵗsucm)
             (suc (suc (suc n)) ≟ᵗ suc (suc n))) x)
      maa = cong incl (maGen _ _ x) ∙ sym (push _)
        where
        maGen : (P : _) (Q : _) (x : Sgen.Sfam (suc n) (suc (suc (suc n))) P)
          → x ≡ invEq (SαEqGen (suc n) (suc (suc n)) P Q)
                   (inl (fst (SfamGenTopElement (suc n) (suc (suc n)) <ᵗsucm Q)
                     (invEq (SfamGenTopElement (suc n) (suc (suc (suc n)))
                       (<ᵗ-trans <ᵗsucm <ᵗsucm) P) x)))
        maGen P (lt x₁) x = ⊥.rec (¬squeeze (x₁ , <ᵗsucm))
        maGen (lt x₂) (eq x₁) x = refl
        maGen (eq x₂) (eq x₁) x =
          ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc n) (cong (predℕ ∘ predℕ) (sym x₂)) <ᵗsucm))
        maGen (gt x₂) (eq x₁) x = refl
        maGen P (gt x₁) x = ⊥.rec (¬m<ᵗm x₁)

  BaOH≡ : (w : _) (n' : Fin (suc (suc (suc n)))) (x : _)
    → BaOH n α w n' (fst n' ≟ᵗ suc n) (fst n' ≟ᵗ suc (suc n)) x
    ≡ prefunctoriality.fn+1/fn (suc (suc (suc n))) (fst (bst w)) n' x
  BaOH≡ w n' (inl x) = refl
  BaOH≡ w n' (inr x) = refl
  BaOH≡ w n' (push a i) = refl


  bst'' : (w : _) → finCellApprox (Sˢᵏᵉˡ (suc n)) (SphereBouquet/ˢᵏᵉˡ (fst α))
                      (ff w) (suc (suc (suc (suc n))))
  FinSequenceMap.fmap (fst (bst'' w)) m' x = F m k α w (fst m') (fst m' ≟ᵗ suc (suc n)) x
  FinSequenceMap.fcomm (fst (bst'' w)) n x = FH m k α w (fst n) _ _ x
  snd (bst'' w) = →FinSeqColimHomotopy _ _
    λ s → ((cong (incl {n = suc (suc (suc (suc n)))})
             (cong (F m k α w (suc (suc (suc (suc n))))
      (Trichotomyᵗ-suc (Trichotomyᵗ-suc (suc (suc n) ≟ᵗ n)))) (sym (secEq (_ , SˢᵏᵉˡConverges (suc n) 1) s))
             ∙ mainL (Trichotomyᵗ-suc (Trichotomyᵗ-suc (suc (suc n) ≟ᵗ n))) (suc (suc (suc n)) ≟ᵗ suc n) (suc (suc (suc n)) ≟ᵗ suc (suc n))
               (invEq (invEq (SαEq (suc n) (1 +ℕ suc (suc n))) ∘ inl , SˢᵏᵉˡConverges (suc n) 1) s))
        ∙ sym (push _))
        ∙ funExt⁻ (snd (bst w)) (fincl (suc (suc (suc n)) , <ᵗsucm) (invEq
                              (invEq (SαEq (suc n) (1 +ℕ suc (suc n))) ∘ inl ,
                               SˢᵏᵉˡConverges (suc n) 1) s))
        ∙ cong (ff w) (push (invEq
                              (invEq (SαEq (suc n) (1 +ℕ suc (suc n))) ∘ inl ,
                               SˢᵏᵉˡConverges (suc n) 1)
                              s)))
          ∙ λ i → ff w (incl {n = suc (suc (suc (suc n)))} (secEq (_ , SˢᵏᵉˡConverges (suc n) 1) s i))
    where
    mainL : (P : _) (Q : _) (R : _)
      (s : _) → F m k α w (suc (suc (suc (suc n)))) P (invEq (SαEqGen (suc n) (suc (suc (suc n))) P R) (inl s))
          ≡ invEq (SphereBouquet/Eq* m k (suc (suc (suc n))) (fst α) P
                                     Q R) (inl (F m k α w (suc (suc (suc n))) R s))
    mainL (lt x) Q R s = ⊥.rec (¬-suc-n<ᵗn (<ᵗ-trans x <ᵗsucm))
    mainL (eq x) Q R s = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) (sym (cong (predℕ ∘ predℕ) x)) (<ᵗ-trans <ᵗsucm <ᵗsucm)))
    mainL (gt x) Q (lt x₁) s = ⊥.rec (¬-suc-n<ᵗn x₁)
    mainL (gt x) Q (eq x₁) s = ⊥.rec (⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc n)) (sym (cong predℕ x₁)) <ᵗsucm)))
    mainL (gt x) (lt x₂) (gt x₁) s = ⊥.rec (¬m<ᵗm (<ᵗ-trans x x₂))
    mainL (gt x) (eq x₂) (gt x₁) s = ⊥.rec (¬m<ᵗm (subst (_<ᵗ suc (suc (suc n))) (λ i → x₂ (~ i)) x))
    mainL (gt x) (gt x₂) (gt x₁) s = refl

  BaOH≡' : (w : _) (n' : Fin (suc (suc (suc n)))) (x : _)
    → BaOH n α w n' (fst n' ≟ᵗ suc n) (fst n' ≟ᵗ suc (suc n)) x
    ≡ prefunctoriality.fn+1/fn (suc (suc (suc (suc n)))) (fst (bst'' w)) (injectSuc n') x
  BaOH≡' w n' (inl x) = refl
  BaOH≡' w n' (inr x) = refl
  BaOH≡' w n' (push a i) = refl


subCWExplicit : ∀ {ℓ} (n : ℕ) → CWexplicit ℓ → CWexplicit ℓ
fst (subCWExplicit n (X , Xsk , e)) = Xsk .fst n
fst (snd (subCWExplicit n (X , Xsk , e))) = subComplex Xsk n
snd (snd (subCWExplicit n (X , Xsk , e))) = isoToEquiv (realiseSubComplex n Xsk)


CWexplicit→CW : ∀ {ℓ} → CWexplicit ℓ → CW ℓ
CWexplicit→CW C = fst C , ∣ snd C ∣₁

subCW : ∀ {ℓ} (n : ℕ) → CWexplicit ℓ → CW ℓ
subCW n X = CWexplicit→CW (subCWExplicit n X)

ConnectedCW : (ℓ : Level) (n : ℕ) → Type (ℓ-suc ℓ)
ConnectedCW ℓ n = Σ[ X ∈ Type ℓ ] isConnectedCW n X

ConnectedCW→CWexplicit : ∀ {ℓ} {n : ℕ} → ConnectedCW ℓ n → CWexplicit ℓ
fst (ConnectedCW→CWexplicit (X , p , con)) = X
fst (fst (snd (ConnectedCW→CWexplicit (X , (Xsk , _ , _) , con)))) = Xsk
snd (fst (snd (ConnectedCW→CWexplicit (X , (Xsk , p , _) , con)))) = p
snd (snd (ConnectedCW→CWexplicit (X , (Xsk , _ , _) , con))) = invEquiv con

ConnectedCW→CW : ∀ {ℓ} {n : ℕ} → ConnectedCW ℓ n → CW ℓ
ConnectedCW→CW X = CWexplicit→CW (ConnectedCW→CWexplicit X)


PreHurewiczLemma : (n : ℕ) (X : CWexplicit ℓ-zero) (conX : isConnected 2 (fst X))
  → ((l : _) (str : _) (t : _)
    → isEquiv (HurewiczHomAb (X .snd .fst .fst (suc (suc (suc n))) , str) l t n .fst))
  → (x : fst X) → isEquiv (HurewiczHomAb  (fst X , ∣ snd X ∣₁) x conX n .fst)
PreHurewiczLemma n X conX ind' x =
  TR.rec (isPropIsEquiv _)
    (λ t → subst isEquiv (funExt (help t)) (altEquiv t .fst .snd))
    (isConnected-CW↪∞ (suc zero) (fst (snd X)) (fst (snd (snd X)) x) .fst)
  where
  SubX : CW ℓ-zero
  SubX = ((realise (subComplex (fst (snd X)) (suc (suc (suc n)))))
                      , ∣ (subComplex (fst (snd X)) (suc (suc (suc n)))) , (idEquiv _) ∣₁)

  module _ (t : fiber (CW↪∞ (fst (snd X)) (suc zero)) (fst (snd (snd X)) x)) where

    x' : fst SubX
    x' = Iso.fun (realiseSubComplex (suc (suc (suc n))) (fst (snd X)))
                 (CWskel∙ (fst (snd X)) (fst t) (suc (suc n)))

    p' : invEq (snd (snd X)) (incl (fst t)) ≡ x
    p' = cong (invEq (snd (snd X))) (snd t) ∙ retEq (snd (snd X)) x

    F₃ : _ →∙ _
    fst F₃ = Iso.inv (realiseSubComplex (suc (suc (suc n))) (fst (snd X)))
    snd F₃ = Iso.leftInv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))) _

    F∙ : (fst SubX , x') →∙ (fst X , x)
    F∙ = (invEq (snd (snd X)) , p')
      ∘∙ (incl∙ (fst (snd X)) (fst t)
      ∘∙ F₃)

    isConnF∙ : isConnectedFun (suc (suc (suc n))) (fst F∙)
    isConnF∙ = isConnectedComp (invEq (snd (snd X))) _ (suc (suc (suc n)))
      (isEquiv→isConnected _ (snd (invEquiv (snd (snd X)))) _)
      (isConnectedComp incl (F₃ .fst) (suc (suc (suc n)))
        (isConnected-CW↪∞ (suc (suc (suc n))) _)
        (isEquiv→isConnected _
          (isoToIsEquiv (invIso (realiseSubComplex (suc (suc (suc n))) (fst (snd X))))) _))

    conS' : isConnected 2 (fst (fst (snd X)) (suc (suc (suc n))))
    conS' = connectedFunPresConnected 2 (subst (isConnected 2) (ua (snd X .snd)) conX)
              λ b →  isConnectedSubtr' (suc n) 2 (isConnected-CW↪∞ (suc (suc (suc n))) (fst (snd X)) b)

    conS : isConnected 2 (fst SubX)
    conS = subst (isConnected 2) (isoToPath (realiseSubComplex (suc (suc (suc n))) (fst (snd X))))
            conS'

    H = HurewiczHomAb SubX x' conS n

    isEqH : isEquiv (fst H)
    isEqH = transport (λ i → isEquiv (fst (HurewiczHomAb (h i .fst) (h i .snd .fst) (h i .snd .snd) n)))
                      (ind' (CWskel∙ (fst (snd X)) (fst t) (suc (suc n)))
                       ∣ subComplex (fst (snd X)) (suc (suc (suc n)))
                       , isoToEquiv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))) ∣₁
                      conS')
      where
      h : Path (Σ[ X ∈ CW ℓ-zero ] (Σ[ x ∈ fst X ] isConnected 2 (fst X)))
               ((_ , ∣ subComplex (fst (snd X)) (suc (suc (suc n)))
                       , isoToEquiv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))) ∣₁)
               , ((CWskel∙ (fst (snd X)) (fst t) (suc (suc n))) , conS'))
               (SubX , (x' , conS))
      h = ΣPathP ((Σ≡Prop (λ _ → squash₁)
                 (isoToPath (realiseSubComplex (suc (suc (suc n))) (fst (snd X)))))
               , (ΣPathPProp (λ _ → isPropIsContr) (toPathP (cong incl
                 (transportRefl _)))))

    altEquiv : AbGroupEquiv (AbelianizationAbGroup (π'Gr n (fst X , x)))
                            ((H̃ᶜʷAb (fst X , ∣ snd X ∣₁) n))
    altEquiv =
      compGroupEquiv
        (invGroupEquiv (connected→Abπ'Equiv n F∙ isConnF∙))
         (compGroupEquiv ((fst H , isEqH) , snd H)
           (subComplexHomologyEquiv (fst (snd X)) n (suc (suc (suc n))) <ᵗsucm))

    help : (a : _) → altEquiv .fst .fst a ≡ HurewiczHomAb (fst X , ∣ snd X ∣₁) x conX n .fst a
    help = Abi.elimProp _ (λ _ → squash/ _ _)
      (λ f → better _
        ∙ cong (HurewiczHomAb (fst X , ∣ snd X ∣₁) x conX n .fst)
           (secEq (fst (connected→Abπ'Equiv n F∙ isConnF∙)) (η f)))
      where
      better : (t : _)
        → H̃ᶜʷ→ {C = subCW (suc (suc (suc n))) X}
                 {D = realise (fst (snd X)) , ∣ (fst (snd X)) , (idEquiv _) ∣₁} (suc n) incl
                 .fst (HurewiczHomAb SubX x' conS n .fst (η t))
          ≡ HurewiczHomAb (fst X , ∣ snd X ∣₁) x conX n .fst (fst (fst (connected→Abπ'Equiv n F∙ isConnF∙)) (η t))
      better = ST.elim (λ _ → isProp→isSet (squash/ _ _))
        λ g → funExt⁻ (cong fst
            (sym (H̃ᶜʷ→comp {C = Sᶜʷ (suc n)}
                           {D = SubX}
                           {E = realise (fst (snd X))
                              , ∣ (fst (snd X)) , (idEquiv _) ∣₁}
                  (suc n) (incl
                  ∘ Iso.inv (realiseSubComplex (suc (suc (suc n))) (fst (snd X))))
                  (fst g))))
                  (genHₙSⁿ n)
             ∙ λ i → H̃ᶜʷ→ {C = Sᶜʷ (suc n)}
                        {D = realise (fst (snd X))
                           , ∣ (fst (snd X)) , (idEquiv _) ∣₁} (suc n)
                           (λ z → secEq (snd (snd X)) (incl (F₃ .fst (fst g z))) (~ i))
                           .fst (genHₙSⁿ n)



HurewiczTheorem : (n : ℕ) (X : CW ℓ-zero) (conX : isConnected (suc (suc n)) (fst X)) (x : _)
  → isEquiv (HurewiczHomAb X x (isConnectedSubtr' n 2 conX) n .fst)
HurewiczTheorem n = uncurry λ X → PT.elim (λ _ → isPropΠ2  λ _ _ → isPropIsEquiv _)
  λ cw isc → PT.rec (isPropΠ (λ _ → isPropIsEquiv _))
    (λ cw' x → E X cw cw' isc x)
    (makeConnectedCW n cw isc)
  where
  isEqTransport : (cw1 cw2 : CW ℓ-zero) (P : cw1 ≡ cw2)
    (con1 : isConnected 2 (fst cw1)) (con2 : isConnected 2 (fst cw2))
    (x' : fst cw1) (x : fst cw2) (PP : PathP (λ i → fst (P i)) x' x)
    → isEquiv (HurewiczHomAb cw1 x' con1 n .fst)
    → isEquiv (HurewiczHomAb cw2 x con2 n .fst)
  isEqTransport cw1 = J> λ con1 con2 x'
    → J> subst (λ c → isEquiv (HurewiczHomAb cw1 x' c n .fst)) (isPropIsContr _ _)

  HA : (X : _) (cw cw' : _) → Path (CW ℓ-zero) ((X , ∣ cw ∣₁)) (X , ∣ cw' ∣₁)
  HA = λ X cw cw' → Σ≡Prop (λ _ → squash₁) refl

  e1 : (n m : ℕ) (l : m <ᵗ suc n) (X : Type) (cwX : isConnectedCW n X)
    → isContr (fst (fst cwX) (suc m))
  e1 n zero l X cwX =
    subst isContr (cong Fin (sym ((snd (fst cwX)) .snd .fst))
                  ∙ sym (ua (CW₁-discrete (fst (fst cwX)
                                        , fst (snd (fst cwX))))))
         (inhProp→isContr fzero isPropFin1)
  e1 n (suc m) l X cwX =
    subst isContr
      (ua (compEquiv (isoToEquiv (PushoutEmptyFam
        (¬Fin0 ∘ subst Fin (snd (fst cwX) .snd .snd m l) ∘ fst)
        (¬Fin0 ∘ subst Fin (snd (fst cwX) .snd .snd m l))))
        (invEquiv (snd (snd (snd (fst (snd (fst cwX))))) (suc m)))))
      (e1 n m (<ᵗ-trans l <ᵗsucm) X cwX)

  e2 : (n : ℕ) (X : Type) (cwX : isConnectedCW n X)
    → fst (fst cwX) (suc (suc n))
    ≃ SphereBouquet (suc n) (Fin (fst (fst (snd (fst cwX))) (suc n)))
  e2 n X cwX =
    compEquiv
      (snd (snd (snd (fst (snd (fst cwX))))) (suc n))
      (compEquiv
       (pushoutEquiv _ _ _ fst
         (idEquiv _)
         (isContr→≃Unit (e1 n n <ᵗsucm X cwX))
         (idEquiv _)
         (λ _ _ → tt)
         (λ i x → fst x))
       (compEquiv (isoToEquiv (Iso-cofibFst-⋁ (λ A → S₊∙ n)))
       (pushoutEquiv _ _ _ _ (idEquiv _) (idEquiv _)
         (Σ-cong-equiv-snd (λ _ → isoToEquiv (invIso (IsoSucSphereSusp n))))
         (λ _ _ → tt) (λ i x → x , IsoSucSphereSusp∙ n i))))

  e3 : (n : ℕ) (X : Type) (cwX : isConnectedCW n X) (str : _)
    → ∃[ α ∈ SphereBouquet∙ (suc n) (Fin (fst (fst (snd (fst cwX))) (suc (suc n))))
         →∙ SphereBouquet∙ (suc n) (Fin (fst (fst (snd (fst cwX))) (suc n))) ]
         ((fst cwX .fst (suc (suc (suc n)))) , str) ≡ SphereBouquet/ᶜʷ  (fst α)
  e3 n X cwX str = PT.rec squash₁
    (λ {(x , ptz , t) → ∣ F x ptz t , Σ≡Prop (λ _ → squash₁) (isoToPath (e3' x ptz t)) ∣₁})
    EX
    where
    open import Cubical.Axiom.Choice
    CON : isConnected 2 (fst (fst cwX) (suc (suc n)))
    CON = subst (isConnected 2) (ua (invEquiv (e2 n X cwX)))
            (isConnectedSubtr' n 2 isConnectedSphereBouquet')

    EX : ∃[ x ∈ fst (fst cwX) (suc (suc n)) ]
          (((a : Fin (fst (fst (snd (fst cwX))) (suc (suc n))))
         → x ≡ fst (snd (fst (snd (fst cwX)))) (suc (suc n))
                 (a , ptSn (suc n)))
         × (fst (e2 n X cwX) x ≡ inl tt))
    EX = TR.rec (isProp→isSet squash₁)
      (λ x₀ → TR.rec squash₁
        (λ pts → TR.rec squash₁ (λ F → ∣ x₀ , F , pts ∣₁)
          (invEq (_ , InductiveFinSatAC 1 (fst (fst (snd (fst cwX))) (suc (suc n))) _)
                λ a → isConnectedPath 1 CON _ _ .fst))
        (isConnectedPath 1 (isConnectedSubtr' n 2 isConnectedSphereBouquet')
          (fst (e2 n X cwX) x₀) (inl tt) .fst))
      (fst CON)

    module _ (x : fst (fst cwX) (suc (suc n)))
             (pts : (a : Fin (fst (fst (snd (fst cwX))) (suc (suc n))))
                  → x ≡ fst (snd (fst (snd (fst cwX)))) (suc (suc n)) (a , ptSn (suc n)))
             (ptd : fst (e2 n X cwX) x ≡ inl tt) where
      F' : SphereBouquet (suc n) (Fin (fst (fst (snd (fst cwX))) (suc (suc n))))
        → fst (fst cwX) (suc (suc n))
      F' (inl tt) = x
      F' (inr x) = fst (snd (fst (snd (fst cwX)))) (suc (suc n)) x
      F' (push a i) = pts a i

      F : SphereBouquet∙ (suc n) (Fin (fst (fst (snd (fst cwX))) (suc (suc n))))
       →∙ SphereBouquet∙ (suc n) (Fin (fst (fst (snd (fst cwX))) (suc n)))
      fst F = fst (e2 n X cwX) ∘ F'
      snd F = ptd

      e3' : Iso (fst (fst cwX) (suc (suc (suc n)))) (cofib (fst F))
      e3' =
        compIso (equivToIso (compEquiv
          (snd (snd (snd (fst (snd (fst cwX))))) (suc (suc n)))
          (pushoutEquiv _ _ _ _ (idEquiv _) (e2 n X cwX) (idEquiv _)
            (λ i x → fst F (inr x))
            (λ i x → fst x))))
        (⋁-cofib-Iso (SphereBouquet∙ (suc n)
                       (Fin (fst (fst (snd (fst cwX))) (suc n)))) F)

  module _ (X : Type) (cw : isCW X) (cw' : isConnectedCW n X)
           (isc : isConnected (suc (suc n)) X) (x : X) where
    E : isEquiv (HurewiczHomAb (X , ∣ cw ∣₁) x (isConnectedSubtr' n 2 isc) n .fst)
    E = isEqTransport (X , ∣ (fst cw' .fst , fst cw' .snd .fst)
                      , invEquiv (snd cw') ∣₁)
                      (X , ∣ cw ∣₁)
          (Σ≡Prop (λ _ → squash₁) refl)
          (isConnectedSubtr' n 2 isc)
          (isConnectedSubtr' n 2 isc) x x refl
          (PreHurewiczLemma n (X , (fst cw' .fst , fst cw' .snd .fst) , invEquiv (snd cw'))
            (isConnectedSubtr' n 2 isc)
            (λ l str con' → PT.rec (isPropIsEquiv _)
            (λ {(α , e) → TR.rec (isPropIsEquiv _)
              (λ linl → isEqTransport _ (fst cw' .fst (suc (suc (suc n))) , str) (sym e)
                              (subst (isConnected 2) (cong fst e) con')
                              con'
                              (inl tt) -- (transport (cong fst e) l)
                              l
                              (toPathP (sym linl))
                              (HurewiczMapCofibEquiv α (subst (isConnected 2) (λ i → fst (e i)) con')))
              (isConnectedPath 1 con' l (transport (sym (cong fst e)) (inl tt)) .fst)})
                (e3 n X cw' str)) x)
