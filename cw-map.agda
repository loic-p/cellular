-- Obtaining a chain map from a cellular map

{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool hiding (_≟_ ; isProp≤)
open import Cubical.Data.CW
open import Cubical.Data.CW.ChainComplex
open import Cubical.Data.CW.Map

open import Cubical.Data.Sequence
open import Cubical.Data.FinSequence

open import Cubical.HITs.Sn
open import Cubical.HITs.Sn.Degree
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.SphereBouquet
open import Cubical.HITs.SphereBouquet.Degree

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms

open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup

open import Cubical.Algebra.ChainComplex


open import cw-chain-complex


module cw-map where

private
  variable
    ℓ ℓ' ℓ'' : Level
    C D E : CWskel ℓ

-- A cellular map between two CW complexes
-- A cellMap from C to D is a family of maps Cₙ → Dₙ that commute with the inclusions Xₙ ↪ Xₙ₊₁
-- realiseSeq

-- open CCℕ
-- From a cellMap to a family of maps between free abelian groups
module finprefunctoriality (m : ℕ) (f : finCellMap m C D) (n' : Fin m) where
  open FinSequenceMap
  open CWskel-fields

  n = fst n'

  fn+1/fn : cofibCW (fst n') C → cofibCW (fst n') D
  fn+1/fn (inl tt) = inl tt
  fn+1/fn (inr x) = inr (f .fmap (fsuc n') x)
  fn+1/fn (push x i) = (push (f .fmap (injectSuc n') x) ∙ (cong inr (f .fcomm n' x))) i

  bouquetFunct : SphereBouquet n (Fin (card C n)) → SphereBouquet n (Fin (card D n))
  bouquetFunct = (Iso.fun (BouquetIso-gen n (card D n) (α D n) (e D n)))
                 ∘ fn+1/fn
                 ∘ (Iso.inv (BouquetIso-gen n (card C n) (α C n) (e C n)))

  chainFunct : AbGroupHom (ℤ[A C ] n) (ℤ[A D ] n)
  chainFunct = bouquetDegree bouquetFunct

module prefunctoriality (f : cellMap C D) (n : ℕ) where
  open SequenceMap
  open CWskel-fields

  fn+1/fn : cofibCW n C → cofibCW n D
  fn+1/fn (inl tt) = inl tt
  fn+1/fn (inr x) = inr (f .map (suc n) x)
  fn+1/fn (push x i) = (push (f .map n x) ∙ (cong inr (f .comm n x))) i

  bouquetFunct : SphereBouquet n (Fin (card C n)) → SphereBouquet n (Fin (card D n))
  bouquetFunct = (Iso.fun (BouquetIso-gen n (card D n) (α D n) (e D n)))
                 ∘ fn+1/fn
                 ∘ (Iso.inv (BouquetIso-gen n (card C n) (α C n) (e C n)))

  chainFunct : AbGroupHom (ℤ[A C ] n) (ℤ[A D ] n)
  chainFunct = bouquetDegree bouquetFunct

module fin-one (m : ℕ) (C : CWskel ℓ) (n' : Fin m) where
  open finprefunctoriality m (idFinCellMap m C) n'
  open SequenceMap
  open CWskel-fields

  fn+1/fn-id : fn+1/fn ≡ idfun _
  fn+1/fn-id = funExt
    λ { (inl x) → refl
      ; (inr x) → refl
      ; (push a i) j → rUnit (push a) (~ j) i}

  bouquetFunct-id : bouquetFunct ≡ idfun _
  bouquetFunct-id =
    cong (λ f → Iso.fun (BouquetIso-gen n (card C n) (α C n) (e C n))
                ∘ f
                ∘ Iso.inv (BouquetIso-gen n (card C n) (α C n) (e C n)))
         fn+1/fn-id
    ∙ funExt (Iso.rightInv (BouquetIso-gen n (card C n) (α C n) (e C n)))

  chainFunct-id : chainFunct ≡ idGroupHom
  chainFunct-id = cong bouquetDegree bouquetFunct-id ∙ bouquetDegreeId


module _ (C : CWskel ℓ) (n : ℕ) where
  open prefunctoriality (idCellMap C) n
  open SequenceMap
  open CWskel-fields

  fn+1/fn-id : fn+1/fn ≡ idfun _
  fn+1/fn-id = funExt
    λ { (inl x) → refl
      ; (inr x) → refl
      ; (push a i) j → rUnit (push a) (~ j) i}

  bouquetFunct-id : bouquetFunct ≡ idfun _
  bouquetFunct-id =
    cong (λ f → Iso.fun (BouquetIso-gen n (card C n) (α C n) (e C n))
                ∘ f
                ∘ Iso.inv (BouquetIso-gen n (card C n) (α C n) (e C n)))
         fn+1/fn-id
    ∙ funExt (Iso.rightInv (BouquetIso-gen n (card C n) (α C n) (e C n)))

  chainFunct-id : chainFunct ≡ idGroupHom
  chainFunct-id = cong bouquetDegree bouquetFunct-id ∙ bouquetDegreeId

module fin-two (m : ℕ) (g : finCellMap m D E) (f : finCellMap m C D) (n' : Fin m) where
  module pf1 = finprefunctoriality m f n'
  module pf2 = finprefunctoriality m g n'
  module pf3 = finprefunctoriality m (composeFinCellMap m g f) n'
  open FinSequenceMap
  open CWskel-fields
  n = fst n'

  open fin-one
  fn+1/fn-comp : pf2.fn+1/fn ∘ pf1.fn+1/fn ≡ pf3.fn+1/fn
  fn+1/fn-comp = funExt
    λ { (inl x) → refl
      ; (inr x) → refl
      ; (push a i) j → help a j i}
    where
    help : (a : fst C n)
      → cong (pf2.fn+1/fn ∘ pf1.fn+1/fn) (push a)  ≡ cong pf3.fn+1/fn (push a)
    help a = cong-∙ pf2.fn+1/fn (push (f .fmap (injectSuc n') a))
                                (λ i₁ → inr (f .fcomm n' a i₁))
           ∙∙ sym (assoc _ _ _)
           ∙∙ sym (cong₂ _∙_ refl
                   (cong-∙ inr (g .fcomm n' (fmap f (injectSuc n') a))
                               (cong (g .fmap (fsuc n')) (f .fcomm n' a))))

  bouquetFunct-comp : pf2.bouquetFunct ∘ pf1.bouquetFunct ≡ pf3.bouquetFunct
  bouquetFunct-comp = funExt λ x
    → cong (Iso.fun (BouquetIso-gen n (card E n) (α E n) (e E n)))
       (cong pf2.fn+1/fn (Iso.leftInv (BouquetIso-gen n (card D n) (α D n) (e D n)) _)
     ∙ funExt⁻ fn+1/fn-comp (Iso.inv (BouquetIso-gen n (card C n) (α C n) (e C n)) x))

  chainFunct-comp : compGroupHom pf1.chainFunct pf2.chainFunct ≡ pf3.chainFunct
  chainFunct-comp = sym (bouquetDegreeComp∙ (pf2.bouquetFunct , refl) (pf1.bouquetFunct , refl))
                  ∙ cong bouquetDegree bouquetFunct-comp


module _ (g : cellMap D E) (f : cellMap C D) (n : ℕ) where
  module pf1 = prefunctoriality f n
  module pf2 = prefunctoriality g n
  module pf3 = prefunctoriality (composeCellMap g f) n
  open SequenceMap
  open CWskel-fields

  fn+1/fn-comp : pf2.fn+1/fn ∘ pf1.fn+1/fn ≡ pf3.fn+1/fn
  fn+1/fn-comp = funExt
    λ { (inl x) → refl
      ; (inr x) → refl
      ; (push a i) j → help a j i}
    where
    help : (a : fst C n)
      → cong (pf2.fn+1/fn ∘ pf1.fn+1/fn) (push a)  ≡ cong pf3.fn+1/fn (push a)
    help a = cong-∙ pf2.fn+1/fn (push (f .map n a))
                                (λ i₁ → inr (f .comm n a i₁))
           ∙∙ sym (assoc _ _ _)
           ∙∙ sym (cong₂ _∙_ refl
                   (cong-∙ inr (g .comm n (map f n a))
                               (cong (g .map (suc n)) (f .comm n a))))

  bouquetFunct-comp : pf2.bouquetFunct ∘ pf1.bouquetFunct ≡ pf3.bouquetFunct
  bouquetFunct-comp = funExt λ x
    → cong (Iso.fun (BouquetIso-gen n (card E n) (α E n) (e E n)))
       (cong pf2.fn+1/fn (Iso.leftInv (BouquetIso-gen n (card D n) (α D n) (e D n)) _)
     ∙ funExt⁻ fn+1/fn-comp (Iso.inv (BouquetIso-gen n (card C n) (α C n) (e C n)) x))

  chainFunct-comp : compGroupHom pf1.chainFunct pf2.chainFunct ≡ pf3.chainFunct
  chainFunct-comp = sym (bouquetDegreeComp∙ (pf2.bouquetFunct , refl) (pf1.bouquetFunct , refl))
                  ∙ cong bouquetDegree bouquetFunct-comp

-- Now we prove the commutativity condition to get a fully fledged chain map
module functoriality (f : cellMap C D) where
  open CWskel-fields
  open SequenceMap
  open prefunctoriality f

  -- δ ∘ fn+1/fn ≡ f ∘ δ
  commδ : (n : ℕ) (x : cofibCW n C) → δ n D (fn+1/fn n x) ≡ suspFun (f .map n) (δ n C x)
  commδ n (inl x) = refl
  commδ n (inr x) = refl
  commδ n (push a i) j =
    hcomp (λ k → λ { (i = i0) → north
          ; (i = i1) → south
          ; (j = i0) → δ n D (compPath-filler (push (f .map n a)) (cong inr (f .comm n a)) k i)
          ; (j = i1) → merid (f .map n a) i })
   (merid (f .map n a) i)

  -- Σto_cofibCW ∘ Σf ≡ Σfn+1/fn ∘ Σto_cofibCW
  commToCofibCWSusp : (n : ℕ) (x : Susp (fst C (suc n)))
                    → suspFun (to_cofibCW n D) (suspFun (f .map (suc n)) x)
                      ≡ suspFun (fn+1/fn n) (suspFun (to_cofibCW n C) x)
  commToCofibCWSusp n north = refl
  commToCofibCWSusp n south = refl
  commToCofibCWSusp n (merid a i) = refl

  -- commδ and commToCofibCWSusp give us the chain map equation at the level of cofibCWs
  -- now we massage isomorphisms and suspensions to get the proper equation between SphereBouquets
  funct∘pre∂ : (n : ℕ) → (SphereBouquet (suc n) (Fin (card C (suc n)))) → SphereBouquet (suc n) (Fin (card D n))
  funct∘pre∂ n = (bouquetSusp→ (bouquetFunct n)) ∘ (preboundary.pre∂ C n)

  pre∂∘funct : (n : ℕ) → (SphereBouquet (suc n) (Fin (card C (suc n)))) → SphereBouquet (suc n) (Fin (card D n))
  pre∂∘funct n = (preboundary.pre∂ D n) ∘ (bouquetFunct (suc n))

  commPre∂Funct : (n : ℕ) → funct∘pre∂ n ≡ pre∂∘funct n
  commPre∂Funct n = funExt λ x → (step1 x) ∙ (step2 x) ∙ (step3 x) ∙ (step4 x) ∙ (step5 x) ∙ (step6 x)
    where
      open preboundary
      open Iso

      bouquet : (C : CWskel ℓ) (n m : ℕ) → Type
      bouquet = λ C n m → SphereBouquet n (Fin (snd C .fst m))

      iso1 : (C : CWskel ℓ) (n : ℕ) → Iso (Susp (bouquet C n n)) (bouquet C (suc n) n)
      iso1 C n = sphereBouquetSuspIso

      iso2 : (C : CWskel ℓ) (n : ℕ) → Iso (cofibCW n C) (bouquet C n n)
      iso2 C n = BouquetIso-gen n (snd C .fst n) (snd C .snd .fst n) (snd C .snd .snd .snd n)

      step1 = λ (x : bouquet C (suc n) (suc n)) → cong (fun (iso1 D n) ∘ (suspFun (bouquetFunct n)))
                     (leftInv (iso1 C n) (((suspFun (fun (iso2 C n))) ∘ (suspFun (to_cofibCW n C))
                                   ∘ (δ (suc n) C) ∘ (inv (iso2 C (suc n)))) x))

      step2aux : ∀ x → suspFun (bouquetFunct n) x
                 ≡ (suspFun (fun (iso2 D n)) ∘ suspFun (fn+1/fn n) ∘ suspFun (inv (iso2 C n))) x
      step2aux north = refl
      step2aux south = refl
      step2aux (merid a i) = refl

      step2 = λ (x : bouquet C (suc n) (suc n)) → cong (fun (iso1 D n))
        (step2aux (((suspFun (fun (iso2 C n))) ∘ (suspFun (to_cofibCW n C))
                  ∘ (δ (suc n) C) ∘ (inv (iso2 C (suc n)))) x))

      step3aux : ∀ x → (suspFun (inv (iso2 C n)) ∘ suspFun (fun (iso2 C n))) x ≡ x
      step3aux north = refl
      step3aux south = refl
      step3aux (merid a i) j = merid (leftInv (iso2 C n) a j) i

      step3 = λ (x : bouquet C (suc n) (suc n)) →
        cong (fun (iso1 D n) ∘ (suspFun (fun (iso2 D n))) ∘ (suspFun (fn+1/fn n)))
             (step3aux (((suspFun (to_cofibCW n C)) ∘ (δ (suc n) C) ∘ (inv (iso2 C (suc n)))) x))

      step4 = λ (x : bouquet C (suc n) (suc n)) → cong ((fun (iso1 D n)) ∘ (suspFun (fun (iso2 D n))))
        (sym (commToCofibCWSusp n (((δ (suc n) C) ∘ (inv (iso2 C (suc n)))) x)))

      step5 = λ (x : bouquet C (suc n) (suc n)) →
        cong ((fun (iso1 D n)) ∘ (suspFun (fun (iso2 D n))) ∘ (suspFun (to_cofibCW n D)))
          (sym (commδ (suc n) (inv (iso2 C (suc n)) x)))

      step6 = λ (x : bouquet C (suc n) (suc n)) →
        cong ((fun (iso1 D n)) ∘ (suspFun (fun (iso2 D n))) ∘ (suspFun (to_cofibCW n D)) ∘ (δ (suc n) D))
        (sym (leftInv (iso2 D (suc n)) (((fn+1/fn (suc n)) ∘ (inv (iso2 C (suc n)))) x)))

  -- finally, we take bouquetDegree to get the equation at the level of abelian groups
  comm∂Funct : (n : ℕ) → compGroupHom (chainFunct (suc n)) (∂ D n) ≡ compGroupHom (∂ C n) (chainFunct n)
  comm∂Funct n = (sym (degree-pre∂∘funct n)) ∙∙ cong bouquetDegree (sym (commPre∂Funct n)) ∙∙ (degree-funct∘pre∂ n)
    where
      degree-funct∘pre∂ : (n : ℕ) → bouquetDegree (funct∘pre∂ n) ≡ compGroupHom (∂ C n) (chainFunct n)
      degree-funct∘pre∂ n = bouquetDegreeComp (bouquetSusp→ (bouquetFunct n)) (preboundary.pre∂ C n)
                          ∙ cong (λ X → compGroupHom (∂ C n) X) (sym (bouquetDegreeSusp (bouquetFunct n)))

      degree-pre∂∘funct : (n : ℕ) → bouquetDegree (pre∂∘funct n) ≡ compGroupHom (chainFunct (suc n)) (∂ D n)
      degree-pre∂∘funct n = bouquetDegreeComp (preboundary.pre∂ D n) (bouquetFunct (suc n))

-- Main statement of functoriality
-- From a cellMap, we can get a ChainComplexMap
cellMap-to-ChainComplexMap : (f : cellMap C D)
  → ChainComplexMap (CW-ChainComplex C) (CW-ChainComplex D)
cellMap-to-ChainComplexMap {C} {D} f .ChainComplexMap.chainmap n = prefunctoriality.chainFunct f n
cellMap-to-ChainComplexMap {C} {D} f .ChainComplexMap.bdrycomm n = functoriality.comm∂Funct f n

-- And thus a map of homology
cellMap-to-HomologyMap : (f : cellMap C D) (n : ℕ)
  → GroupHom (Hᶜʷ C n) (Hᶜʷ D n)
cellMap-to-HomologyMap {C = C} {D = D} f n =
  chainComplexMap→HomologyMap (cellMap-to-ChainComplexMap f) n

-- sanity check: chainFunct of a cellular map fₙ : Cₙ → Dₙ
-- is just functoriality of ℤ[-] when n = 1.
module _ (f : cellMap C D) where
  open CWskel-fields
  open SequenceMap
  open prefunctoriality f

  cellMap↾₁ : Fin (card C 0) → Fin (card D 0)
  cellMap↾₁ = fst (CW₁-discrete D) ∘ map f 1 ∘ invEq (CW₁-discrete C)

  chainFunct' : AbGroupHom (ℤ[A C ] 0) (ℤ[A D ] 0)
  chainFunct' = ℤFinFunct cellMap↾₁

  chainFunct₀ : chainFunct' ≡ chainFunct 0
  chainFunct₀ =
    agreeOnℤFinGenerator→≡ λ t → funExt λ x
    → sumFin-choose _+_ 0 (λ _ → refl) +Comm
        (λ a → ℤFinFunctGenerator cellMap↾₁ (ℤFinGenerator t) a x)
        (S⁰×S⁰→ℤ true (pickPetal x (bouquetFunct 0 (inr (t , false)))))
        t (ℤFinFunctGenerator≡ cellMap↾₁ t x ∙ main₁ t x)
        (main₂ cellMap↾₁ x t)
    ∙ isGeneratorℤFinGenerator'
        (λ a → degree 0 λ s
             → pickPetal x (bouquetFunct 0 (inr (a , s)))) t
    where
    F = Pushout→Bouquet 0 (card D 0) (α D 0) (e D 0)

    main₁ : (t : _) (x : _)
      → ℤFinGenerator (cellMap↾₁ t) x
       ≡ S⁰×S⁰→ℤ true
          (pickPetal x (F (fst (e D 0) (f .map 1 (invEq (CW₁-discrete C) t)))))
    main₁ t x = (ℤFinGeneratorComm (cellMap↾₁ t) x
      ∙ lem₂ (cellMap↾₁ t) x)
      ∙ cong (S⁰×S⁰→ℤ true ∘ pickPetal x ∘ F)
             (lem₁ _)
      where
      lem₀ : (x : Pushout (α D 0) fst)
        → inr (CW₁-discrete D .fst (invEq (e D 0) x)) ≡ x
      lem₀ (inl x) = ⊥.rec (CW₀-empty D x)
      lem₀ (inr x) j = inr (secEq (CW₁-discrete D) x j)

      lem₁ : (x : _)
        → inr (CW₁-discrete D .fst x) ≡ fst (e D 0) x
      lem₁ x = (λ i → inr (CW₁-discrete D .fst
                            (retEq (e D 0) x (~ i))))
              ∙ lem₀ (fst (e D 0) x)

      lem₂ : (t : _) (x : _)
        → ℤFinGenerator x t ≡ S⁰×S⁰→ℤ true (pickPetal x (inr (t , false)))
      lem₂ t x with (fst x ≟ fst t)
      ... | lt x₁ = refl
      ... | eq x₁ = refl
      ... | gt x₁ = refl

    main₂ : (f' : _) (x : _) (t : _) (x' : Fin (card C zero))
      → ¬ x' ≡ t
      → ℤFinFunctGenerator {n = card C zero} {m = card D zero}
                        f' (ℤFinGenerator t) x' x
       ≡ pos 0
    main₂ f' x t x' p with (f' x' .fst ≟ x .fst) | (fst t ≟ fst x')
    ... | lt x₁ | r = refl
    ... | eq x₂ | r = lem
      where
      lem : _
      lem with (fst t ≟ fst x')
      ... | lt x = refl
      ... | eq x = ⊥.rec (p (Σ≡Prop (λ _ → isProp≤) (sym x)))
      ... | gt x = refl
    ... | gt x₁ | r = refl

