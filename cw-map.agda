{-# OPTIONS --cubical --safe --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Int renaming (_·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Bool hiding (_≟_ ; isProp≤)

open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.Susp
open import Cubical.HITs.SequentialColimit


open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms

open import prelude
open import freeabgroup
open import spherebouquet
open import degree
open import cw-complex
open import cw-chain-complex
open import ChainComplex

module cw-map where

record cellMap (A B : CW) : Type where
  field
    map : (n : ℕ) → fst A n → fst B n
    comm : (n : ℕ) (x : fst A n) → CW↪ B n (map n x) ≡ map (suc n) (CW↪ A n x)

realiseCellMap : {A B : CW} → cellMap A B → realise A → realise B
realiseCellMap record { map = map ; comm = comm } (incl x) = incl (map _ x)
realiseCellMap record { map = map ; comm = comm } (push {n = n} x i) =
  (push (map n x) ∙ λ i → incl (comm n x i)) i

idCellMap : (A : CW) → cellMap A A
idCellMap A .cellMap.map n x = x
idCellMap A .cellMap.comm n x = refl

composeCellMap : {A B C : CW} (g : cellMap B C) (f : cellMap A B) → cellMap A C
composeCellMap g f .cellMap.map n x = g .cellMap.map n (f .cellMap.map n x)
composeCellMap g f .cellMap.comm n x = g .cellMap.comm n _
                                       ∙ cong (g .cellMap.map (suc n)) (f .cellMap.comm n x)

-- In this module, we transform a cellMap into a family of maps between free
-- abelian groups
module prefunctoriality {C D : CW} (f : cellMap C D) (n : ℕ) where
  open cellMap

  An = (snd C .fst n)
  αn = (snd C .snd .fst n)
  isoCn = (snd C .snd .snd .snd n)
  Bn = (snd D .fst n)
  βn = (snd D .snd .fst n)
  isoDn = (snd D .snd .snd .snd n)

  fn+1/fn : cofiber n C → cofiber n D
  fn+1/fn (inl tt) = inl tt
  fn+1/fn (inr x) = inr (f .map (suc n) x)
  fn+1/fn (push x i) = (push (f .map n x) ∙ (cong inr (f .comm n x))) i

  bouquetFunct : SphereBouquet n (Fin An) → SphereBouquet n (Fin Bn)
  bouquetFunct x = Iso.fun (BouquetIso-gen n Bn βn isoDn) (fn+1/fn (Iso.inv (BouquetIso-gen n An αn isoCn) x))

  chainFunct : AbGroupHom (ℤ[A C ] n) (ℤ[A D ] n)
  chainFunct = bouquetDegree bouquetFunct

-- Now we prove the commutativity condition to get a fully fledged chain map
module functoriality {C D : CW} (f : cellMap C D) where
  open cellMap
  open prefunctoriality f

  commδ : (n : ℕ) (x : cofiber n C) → δ n D (fn+1/fn n x) ≡ suspFun (f .map n) (δ n C x)
  commδ n (inl x) = refl
  commδ n (inr x) = refl
  commδ n (push a i) j = -- that would be refl if function application commuted with hcomp
    hcomp (λ k → λ { (i = i0) → north
          ; (i = i1) → south
          ; (j = i0) → δ n D (compPath-filler (push (f .map n a)) (cong inr (f .comm n a)) k i)
          ; (j = i1) → merid (f .map n a) i })
   (merid (f .map n a) i)

  commToCofiberSusp : (n : ℕ) (x : Susp (fst C (suc n)))
                    → suspFun (to_cofiber n D) (suspFun (f .map (suc n)) x)
                      ≡ suspFun (fn+1/fn n) (suspFun (to_cofiber n C) x)
  commToCofiberSusp n north = refl
  commToCofiberSusp n south = refl
  commToCofiberSusp n (merid a i) = refl

  -- now we can get that pre∂ is a pre-chain map by pasting commδ and commToCofiberSusp
  funct∘pre∂ : (n : ℕ) → (SphereBouquet (suc n) (Fin (An (suc n)))) → SphereBouquet (suc n) (Fin (Bn n))
  funct∘pre∂ n = (bouquetSusp→ (bouquetFunct n)) ∘ (preboundary.pre∂ C n)

  degree-funct∘pre∂ : (n : ℕ) → bouquetDegree (funct∘pre∂ n) ≡ compGroupHom (∂ C n) (chainFunct n)
  degree-funct∘pre∂ n = degreeComp (bouquetSusp→ (bouquetFunct n)) (preboundary.pre∂ C n)
                      ∙ cong (λ X → compGroupHom (∂ C n) X) (sym (degreeSusp (bouquetFunct n)))

  pre∂∘funct : (n : ℕ) → (SphereBouquet (suc n) (Fin (An (suc n)))) → SphereBouquet (suc n) (Fin (Bn n))
  pre∂∘funct n = (preboundary.pre∂ D n) ∘ (bouquetFunct (suc n))

  degree-pre∂∘funct : (n : ℕ) → bouquetDegree (pre∂∘funct n) ≡ compGroupHom (chainFunct (suc n)) (∂ D n)
  degree-pre∂∘funct n = degreeComp (preboundary.pre∂ D n) (bouquetFunct (suc n))

  commPre∂Funct : (n : ℕ) → funct∘pre∂ n ≡ pre∂∘funct n
  commPre∂Funct n = funExt λ x → (step1 x) ∙ (step2 x) ∙ (step3 x) ∙ (step4 x) ∙ (step5 x) ∙ (step6 x)
    where
      open preboundary
      open Iso

      bouquet : (C : CW) (n m : ℕ) → Type
      bouquet = λ C n m → SphereBouquet n (Fin (snd C .fst m))

      iso1 : (C : CW) (n : ℕ) → Iso (Susp (bouquet C n n)) (bouquet C (suc n) n)
      iso1 C n = sphereBouquetSuspIso

      iso2 : (C : CW) (n : ℕ) → Iso (cofiber n C) (bouquet C n n)
      iso2 C n = BouquetIso-gen n (snd C .fst n) (snd C .snd .fst n) (snd C .snd .snd .snd n)

      step1 = λ (x : bouquet C (suc n) (suc n)) → cong (fun (iso1 D n) ∘ (suspFun (bouquetFunct n)))
                     (leftInv (iso1 C n) (((suspFun (fun (iso2 C n))) ∘ (suspFun (to_cofiber n C))
                                   ∘ (δ (suc n) C) ∘ (inv (iso2 C (suc n)))) x))

      step2aux : ∀ x → suspFun (bouquetFunct n) x
                 ≡ (suspFun (fun (iso2 D n)) ∘ suspFun (fn+1/fn n) ∘ suspFun (inv (iso2 C n))) x
      step2aux north = refl
      step2aux south = refl
      step2aux (merid a i) = refl

      step2 = λ (x : bouquet C (suc n) (suc n)) → cong (fun (iso1 D n))
        (step2aux (((suspFun (fun (iso2 C n))) ∘ (suspFun (to_cofiber n C))
                  ∘ (δ (suc n) C) ∘ (inv (iso2 C (suc n)))) x))

      step3aux : ∀ x → (suspFun (inv (iso2 C n)) ∘ suspFun (fun (iso2 C n))) x ≡ x
      step3aux north = refl
      step3aux south = refl
      step3aux (merid a i) j = merid (leftInv (iso2 C n) a j) i

      step3 = λ (x : bouquet C (suc n) (suc n)) →
        cong (fun (iso1 D n) ∘ (suspFun (fun (iso2 D n))) ∘ (suspFun (fn+1/fn n)))
             (step3aux (((suspFun (to_cofiber n C)) ∘ (δ (suc n) C) ∘ (inv (iso2 C (suc n)))) x))

      step4 = λ (x : bouquet C (suc n) (suc n)) → cong ((fun (iso1 D n)) ∘ (suspFun (fun (iso2 D n))))
        (sym (commToCofiberSusp n (((δ (suc n) C) ∘ (inv (iso2 C (suc n)))) x)))

      step5 = λ (x : bouquet C (suc n) (suc n)) →
        cong ((fun (iso1 D n)) ∘ (suspFun (fun (iso2 D n))) ∘ (suspFun (to_cofiber n D)))
          (sym (commδ (suc n) (inv (iso2 C (suc n)) x)))

      step6 = λ (x : bouquet C (suc n) (suc n)) →
        cong ((fun (iso1 D n)) ∘ (suspFun (fun (iso2 D n))) ∘ (suspFun (to_cofiber n D)) ∘ (δ (suc n) D))
        (sym (leftInv (iso2 D (suc n)) (((fn+1/fn (suc n)) ∘ (inv (iso2 C (suc n)))) x)))


  comm∂Funct : (n : ℕ) → compGroupHom (chainFunct (suc n)) (∂ D n) ≡ compGroupHom (∂ C n) (chainFunct n)
  comm∂Funct n = (sym (degree-pre∂∘funct n)) ∙∙ cong bouquetDegree (sym (commPre∂Funct n)) ∙∙ (degree-funct∘pre∂ n)

cellMap-to-ChainComplexMap : {C D : CW} (f : cellMap C D)
                           → ChainComplexMap (CW-ChainComplex C) (CW-ChainComplex D)
cellMap-to-ChainComplexMap {C} {D} f .ChainComplexMap.chainmap n = prefunctoriality.chainFunct f n
cellMap-to-ChainComplexMap {C} {D} f .ChainComplexMap.bdrycomm n = functoriality.comm∂Funct f n

cellMap-to-HomologyMap : {C D : CW} (f : cellMap C D) (n : ℕ)
  → GroupHom (Hᶜʷ C n) (Hᶜʷ D n)
cellMap-to-HomologyMap {C = C} {D = D} f n =
  chainComplexMap→HomologyMap (cellMap-to-ChainComplexMap f) n

-- sanity check: chainFunct of a cellular map fₙ : Cₙ → Dₙ
-- is just functoriality of ℤ[-] when n = 1.
module _ {C D : CW} (f : cellMap C D) where
  open cellMap
  open prefunctoriality f
  cellMap↾₁ : Fin (An 0) → Fin (Bn 0)
  cellMap↾₁ = fst (CW₁-discrete D) ∘ map f 1 ∘ invEq (CW₁-discrete C)

  chainFunct' : AbGroupHom (ℤ[A C ] 0) (ℤ[A D ] 0)
  chainFunct' = ℤ[]-funct cellMap↾₁

  chainFunct₀ : chainFunct' ≡ chainFunct 0
  chainFunct₀ =
    EqHoms λ t → funExt λ x
    → sumFin-choose _+_ 0 (λ _ → refl) +Comm
        (λ a → pre-ℤ[]-funct cellMap↾₁ (generator t) a x)
        (S⁰×S⁰→ℤ true (chooseS x (bouquetFunct 0 (inr (t , false)))))
        t (pre-ℤ[]-funct-gen cellMap↾₁ t x ∙ main₁ t x)
        (main₂ cellMap↾₁ x t)
    ∙ generator-is-generator'
        (λ a → degree 0 λ s
             → chooseS x (bouquetFunct 0 (inr (a , s)))) t
    where
    F = Pushout→Bouquet 0 (Bn 0) (βn 0) (isoDn 0)

    main₁ : (t : _) (x : _)
      → generator (cellMap↾₁ t) x
       ≡ S⁰×S⁰→ℤ true
          (chooseS x (F (fst (isoDn 0) (f .map 1 (invEq (CW₁-discrete C) t)))))
    main₁ t x = (generator-comm (cellMap↾₁ t) x
      ∙ lem₂ (cellMap↾₁ t) x)
      ∙ cong (S⁰×S⁰→ℤ true ∘ chooseS x ∘ F)
             (lem₁ _)
      where
      lem₀ : (x : Pushout (βn 0) fst)
        → inr (CW₁-discrete D .fst (invEq (isoDn 0) x)) ≡ x
      lem₀ (inl x) = ⊥.rec (CW₀-empty D x)
      lem₀ (inr x) j = inr (secEq (CW₁-discrete D) x j)

      lem₁ : (x : _)
        → inr (CW₁-discrete D .fst x) ≡ fst (isoDn 0) x
      lem₁ x = (λ i → inr (CW₁-discrete D .fst
                            (retEq (isoDn 0) x (~ i))))
              ∙ lem₀ (fst (isoDn 0) x)

      lem₂ : (t : _) (x : _)
        → generator x t ≡ S⁰×S⁰→ℤ true (chooseS x (inr (t , false)))
      lem₂ t x with (fst x ≟ fst t)
      ... | lt x₁ = refl
      ... | eq x₁ = refl
      ... | gt x₁ = refl

    main₂ : (f' : _) (x : _) (t : _) (x' : Fin (An zero))
      → ¬ x' ≡ t
      → pre-ℤ[]-funct {n = An zero} {m = Bn zero}
                        f' (generator t) x' x
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
