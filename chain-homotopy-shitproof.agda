{-# OPTIONS --cubical --allow-unsolved-metas --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (isProp≤)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.SequentialColimit
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base


open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.AbGroup
open import freeabgroup
open import spherebouquet
open import cw-chain-complex


open import prelude
open import cw-complex
open import choice
open import cw-map
open import freeabgroup
open import cw-approx

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import degree
open import Cubical.Data.Int renaming (_+_ to _+ℤ_)


module chain-homotopy-shitproof where

open Sequence
open import Cubical.HITs.Susp

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.HITs.Wedge


bouquetSusp→· : {n : ℕ} {A B : Type}
  → (a : A)
  → (f : SphereBouquet (suc n) A → SphereBouquet (suc n) B)
  → (f (inl tt) ≡ inl tt) 
  → cong (bouquetSusp→ f) (λ i → inr (a , merid (ptSn (suc n)) i)) ≡ refl
bouquetSusp→· {n = n} {B = B} a f p =
  cong (Bouquet→ΩBouquetSusp B (λ _ → S₊ (suc n) , ptSn (suc n)))
    (cong f (sym (push a)) ∙ p)

Bouquet→Const : {A : Type} {C : Pointed₀} {B : A → Pointed₀}
     (f : (Pushout (terminal A) ((λ a → a , B a .snd)) , inl tt)
         →∙ C)
  → ((x : _) → fst f (inr x) ≡ pt C)
  → (x : _) → f .fst x ≡ pt C
Bouquet→Const f ind (inl x) = snd f
Bouquet→Const {C = C} {B = B} f ind (inr x) =
  (ind x ∙ sym (ind (fst x , pt (B _)))) ∙ (cong (fst f) (sym (push (fst x))) ∙ snd f)
Bouquet→Const {C = C}{B = B}  f ind (push a i) j = help i j
  where
  help : PathP (λ i → f . fst (push a i) ≡ snd C)
               (snd f)
               ((ind (a , pt (B _)) ∙ sym (ind (a , pt (B _))))
               ∙ (cong (fst f) (sym (push a)) ∙ snd f))
  help = (compPath-filler' (sym (cong (fst f) (push a))) (snd f))
       ▷ sym (cong (_∙ cong (fst f) (sym (push a)) ∙ snd f) (rCancel _) ∙ sym (lUnit _))

open import Cubical.Foundations.Pointed.Homogeneous
Bouquet→Ω : {A C : Type} {B : A → Pointed₀}
    {c : C}
     (f g : Pushout (terminal A) ((λ a → a , B a .snd))
         → (c ≡ c))
  → (f (inl tt) ≡ refl)
  → (g (inl tt) ≡ refl)
  → ((x : _) → f (inr x) ≡ g (inr x))
  → (x : _) → f x ≡ g x
Bouquet→Ω f g p q h x =
     rUnit (f x)
  ∙∙ cong (f x ∙_) (sym (lCancel (g x)))
  ∙∙ assoc (f x) (sym (g x)) (g x)
  ∙∙ cong (_∙ (g x)) (lem x)
  ∙∙ sym (lUnit (g x))
  where
  lem : (x : _) → f x ∙ sym (g x) ≡ refl
  lem = Bouquet→Const ((λ x → f x ∙ sym (g x)) , cong₂ _∙_ p (cong sym q) ∙ sym (rUnit refl))
          λ x → cong (_∙ sym (g (inr x))) (h x) ∙ rCancel _

module _ {C D : CW} (n : ℕ) (f : Susp (cofiber n C) → cofiber (suc n) D) where
  module ℂ = CW-fields C
  module 𝔻 = CW-fields D
  cofib-map→sphereBouquetMap↑ : SphereBouquet (suc n) (Fin (snd C .fst n))
                              → SphereBouquet (suc n) (Fin (snd D .fst (suc n)))
  cofib-map→sphereBouquetMap↑ =
      BouquetIso-gen (suc n) (𝔻.card (suc n)) (𝔻.α (suc n)) (𝔻.e (suc n)) .Iso.fun
    ∘ f
    ∘ suspFun (BouquetIso-gen n (ℂ.card n) (ℂ.α n) (ℂ.e n) .Iso.inv)
    ∘ Iso.inv sphereBouquetSuspIso

  cofib-map→ℤ↑ : AbGroupHom (ℤ[A C ] n) (ℤ[A D ] (suc n))
  cofib-map→ℤ↑ = bouquetDegree {n = suc n} cofib-map→sphereBouquetMap↑

cofib-map→sphereBouquetMap↑∙ :
  {C D : CW} (n : ℕ) (t : Fin (snd C .fst (suc n)))
    (f : Susp (cofiber (suc n) C) → cofiber (suc (suc n)) D)
    (fp : f north ≡ inl tt)
      → cong (λ x → cofib-map→sphereBouquetMap↑ (suc n) f (inr (t , x))) (merid (ptSn (suc n)))
      ≡ cong ((BouquetFuns.CTB (suc (suc n)) (D .snd .fst (suc (suc n)))
      (D .snd .snd .fst (suc (suc n)))
      (D .snd .snd .snd .snd (suc (suc n)))) ∘ f) (merid (inl tt))
cofib-map→sphereBouquetMap↑∙ {C = C} {D = D} zero t f fp = refl
cofib-map→sphereBouquetMap↑∙ {C = C} {D = D} (suc n) t f fp = refl

module _ {C D : CW} (f-c g-c : cellMap C D) where
  private
    f = cellMap.map f-c
    g = cellMap.map g-c
    f-hom = cellMap.comm f-c
    g-hom = cellMap.comm g-c

  cofib-map-filler : (n : ℕ)
    (hₙ : (c : _) → CW↪ D n (f n c) ≡ CW↪ D n (g n c))
    (hₙ₊₁ : (c : _) → CW↪ D (suc n) (f (suc n) c)
                     ≡ CW↪ D (suc n) (g (suc n) c))
    (hₙ-coh : (c : _)
    → Square (cong (CW↪ D (suc n)) (hₙ c)) (hₙ₊₁ (CW↪ C n c))
             (cong (CW↪ D (suc n)) (f-hom n c))
             (cong (CW↪ D (suc n)) (g-hom n c)))
    (a : _) → (i j k : I) → cofiber (suc n) D
  cofib-map-filler n hₙ hₙ₊₁ hₙ-coh a i j k =
    hfill (λ k → λ {(i = i0) → push (f-hom n a j) (~ k)
                   ; (i = i1) → push (g-hom n a j) (~ k)
                   ; (j = i0) → push (hₙ a i) (~ k)
                   ; (j = i1) → doubleCompPath-filler
                                  (push (f (suc n) (CW↪ C n a)))
                                  (λ i₁ → inr (hₙ₊₁ (CW↪ C n a) i₁))
                                  (sym (push (g (suc n) (CW↪ C n a)))) k i})
          (inS (inr (hₙ-coh a j i))) k

  cofib-map :  (n : ℕ)
    (hₙ : (c : _) → CW↪ D n (f n c) ≡ CW↪ D n (g n c))
    (hₙ₊₁ : (c : _) → CW↪ D (suc n) (f (suc n) c)
                     ≡ CW↪ D (suc n) (g (suc n) c))
    (hₙ-coh : (c : _)
    → Square (cong (CW↪ D (suc n)) (hₙ c)) (hₙ₊₁ (CW↪ C n c))
              (cong (CW↪ D (suc n)) (f-hom n c))
              (cong (CW↪ D (suc n)) (g-hom n c)))
    → Susp (cofiber n C) → cofiber (suc n) D
  cofib-map n hₙ hₙ₊₁ hₙ-coh north = inl tt
  cofib-map n hₙ hₙ₊₁ hₙ-coh south = inl tt
  cofib-map n hₙ hₙ₊₁ hₙ-coh (merid (inl x) i) = inl tt
  cofib-map n hₙ hₙ₊₁ hₙ-coh (merid (inr x) i) =
    (push (f (suc n) x) ∙∙ (λ i → inr (hₙ₊₁ x i)) ∙∙ sym (push (g (suc n) x))) i
  cofib-map n hₙ hₙ₊₁ hₙ-coh (merid (push a j) i) =
      cofib-map-filler n hₙ hₙ₊₁ hₙ-coh a i j i1


open import Cubical.Homotopy.Loopspace
open import Cubical.Foundations.Pointed
open import Cubical.HITs.S1
open import Cubical.Data.Int renaming (_+_ to _+ℤ_ ; -_ to -ℤ_ ; _·_ to _·ℤ_)
open import degree
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Properties

ΩSphere : {n : ℕ} -- move to degree.agda
  → (S₊ n → Ω (S₊∙ (suc n)) .fst) → S₊ (suc n) → S₊ (suc n)
ΩSphere {zero} f base = base
ΩSphere {zero} f (loop i) = f false i
ΩSphere {suc n} f north = north
ΩSphere {suc n} f south = north
ΩSphere {suc n} f (merid a i) = f a i

degreePres- : {n : ℕ} -- move to degree.agda 
  → (f : S₊ n → Ω (S₊∙ (suc n)) .fst)
  → degree (suc n) (ΩSphere (λ x → sym (f x)))
  ≡ -ℤ (degree (suc n) (ΩSphere f))
degreePres- {n = n} f =
    cong (Iso.fun (Hⁿ-Sⁿ≅ℤ n .fst)) (help n f)
  ∙ IsGroupHom.presinv (Hⁿ-Sⁿ≅ℤ n .snd) ∣ (λ x → ∣ ΩSphere f x ∣) ∣₂
  where
  lem : (n : ℕ) → (p : Path (coHomK (suc n)) (0ₖ (suc n)) (0ₖ (suc n)))
    → PathP (λ i → -0ₖ {n = suc n} i ≡ -0ₖ {n = suc n} i) (cong (-ₖ_) p) (sym p)
  lem n p = cong (cong (-ₖ_)) (sym (Iso.rightInv (Iso-Kn-ΩKn+1 n) p))
    ◁ (main n (ΩKn+1→Kn n p)
    ▷ (cong sym (Iso.rightInv (Iso-Kn-ΩKn+1 n) p)))
    where
    Kn→ΩKn+1' : (n : ℕ) → coHomK n → Ω (coHomK (suc n) , 0ₖ (suc n)) .fst
    Kn→ΩKn+1' zero x = cong (-ₖ_) (Kn→ΩKn+1 zero x)
    Kn→ΩKn+1' (suc n) = TR.elim (λ _ → isOfHLevelTrunc (4 +ℕ n) _ _)
      λ a → cong -ₖ_ (cong ∣_∣ₕ (merid a))

    Kn→ΩKn+1'≡ : (n : ℕ) (x : _)
      → PathP (λ i → -0ₖ {n = suc n} i ≡ -0ₖ {n = suc n} i)
              (cong (-ₖ_) (Kn→ΩKn+1 n x)) (Kn→ΩKn+1' n x)
    Kn→ΩKn+1'≡ zero = λ _ → refl
    Kn→ΩKn+1'≡ (suc n) =
      TR.elim (λ _ → isOfHLevelPath (3 +ℕ n) (isOfHLevelTrunc (4 +ℕ n) _ _) _ _)
        λ a → cong-∙ (-ₖ_ ∘ ∣_∣ₕ) (merid a) (sym (merid (ptSn (suc n))))
            ∙ cong (Kn→ΩKn+1' (suc n) ∣ a ∣ₕ ∙_)
                   (cong (sym ∘ cong ∣_∣ₕ) (rCancel (merid (ptSn (suc n)))))
            ∙ sym (rUnit _)

    cong-ₖ-pos1 : Kn→ΩKn+1' zero (pos 1) ≡ sym (Kn→ΩKn+1 zero (pos 1))
    cong-ₖ-pos1 = cong (cong (-ₖ_)) lemma ∙ cong sym (sym lemma)
      where
      lemma : Kn→ΩKn+1 zero (pos 1) ≡ cong ∣_∣ₕ loop
      lemma = sym (cong (cong ∣_∣ₕ) (lUnit loop)  ∙ rUnit (cong ∣_∣ₕ (refl ∙ loop)))

    cong-ₖ-pos : (x : ℕ) → Kn→ΩKn+1' zero (pos x) ≡ sym (Kn→ΩKn+1 zero (pos x))
    cong-ₖ-pos zero = refl
    cong-ₖ-pos (suc n) = cong (cong (-ₖ_)) (Kn→ΩKn+1-hom zero (pos n) 1)
                        ∙ cong-∙ (-ₖ_) (Kn→ΩKn+1 zero (pos n)) (Kn→ΩKn+1 zero (pos 1))
                        ∙ cong₂ _∙_ (cong-ₖ-pos n) cong-ₖ-pos1
                        ∙ sym (symDistr (Kn→ΩKn+1 zero (pos 1)) (Kn→ΩKn+1 zero (pos n))) 
                        ∙ cong sym (isCommΩK 1 (Kn→ΩKn+1 zero (pos 1))
                                               (Kn→ΩKn+1 zero (pos n))
                                  ∙ sym (Kn→ΩKn+1-hom zero (pos n) 1))
    

    cong-ₖ : (x : ℤ) → Kn→ΩKn+1' zero x ≡ sym (Kn→ΩKn+1 zero x)
    cong-ₖ (pos n) = cong-ₖ-pos n
    cong-ₖ (negsuc n) =
         (cong (cong (-ₖ_))
          (cong (Kn→ΩKn+1 zero) (minus≡0- (pos (suc n)))
         ∙ (Kn→ΩKn+1-ₖ zero (pos (suc n)))))
      ∙∙ cong sym (cong-ₖ-pos (suc n))
      ∙∙ (cong (Kn→ΩKn+1 zero) (minus≡0- (negsuc n))
        ∙ Kn→ΩKn+1-ₖ zero (negsuc n))

    main-tr : (n : ℕ) → (x : coHomK n)
      → Kn→ΩKn+1' n x ≡ sym (Kn→ΩKn+1 n x)
    main-tr zero = cong-ₖ
    main-tr (suc n) =
      TR.elim (λ _ → isOfHLevelPath (3 +ℕ n) (isOfHLevelTrunc (4 +ℕ n) _ _) _ _)
        λ a → cong (cong ∣_∣ₕ) (sym (symDistr (merid a) (sym (merid (ptSn (suc n))))))

    main :  (n : ℕ) → (x : coHomK n)
      → PathP (λ i → -0ₖ {n = suc n} i ≡ -0ₖ {n = suc n} i)
              (cong (-ₖ_) (Kn→ΩKn+1 n x)) (sym (Kn→ΩKn+1 n x))
    main n x = Kn→ΩKn+1'≡ n x ▷ main-tr n x

  help : (n : ℕ) (f : _) → Path (coHomGr (suc n) (S₊ (suc n)) .fst)
              ∣ (λ x → ∣ ΩSphere (λ x₁ → sym (f x₁)) x ∣) ∣₂
              (-ₕ ∣ (λ x → ∣ ΩSphere f x ∣) ∣₂)
  help zero f = cong ∣_∣₂ (funExt λ { base → refl ; (loop i) j → lem _ (cong ∣_∣ₕ (f false)) (~ j) i})
  help (suc n) f = cong ∣_∣₂ (funExt λ { north → refl ; south → refl ; (merid a i) j → lem _ (cong ∣_∣ₕ (f a)) (~ j) i })

degreePres+ : {n : ℕ} -- move to degree.agda
  → (f g : S₊ n → Ω (S₊∙ (suc n)) .fst)
  → degree (suc n) (ΩSphere (λ x → f x ∙ g x))
  ≡ degree (suc n) (ΩSphere f) +ℤ degree (suc n) (ΩSphere g) 
degreePres+ {n = n} f g =
    cong (Iso.fun (Hⁿ-Sⁿ≅ℤ n .fst)) (help n f g)
  ∙ IsGroupHom.pres· (Hⁿ-Sⁿ≅ℤ n .snd)
    ∣ (λ x → ∣ ΩSphere f x ∣) ∣₂
    ∣ (λ x → ∣ ΩSphere g x ∣) ∣₂
  where
  help : (n : ℕ) → (f g : S₊ n → Ω (S₊∙ (suc n)) .fst)
       → Path (coHom (suc n) (S₊ (suc n)))
               ∣ ∣_∣ₕ ∘ ΩSphere (λ x → f x ∙ g x) ∣₂
               (∣ ∣_∣ₕ ∘ ΩSphere f ∣₂ +ₕ ∣ ∣_∣ₕ ∘ ΩSphere g ∣₂)
  help zero f g = cong ∣_∣₂
    (funExt (λ { base → refl
               ; (loop i) j
                 → (cong-∙ ∣_∣ₕ (f false) (g false)
                  ∙ ∙≡+₁ (cong ∣_∣ₕ (f false)) (cong ∣_∣ₕ (g false))) j i}))
  help (suc n) f g = cong ∣_∣₂
    (funExt (λ { north → refl
               ; south → refl
               ; (merid a i) j
                → (cong-∙ ∣_∣ₕ (f a) (g a)
                  ∙ ∙≡+₂ n (cong ∣_∣ₕ (f a)) (cong ∣_∣ₕ (g a))) j i}))

cofib-map→sphereBouquetMap↑-pt : {C D : CW} (m : ℕ) (f : _)
  → (f north ≡ inl tt)
  → cofib-map→sphereBouquetMap↑ {C = C} {D = D} m f (Iso.fun sphereBouquetSuspIso north)
    ≡ inl tt
cofib-map→sphereBouquetMap↑-pt {D = D} zero f p i =
  BouquetFuns.CTB 1 (D .snd .fst 1) (D .snd .snd .fst 1)
         (D .snd .snd .snd .snd 1) (p i)
cofib-map→sphereBouquetMap↑-pt  {D = D} (suc m) f p i =
  BouquetFuns.CTB (suc (suc m)) (D .snd .fst (suc (suc m)))
         (D .snd .snd .fst (suc (suc m)))
         (D .snd .snd .snd .snd (suc (suc m))) (p i)

module _ {C D : CW} (f-c g-c : cellMap C D)
         (h∞ : realiseCellMap f-c ≡ realiseCellMap g-c) where
  private
    f = cellMap.map f-c
    g = cellMap.map g-c
    f-hom = cellMap.comm f-c
    g-hom = cellMap.comm g-c
    cell-homC = cell-hom f-c g-c h∞
    cell-hom-cohC = cell-hom-coh f-c g-c h∞

  


  open CW-fields C
  module _ (m : ℕ)
           (hₘ : (c : fst C m) → cell-homC m c)
           (hₘ₊₁ : (c : fst C (suc m)) → cell-homC (suc m) c)
           (hₘ₊₂ : (c : fst C (suc (suc m))) → cell-homC (suc (suc m)) c)
           (hₘ-coh : (c : fst C m) → cell-hom-cohC m c (hₘ c) (hₘ₊₁ (CW↪ C m c)))
           (hₘ₊₁-coh : (c : fst C (suc m)) → cell-hom-cohC (suc m) c (hₘ₊₁ c) (hₘ₊₂ (CW↪ C (suc m) c))) where

    


    Hₘ : AbGroupHom (ℤ[A C ] m) (ℤ[A D ] (suc m))
    Hₘ = cofib-map→ℤ↑ m (cofib-map f-c g-c m hₘ hₘ₊₁ hₘ-coh)

    ∂ₘ : AbGroupHom (ℤ[A C ] (suc m)) (ℤ[A C ] m)
    ∂ₘ = ∂ C m
    
    Hₘ∂ₘ : AbGroupHom (ℤ[A C ] (suc m)) (ℤ[A D ] (suc m))
    Hₘ∂ₘ = compGroupHom ∂ₘ Hₘ

    f-space-back : Type
    f-space-back = (SphereBouquet (suc m) (Fin (snd C .fst (suc m)))
                  → Path (SphereBouquet (suc (suc m))
                          (Fin (snd D .fst (suc m)))) (inl tt) (inl tt))

    f-space-back-gen : SphereBouquet (suc (suc m))
                          (Fin (snd D .fst (suc m))) → Type
    f-space-back-gen x = (SphereBouquet (suc m) (Fin (snd C .fst (suc m)))
                  → Path (SphereBouquet (suc (suc m))
                          (Fin (snd D .fst (suc m)))) x x)

    fspace-rewrite'' : (x : _) → f-space-back-gen x → Susp (SphereBouquet (suc m) (Fin (snd C .fst (suc m))))
      → SphereBouquet (suc (suc m)) (Fin (snd D .fst (suc m)))
    fspace-rewrite'' x f north = x
    fspace-rewrite'' x f south = x
    fspace-rewrite'' x f (merid a i) = f a i

    fspace-rewrite' : f-space-back → Susp (SphereBouquet (suc m) (Fin (snd C .fst (suc m))))
      → SphereBouquet (suc (suc m)) (Fin (snd D .fst (suc m)))
    fspace-rewrite' = fspace-rewrite'' (inl tt)

    fspace-rewrite-gen : (a : _) → f-space-back-gen a
                  → SphereBouquet (suc (suc m)) (Fin (snd C .fst (suc m)))
                  → SphereBouquet (suc (suc m)) (Fin (snd D .fst (suc m)))
    fspace-rewrite-gen a f x = fspace-rewrite'' a f (Iso.inv sphereBouquetSuspIso x) 

    fspace-rewrite : f-space-back
                  → SphereBouquet (suc (suc m)) (Fin (snd C .fst (suc m)))
                  → SphereBouquet (suc (suc m)) (Fin (snd D .fst (suc m)))
    fspace-rewrite = fspace-rewrite-gen (inl tt)




    chooseS-ΩSphere : (f : f-space-back)
           (x : Fin (snd D .fst (suc m)))
           (t : Fin (snd C .fst (suc m)))
           (x' : S₊ (suc (suc m)))
      → Path (S₊ (suc (suc m)))
                (chooseS x (fspace-rewrite f (inr (t , x'))))
                ((ΩSphere {n = suc m} λ x' → cong (chooseS x) (f (inr (t , x')))) x')
    chooseS-ΩSphere f x t north = refl
    chooseS-ΩSphere f x t south = refl
    chooseS-ΩSphere f x t (merid a i) = refl

    bouquetDegInv : (f : _ ) → bouquetDegree (fspace-rewrite λ x → sym (f x))
                              ≡ negGroupHom _ _ (bouquetDegree (fspace-rewrite f))
    bouquetDegInv f = EqHoms λ t → funExt λ x
      →  sym (p x t (sym ∘ f))
        ∙ cong (degree  (suc (suc m))) (funExt (chooseS-ΩSphere (sym ∘ f) x t))
        ∙ degreePres-  (λ x' → cong (chooseS x) (f (inr (t , x'))))
        ∙ cong (-ℤ_ ∘ degree  (suc (suc m))) (sym (funExt (chooseS-ΩSphere f x t)))
        ∙ cong -ℤ_ (p x t f)
      where
      p : (x : _) (t  : _) (f : _) → _
      p x t f = (generator-is-generator' (λ a → degree (suc (suc m))
                λ x' → chooseS x (fspace-rewrite f (inr (a , x')))) t)

    bouquetDeg+ : (f g : f-space-back)
      → bouquetDegree (fspace-rewrite (λ x → f x ∙ g x))
       ≡ addGroupHom _ _
           (bouquetDegree (fspace-rewrite f))
           (bouquetDegree (fspace-rewrite g)) 
    bouquetDeg+ f g =
      EqHoms λ t → funExt λ x
        → sym (generator-is-generator' (λ a → degree (suc (suc m))
                λ x' → chooseS x (fspace-rewrite (λ x₂ → f x₂ ∙ g x₂) (inr (a , x')))) t)
              ∙ cong (degree (suc (suc m))) (funExt (chooseS-ΩSphere (λ x₂ → f x₂ ∙ g x₂) x t))
              ∙ cong (degree (suc (suc m)))
                 (cong ΩSphere (funExt
                   (λ x' → cong-∙ (chooseS x) (f (inr (t , x'))) (g (inr (t , x'))))))
              ∙ degreePres+ (λ x' → cong (chooseS x) (f (inr (t , x'))))
                                (λ x' → cong (chooseS x) (g (inr (t , x'))))
              ∙ cong₂ _+ℤ_
                   (sym (cong (degree (suc (suc m))) (funExt (chooseS-ΩSphere f x t)))
                        ∙ generator-is-generator'
                         (λ a → degree (suc (suc m))
                           λ x' → chooseS x (fspace-rewrite f (inr (a , x')))) t)
                   (sym (cong (degree (suc (suc m))) (funExt (chooseS-ΩSphere g x t)))
                        ∙ generator-is-generator'
                         (λ a → degree (suc (suc m))
                          λ x' → chooseS x (fspace-rewrite g (inr (a , x')))) t)

    Hₘ∂ₘ'-map : SphereBouquet (suc (suc m)) (Fin (snd C .fst (suc m)))
             → SphereBouquet (suc (suc m)) (Fin (snd D .fst (suc m)))
    Hₘ∂ₘ'-map =
      bouquetSusp→
        (cofib-map→sphereBouquetMap↑ m (cofib-map f-c g-c m hₘ hₘ₊₁ hₘ-coh)
             ∘ preboundary.pre∂ C m)

    Hₘ∂ₘ''-map : SphereBouquet (suc m) (Fin (preboundary.An+1 C m)) → SphereBouquet (suc m) (Fin (snd D .fst (suc m)))
    Hₘ∂ₘ''-map x = BouquetFuns.CTB (suc m) (CW-fields.card D (suc m))
                    (CW-fields.α D (suc m)) (CW-fields.e D (suc m))
                     (cofib-map f-c g-c m hₘ hₘ₊₁ hₘ-coh
                       (suspFun (to m cofiber C)
                         (δ (suc m) C (preboundary.isoCofBouquetInv↑ C m x))))

    Hₘ∂ₘ'-map≡ : Hₘ∂ₘ'-map ≡ bouquetSusp→ Hₘ∂ₘ''-map
    Hₘ∂ₘ'-map≡ = cong bouquetSusp→
      (funExt λ x → cong (BouquetFuns.CTB (suc m) (CW-fields.card D (suc m))
                            (CW-fields.α D (suc m)) (CW-fields.e D (suc m))
                         ∘ cofib-map f-c g-c m hₘ hₘ₊₁ hₘ-coh)
                        (h x))
      where
      F = suspFun (to m cofiber C) ∘ (δ (suc m) C) ∘ preboundary.isoCofBouquetInv↑ C m

      h : (x : _)
        → suspFun (BouquetFuns.BTC m (card m) (α m) (e m))
            (Iso.inv sphereBouquetSuspIso (preboundary.pre∂ C m x))
        ≡ F x
      h x = cong (suspFun (BouquetFuns.BTC m (card m) (α m) (e m)))
                 (Iso.leftInv sphereBouquetSuspIso
                   (suspFun (preboundary.isoCofBouquet C m)
                    (F x)))
           ∙ sym (funExt⁻ (suspFun-comp (BouquetFuns.BTC m (card m) (α m) (e m))
                     (preboundary.isoCofBouquet C m)) (F x))
           ∙ (λ i → suspFun (funExt (BouquetIso-gen m (card m) (α m) (e m) .Iso.leftInv) i) (F x))
           ∙ funExt⁻ suspFun-id (F x)

    module _ where
      Hₘ∂ₘ'-map-merid⋆ : (a : _) → cong Hₘ∂ₘ'-map (λ i → inr (a , merid (ptSn (suc m)) i)) ≡ refl
      Hₘ∂ₘ'-map-merid⋆ a = cong (cong sphereBouquetSuspFun)
                             ((λ j → merid (cofib-map→sphereBouquetMap↑ m (cofib-map f-c g-c m hₘ hₘ₊₁ hₘ-coh)
                                             (preboundary.pre∂ C m (push a (~ j)))))
                            ∙ cong merid (cofib-map→sphereBouquetMap↑-pt m (cofib-map f-c g-c m hₘ hₘ₊₁ hₘ-coh) refl))

    susper :
        (x : SphereBouquet (suc m) (Fin (snd C .fst (suc m))))
      → Ω (SphereBouquet (suc (suc m)) (Fin (snd C .fst (suc m))) , inl tt) .fst
    susper (inl x) = refl
    susper (inr (a , x)) = push a ∙∙ (λ i → inr (a , σ (suc m) x i)) ∙∙ sym (push a)
    susper (push a i) j =
      (sym (∙∙lCancel (sym (push a)))
           ∙ λ i → push a
                ∙∙ (λ j → inr (a , σ∙ (suc m) .snd (~ i) j))
                ∙∙ sym (push a)) i j

    fspace-rewrite-lem :
         (f : SphereBouquet (suc (suc m)) (Fin (snd C .fst (suc m)))
           → SphereBouquet (suc (suc m)) (Fin (snd D .fst (suc m))))
         (p : f (inl tt) ≡ inl tt)
         (t : _)
      → f t ≡ fspace-rewrite-gen (f (inl tt)) (λ x i → f (susper x i)) t
    fspace-rewrite-lem f p t =
        cong f (sym (Iso.rightInv sphereBouquetSuspIso t))
       ∙ sym (lem (Iso.inv sphereBouquetSuspIso t))
      where
      main : (a : _) → cong f (susper a)
                      ≡ cong f (Bouquet→ΩBouquetSusp (Fin (snd C .fst (suc m)))
                                 (λ _ → S₊∙ (suc m))  a)
      main =
        Bouquet→Ω
          (cong f ∘ susper)
          (cong f ∘ Bouquet→ΩBouquetSusp (Fin (snd C .fst (suc m)))
            (λ _ → S₊∙ (suc m)))
            refl refl λ {_ → refl}
      lem : (t : _) → fspace-rewrite'' (f (inl tt)) (λ x i → f (susper x i)) t
                    ≡ f (Iso.fun sphereBouquetSuspIso t)
      lem north = refl
      lem south = refl
      lem (merid a i) j = main a j i

    fspace-rewrite-bouquetSusp : (f : _) (t : _)
      → bouquetSusp→ f t ≡  fspace-rewrite (λ x i → bouquetSusp→ f (susper x i)) t
    fspace-rewrite-bouquetSusp f = fspace-rewrite-lem (bouquetSusp→ f) refl

    Hₘ∂ₘ' : AbGroupHom (ℤ[A C ] (suc m)) (ℤ[A D ] (suc m))
    Hₘ∂ₘ' = bouquetDegree Hₘ∂ₘ'-map

    Hₘ∂ₘ≡Hₘ∂ₘ' : Hₘ∂ₘ ≡ Hₘ∂ₘ'
    Hₘ∂ₘ≡Hₘ∂ₘ' =
      sym (degreeComp
            (cofib-map→sphereBouquetMap↑ m
              (cofib-map f-c g-c m hₘ hₘ₊₁ hₘ-coh))
                (preboundary.pre∂ C m))
      ∙ degreeSusp _

    Hₘ₊₁ : AbGroupHom (ℤ[A C ] (suc m)) (ℤ[A D ] (suc (suc m)))
    Hₘ₊₁ = cofib-map→ℤ↑ (suc m) (cofib-map f-c g-c (suc m) hₘ₊₁ hₘ₊₂ hₘ₊₁-coh)

    ∂ₘ₊₁ : AbGroupHom (ℤ[A D ] (suc (suc m))) (ℤ[A D ] (suc m))
    ∂ₘ₊₁ = ∂ D (suc m)

    ∂ₘ₊₁Hₘ₊₁ : AbGroupHom (ℤ[A C ] (suc m)) (ℤ[A D ] (suc m))
    ∂ₘ₊₁Hₘ₊₁ = compGroupHom Hₘ₊₁ ∂ₘ₊₁

    ∂ₘ₊₁Hₘ₊₁'-map = (preboundary.pre∂ D (suc m)
        ∘ cofib-map→sphereBouquetMap↑ (suc m)
           (cofib-map f-c g-c (suc m) hₘ₊₁ hₘ₊₂ hₘ₊₁-coh))

    ∂ₘ₊₁Hₘ₊₁''-map = preboundary.isoSuspBouquet D (suc m)
                   ∘ suspFun (preboundary.isoCofBouquet D (suc m))
                   ∘ suspFun (to suc m cofiber D)
                   ∘ δ (suc (suc m)) D
                   ∘ cofib-map f-c g-c (suc m) hₘ₊₁ hₘ₊₂ hₘ₊₁-coh
                  ∘  (suspFun (BouquetIso-gen (suc m) (card (suc m)) (α (suc m)) (e (suc m)) .Iso.inv))
                  ∘ (Iso.inv sphereBouquetSuspIso)

    ∂ₘ₊₁Hₘ₊₁''-map-pt : (x : _) → cong (λ y → ∂ₘ₊₁Hₘ₊₁''-map (inr (x , y))) (merid (ptSn (suc m))) ≡ refl
    ∂ₘ₊₁Hₘ₊₁''-map-pt x i j =
      (preboundary.isoSuspBouquet D (suc m)
                   ∘ suspFun (preboundary.isoCofBouquet D (suc m))
                   ∘ suspFun (to suc m cofiber D)
                   ∘ δ (suc (suc m)) D
                   ∘ cofib-map f-c g-c (suc m) hₘ₊₁ hₘ₊₂ hₘ₊₁-coh)
          (merid (preBTC (suc m) (card (suc m)) (α (suc m)) (e (suc m)) x .snd i) j) 

    ∂ₘ₊₁Hₘ₊₁'-map≡ : ∂ₘ₊₁Hₘ₊₁'-map ≡ ∂ₘ₊₁Hₘ₊₁''-map
    ∂ₘ₊₁Hₘ₊₁'-map≡ i x =
      (preboundary.isoSuspBouquet D (suc m)
                   ∘ suspFun (preboundary.isoCofBouquet D (suc m))
                   ∘ suspFun (to suc m cofiber D)
                   ∘ δ (suc (suc m)) D)
        (Iso.leftInv (BouquetIso-gen (suc (suc m))
          (preboundary.An+1 D (suc m)) (preboundary.αn+1 D (suc m))
          (snd D .snd .snd .snd (suc (suc m))))
            (cofib-map f-c g-c (suc m) hₘ₊₁ hₘ₊₂ hₘ₊₁-coh
              (suspFun (BouquetIso-gen (suc m)
                         (card (suc m)) (α (suc m)) (e (suc m)) .Iso.inv)
                (Iso.inv sphereBouquetSuspIso x))) i)

    ∂ₘ₊₁Hₘ₊₁' : AbGroupHom (ℤ[A C ] (suc m)) (ℤ[A D ] (suc m))
    ∂ₘ₊₁Hₘ₊₁' =
      bouquetDegree {m = snd C .fst (suc m)}
         (preboundary.pre∂ D (suc m)
        ∘ cofib-map→sphereBouquetMap↑ (suc m)
           (cofib-map f-c g-c (suc m) hₘ₊₁ hₘ₊₂ hₘ₊₁-coh))


    module _ (F : SphereBouquet (suc (suc m)) (Fin (snd C .fst (suc m)))
               → SphereBouquet (suc (suc m)) (Fin (snd D .fst (suc m))))
              where
      ∈Im-fspace-rewrite : Σ[ f ∈ f-space-back-gen (F (inl tt)) ]
         ((y : _) → F y ≡ fspace-rewrite-gen (F (inl tt)) f y)
      fst ∈Im-fspace-rewrite x = cong F (susper x)
      snd ∈Im-fspace-rewrite (inl x) = refl
      snd ∈Im-fspace-rewrite (inr (a , north)) = cong F (sym (push a))
      snd ∈Im-fspace-rewrite (inr (a , south)) = cong F ((λ i → inr (a , merid (ptSn (suc m)) (~ i))) ∙ sym (push a))
      snd ∈Im-fspace-rewrite (inr (a , merid b i)) j =
        hcomp (λ k → λ {(i = i0) → F (push a (~ j ∨ ~ k))
                       ; (i = i1) → F (compPath-filler (λ i₁ → inr (a , merid (ptSn (suc m)) (~ i₁)))
                                                        (sym (push a)) k j)
                       ; (j = i0) → F (inr (a , merid b i))
                       ; (j = i1) → F (doubleCompPath-filler
                                         (push a)
                                         (λ j → inr (a , σ (suc m) b j))
                                         (sym (push a)) k i)})
         (F (inr (a , compPath-filler (merid b) (sym (merid (ptSn (suc m)))) j i)))
      snd ∈Im-fspace-rewrite (push a i) j = F (push a (i ∧ ~ j))

    ∂ₘ₊₁Hₘ₊₁≡∂ₘ₊₁Hₘ₊₁' : ∂ₘ₊₁Hₘ₊₁ ≡ ∂ₘ₊₁Hₘ₊₁'
    ∂ₘ₊₁Hₘ₊₁≡∂ₘ₊₁Hₘ₊₁' = 
      sym (degreeComp
            (preboundary.pre∂ D (suc m))
            (cofib-map→sphereBouquetMap↑ (suc m)
             (cofib-map f-c g-c (suc m) hₘ₊₁ hₘ₊₂ hₘ₊₁-coh)))

    ∂ₘ₊₁Hₘ₊₁+Hₘ∂ₘ : AbGroupHom (ℤ[A C ] (suc m)) (ℤ[A D ] (suc m))
    ∂ₘ₊₁Hₘ₊₁+Hₘ∂ₘ = addGroupHom _ _ ∂ₘ₊₁Hₘ₊₁ Hₘ∂ₘ

    fₘ₊₁ gₘ₊₁ : AbGroupHom (ℤ[A C ] (suc m)) (ℤ[A D ] (suc m))
    fₘ₊₁ = prefunctoriality.chainFunct f-c (suc m)
    gₘ₊₁ = prefunctoriality.chainFunct g-c (suc m)

    bouquetFunct-f = prefunctoriality.bouquetFunct f-c (suc m)
    bouquetFunct-g = prefunctoriality.bouquetFunct g-c (suc m)

    fₘ₊₁-gₘ₊₁ : AbGroupHom (ℤ[A C ] (suc m)) (ℤ[A D ] (suc m))
    fₘ₊₁-gₘ₊₁ = subtrGroupHom _ _ fₘ₊₁ gₘ₊₁


    open import Cubical.Foundations.Path
    Square→compPath' : ∀ {ℓ} {A : Type ℓ} {x y z w : A}
      {p : x ≡ y} {q : y ≡ z} {r : x ≡ w} {s : w ≡ z}
      → Square p s r q
      → p ∙ q ≡ r ∙ s
    Square→compPath' {p = p} {q = q} {r = r} {s = s} sq i j =
      hcomp (λ k → λ {(i = i0) → compPath-filler' p q k j
                     ; (j = i0) → p (~ i ∧ ~ k)
                     ; (j = i1) → s (~ i ∨ k)})
            (sq j (~ i))

    open import spherebouquet
    open import Cubical.Data.Int
    lem' : (x : _) (a : _)
      → Square (λ i → ∂ₘ₊₁Hₘ₊₁''-map (inr (x , merid a i)))
               (λ i → bouquetSusp→ bouquetFunct-g (inr (x , merid a (~ i))))
               (λ i → bouquetSusp→ bouquetFunct-f (inr (x , merid a i)))
               (λ i → bouquetSusp→ Hₘ∂ₘ''-map (inr (x , merid a i)))
    lem' x a i j = baha (G (inr (x , a))) i j
      where
      Corr = SuspBouquet→Bouquet (Fin (snd D .fst (suc m))) (λ _ → S₊∙ (suc m))
      F : (D : CW) (m : ℕ) → cofiber m D
                  → SphereBouquet m (Fin (CW-fields.card D m))
      F D m = BouquetIso-gen m
           (CW-fields.card D m)
           (CW-fields.α D m)
           (CW-fields.e D m) .Iso.fun

      G = BouquetIso-gen (suc m)
            (CW-fields.card C (suc m))
            (CW-fields.α C (suc m))
            (CW-fields.e C (suc m)) .Iso.inv

      baha-inr : (x : _) (i j k : I) → Bouquet (Fin (snd D .fst (suc m))) (λ c → Susp∙ (fst (S₊∙ (suc m))))
      baha-inr x i j k =
        hfill (λ k → λ {(i = i0) → Corr (suspFun (F D (suc m)) (suspFun (to (suc m) cofiber D)
                                      (δ (suc (suc m)) D
                                       (doubleCompPath-filler
                                        (push (f (suc (suc m)) x))
                                        (λ j → inr (hₘ₊₂ x j))
                                        (sym (push (g (suc (suc m)) x))) k j))))
                       ; (i = i1) → Corr (merid (F D (suc m) (inr (g (suc (suc m)) x))) (~ j ∨ ~ k))
                       ; (j = i0) → Corr (merid (F D (suc m) (inr (f (suc (suc m)) x))) (i ∨ ~ k))
                       ; (j = i1) → Corr (merid (F D (suc m) (inr (g (suc (suc m)) x))) (~ k))})
              (inS (inl tt))
              k

      baha : (l : cofiber (suc m) C)
        → Square (λ j → Corr (suspFun (F D (suc m)) (suspFun (to (suc m) cofiber D)
                                (δ (suc (suc m)) D ((cofib-map f-c g-c (suc m) hₘ₊₁ hₘ₊₂ hₘ₊₁-coh
                                 (merid l j)))))))
          (λ j → Corr (merid (F D (suc m) (prefunctoriality.fn+1/fn g-c (suc m) l)) (~ j)))
          (λ j → Corr (merid (F D (suc m) (prefunctoriality.fn+1/fn f-c (suc m) l)) j))
           λ j → Corr (merid (F D (suc m) (cofib-map f-c g-c m hₘ hₘ₊₁ hₘ-coh
                       (suspFun (to m cofiber C)
                         (δ-pre (CW↪ C (suc m)) l)))) j)
      baha (inl x) = refl
      baha (inr x) i j = baha-inr x i j i1
      baha (push a k) i j =
        hcomp (λ r → λ {(i = i0) → Corr (suspFun (F D (suc m)) (suspFun (to (suc m) cofiber D)
                                      (δ (suc (suc m)) D
                                       (cofib-map-filler f-c g-c (suc m) hₘ₊₁ hₘ₊₂ hₘ₊₁-coh a j k r))))
                       ; (i = i1) → i00 r j k
                       ; (j = i0) → j00 r i k
                       ; (j = i1) → (j01 r i k)
                       ; (k = i0) → Corr (merid (F D (suc m) (to suc m cofiber D (hₘ₊₁ a j))) (~ r ∧ ~ i))
                       })
          (hcomp (λ r → λ {(i = i0) → ((cong-∙∙ (λ x → cong Corr (merid (F D (suc m) x)))
                                                    (push (f (suc m) a)) (λ j → inr (hₘ₊₁ a j)) refl)
                                          ◁ helpp5 _ (λ k r → Corr (merid (F D (suc m) (push (f (suc m) a) k)) r))
                                                   _ (λ j r → Corr (merid (F D (suc m) (inr (hₘ₊₁ a j))) r)))
                                             r j k
                          ; (i = i1) → Corr (merid (F D (suc m)
                                            (compPath-filler (push (g (suc m) a))
                                              (λ j₂ → inr (g-hom (suc m) a j₂)) r j)) k)
                          ; (j = i0) → Corr (merid (F D (suc m) (push (f (suc m) a) (~ k))) (~ i ∧ r))
                          ; (k = i0) → Corr (merid (F D (suc m) (inr (hₘ₊₁ a j))) (~ i ∧ r))
                          ; (k = i1) → inl tt})
             (hcomp (λ r → λ {(i = i0) → Corr (merid (F D (suc m)
                                             ((push (f (suc m) a)
                                           ∙∙ (λ j → inr (hₘ₊₁ a j))
                                           ∙∙ λ k → push (g (suc m) a) (~ k ∨ r)) j)) k)
                          ; (i = i1) → Corr (merid (F D (suc m) (push (cellMap.map g-c (suc m) a) (j ∧ r))) k)
                          ; (j = i0) → inl tt
                          ; (j = i1) → btm1-fill i k r
                          ; (k = i0) → inl tt -- inl tt -- inl tt
                          ; (k = i1) → inl tt -- inl tt -- inl tt
                          })
                    (help6 (λ i k → btm1-fill i k i0) j i k)))
        where -- r j k
        open import Cubical.Foundations.Path

        btm1-fill : (i j k : I) → _
        btm1-fill i j k = hfill (λ k → λ {(i = i0) → Corr (merid (F D (suc m) (push (g (suc m) a) k)) j)
                         ; (i = i1) → Corr (merid (F D (suc m) (push (g (suc m) a) k)) j)
                         ; (j = i0) → inl tt
                         ; (j = i1) → inl tt})
                  (inS (Corr (merid (F D (suc m)
                          ((push (f (suc m) a) ∙∙ (λ i → inr (hₘ₊₁ a i)) ∙∙ sym (push (g (suc m) a))) j)) i))) k

        btm1 : (i j : I) → _
        btm1 i j =
          hcomp (λ k → λ {(i = i0) → Corr (merid (F D (suc m) (inr (hₘ₊₁ a i1))) (j ∨ k))
                         ; (i = i1) → Corr (merid (F D (suc m) (inr (g-hom (suc m) a k))) j) 
                         ; (j = i0) → Corr (merid (F D (suc m) (inr (hₘ₊₁ a i1))) (~ i ∧ k))
                         ; (j = i1) → inl tt})
           (btm1-fill i j i1)
        

        helpp : ∀ {A : Type} {x : A} (p : x ≡ x) (r : refl ≡ p)
          → Cube (λ i r → p (~ i ∧ ~ r)) (λ i r → p (i ∨ ~ r))
                  refl
                  refl
                  (λ j k → r (~ j) (~ k))
                  λ j k → r j k
        helpp = J> refl

        helpp2 : ∀ {A : Type} {x : A} (p : x ≡ x) (r : refl ≡ p)
          → Cube (λ _ _ → x) (λ j r → p (~ j ∨ ~ r))
                  (λ _ _ → x) (λ k r → p (~ r ∧ k))
                  (λ k j → r j k) λ k j → r k (~ j)
        helpp2 = J> refl

        helpp3 : ∀ {A : Type} {x : A} (y : A) (p q : x ≡ y) (r : p ≡ q)
          → Cube (λ k r' → p (k ∧ ~ r')) (λ k r' → r k (~ r'))
                  (λ j r → p (~ r ∧ j)) (λ j r' → r j (~ r'))
                  (λ j k → p (k ∨ j)) λ _ _ → x
        helpp3 = J> (J> refl)

        helpp4 : ∀ {A : Type} {x : A} (q : x ≡ x) (s : refl ≡ q)
          → Cube  (λ i j → s j i) (λ i r → q (~ r))
                  (λ j r → s j (~ r)) (λ j r → s j (~ r))
                  (λ _ _ → x)
                  λ j i → s (~ j) i
        helpp4 = J> refl

        help6 : ∀ {A : Type} {x : A} (p : Square (refl {x = x}) refl refl refl)
          → Cube (λ _ _ → x) p (λ j k → p k j) (λ _ _ → x) (λ _ _ → x) λ _ _ → x
        help6 p = (λ j i k → p k (~ i ∧ j)) ▷ (sym≡flipSquare (λ i j → p j i))

        helpp5 : ∀ {A : Type} {x : A} (p : x ≡ x) (s : refl ≡ p) (q : x ≡ x) (r : p ≡ q)
          → Cube (λ i j → (s ∙∙ r ∙∙ refl) i j) (λ _ _ → x)
                  (λ r' k → s (~ k) r') (λ r' k → q (r' ∨ k))
                  (λ r' j → r j r') λ _ _ → x
        helpp5 = J> (J> (sym (rUnit refl)))

        j00 : (r i k : I) → _
        j00 r i k =
          hcomp (λ j → λ {(i = i0) → Corr (merid (F D (suc m) (inr (f-hom (suc m) a (k ∧ j)))) (~ r))
                       ; (i = i1) → inl tt
                       ; (r = i0) → Corr (merid (F D (suc m) (push (f (suc m) a) (~ k))) (~ i))
                       ; (r = i1) → Corr (merid (F D (suc m) ((compPath-filler (push (f (suc m) a)) (λ i → inr (f-hom (suc m) a i)) j) k)) i)
                       ; (k = i0) → Corr (merid (F D (suc m) (inr (CW↪ D (suc m) (f (suc m) a)))) (~ i ∧ ~ r))
                       ; (k = i1) → Corr (merid (F D (suc m) (inr (f-hom (suc m) a j))) (i ∨ ~ r))
                       })
            (helpp (cong Corr (merid (F D (suc m) (inr (CW↪ D (suc m) (f (suc m) a))))))
                   (λ k → cong Corr (merid (F D (suc m) (push (f (suc m) a) k)))) k i r)

        j01 : (r i k : I) → _
        j01 r i k =
          hcomp (λ j → λ {(i = i0) → helpp3 _ (λ k → Corr (merid (F D (suc m)
                                                       (inr (CW↪ D (suc m) (g (suc m) a)))) k))
                                               _ (λ i k → Corr (merid (F D (suc m)
                                                       (inr (g-hom (suc m) a i))) k))
                                               j k r
                       ; (i = i1) → Corr (merid (F D (suc m) (inr (g-hom (suc m) a j))) (~ r ∧ k))
                       ; (r = i1) → Corr (merid (F D (suc m)
                                      (doubleCompPath-filler (push (f (suc m) a)) (λ j → inr (hₘ₊₁ a j)) (sym (push (g (suc m) a))) i1 k)) i)
                       ; (k = i0) → Corr (merid (F D (suc m) (inr (CW↪ D (suc m) (g (suc m) a)))) ((~ i ∧ j) ∧ ~ r))
                       ; (k = i1) → Corr (merid (F D (suc m) (inr (g-hom (suc m) a j))) (~ r)) 
                       })
                 (hcomp (λ j → λ {(i = i0) → Corr (merid (F D (suc m) (push (g (suc m) a) j)) (k ∧ ~ r))
                       ; (i = i1) → Corr (merid (F D (suc m) (push (g (suc m) a) j)) (k ∧ ~ r))
                       ; (r = i1) → Corr (merid (F D (suc m)
                                      (doubleCompPath-filler (push (f (suc m) a)) (λ j → inr (hₘ₊₁ a j)) (sym (push (g (suc m) a))) j k)) i)
                       ; (k = i0) → Corr (merid (F D (suc m) (push (f (suc m) a) (~ j ∧ r))) i)
                       ; (k = i1) → helpp4 _ (λ i j → Corr (merid (F D (suc m) (push (g (suc m) a) i)) j)) j i r
                       })
                     (Corr (merid (F D (suc m)
                                      (doubleCompPath-filler (push (f (suc m) a))
                                                             (λ j → inr (hₘ₊₁ a j))
                                                             (sym (push (g (suc m) a))) (~ r) k)) i)))
        i00 : (r i k : I) → _
        i00 r j k =
          hcomp (λ i → λ { (r = i0) → Corr (merid (F D (suc m) (compPath-filler (push (g (suc m) a)) (λ j → inr (g-hom (suc m) a j)) i j)) k)
                       ; (r = i1) → Corr (merid (F D (suc m) (compPath-filler (push (g (suc m) a)) (λ j → inr (g-hom (suc m) a j)) i k)) (~ j))
                       ; (j = i0) → inl tt
                       ; (j = i1) → Corr (merid (F D (suc m) (inr (g-hom (suc m) a i))) (~ r ∧ k))
                       ; (k = i0) → inl tt
                       ; (k = i1) → Corr (merid (F D (suc m) (inr (g-hom (suc m) a i))) (~ j ∨ ~ r))
                       })
            (helpp2 (cong Corr (merid (F D (suc m) (inr (CW↪ D (suc m) (g (suc m) a))))))
                    (λ k → cong Corr (merid (F D (suc m) (push (g (suc m) a) k)))) k j r)

    lem : (x : _) (a : _)
      → Square (λ i → ∂ₘ₊₁Hₘ₊₁''-map (inr (x , σ (suc m) a i)))
               (λ i → bouquetSusp→ bouquetFunct-g (inr (x , σ (suc m) a (~ i))))
               (λ i → bouquetSusp→ bouquetFunct-f (inr (x , σ (suc m) a i)))
               (λ i → bouquetSusp→ Hₘ∂ₘ''-map (inr (x , σ (suc m) a i)))
    lem x a i j =
      hcomp (λ k → λ { (i = i0) → cong-∙ (λ y → ∂ₘ₊₁Hₘ₊₁''-map (inr (x , y))) (merid a) (sym (merid (ptSn (suc m)))) (~ k) j
                       ; (i = i1) → cong-∙ (λ y → bouquetSusp→ bouquetFunct-g (inr (x , y)))
                                           (merid a) (sym (merid (ptSn (suc m)))) (~ k) (~ j)
                       ; (j = i0) → cong-∙ (λ y → bouquetSusp→ bouquetFunct-f (inr (x , y)))
                                           (merid a) (sym (merid (ptSn (suc m)))) (~ k) i
                       ; (j = i1) → cong-∙ (λ y → bouquetSusp→ Hₘ∂ₘ''-map (inr (x , y))) (merid a) (sym (merid (ptSn (suc m)))) (~ k) i})
       (hcomp (λ k → λ { (i = i0) → kill-refl (cong (λ y → ∂ₘ₊₁Hₘ₊₁''-map (inr (x , y))) (merid a)) _
                                                (cong sym (sym (∂ₘ₊₁Hₘ₊₁''-map-pt x))) (~ k) j
                       ; (i = i1) → kill-refl (cong (λ y → bouquetSusp→ bouquetFunct-g (inr (x , y))) (merid a)) _
                                               (cong sym (sym (bouquetSusp→· x bouquetFunct-g refl))) (~ k) (~ j)
                       ; (j = i0) → kill-refl (cong (λ y → bouquetSusp→ bouquetFunct-f (inr (x , y))) (merid a)) _
                                               (cong sym (sym (bouquetSusp→· x bouquetFunct-f refl))) (~ k) i
                       ; (j = i1) → kill-refl (cong (λ y → bouquetSusp→ Hₘ∂ₘ''-map (inr (x , y))) (merid a)) _
                                               (cong sym (sym (bouquetSusp→· x Hₘ∂ₘ''-map refl))) (~ k) i })
              (lem' x a i j))
     where
     kill-refl : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y) (q : y ≡ y)
       → (refl ≡ q) → p ∙ q ≡ p
     kill-refl p = J> (sym (rUnit p))

    main-coh*ₗ main-coh*ᵣ : (SphereBouquet (suc m) (Fin (snd C .fst (suc m))) , inl tt)
                       →∙ Ω (SphereBouquet (suc (suc m)) (Fin (preboundary.An D (suc m))) , inl tt)
    main-coh*ₗ = const∙ _ _
    fst main-coh*ᵣ x = ((λ i → bouquetSusp→ bouquetFunct-f (susper x (~ i)))
                           ∙∙ cong ∂ₘ₊₁Hₘ₊₁''-map (susper x)
                           ∙∙ (λ i → bouquetSusp→ Hₘ∂ₘ''-map (susper x i)))
                    ∙ λ i → bouquetSusp→ bouquetFunct-g (susper x i)
    snd main-coh*ᵣ = sym (rUnit _) ∙ sym (rUnit _)

    main-coh* : Path (SphereBouquet (suc m) (Fin (snd C .fst (suc m))) → _)
                     (λ x → refl)
                     (λ x → ((λ i → bouquetSusp→ bouquetFunct-f (susper x (~ i)))
                           ∙∙ cong ∂ₘ₊₁Hₘ₊₁''-map (susper x)
                           ∙∙ (λ i → bouquetSusp→ Hₘ∂ₘ''-map (susper x i)))
                           ∙ (λ i → bouquetSusp→ bouquetFunct-g (susper x i)))
    main-coh* = funExt λ x
      → sym (Bouquet→Const main-coh*ᵣ
            (λ y → cong₂ _∙_
            (λ k → (λ i →  bouquetSusp→ bouquetFunct-f (dc y (~ k) (~ i)))
                 ∙∙ (λ i → ∂ₘ₊₁Hₘ₊₁''-map (dc y (~ k) i))
                 ∙∙ λ i → bouquetSusp→ Hₘ∂ₘ''-map (dc y (~ k) i))
               (λ j i → bouquetSusp→ bouquetFunct-g (dc y (~ j) i))
              ∙ lema _ _ _ _ _ _ _ (lem (fst y) (snd y)) ) x)
      where
      dc : (y : Σ (Fin (snd C .fst (suc m))) (λ c → S₊ (suc m)))
        → I → I
        → SphereBouquet (suc (suc m)) (Fin (prefunctoriality.An g-c (suc m)))
      dc y i j =
        doubleCompPath-filler
             (push (fst y))
             (λ i₁ → inr (fst y , toSusp (S₊∙ (suc m)) (snd y) i₁))
             (sym (push (fst y))) i j


      lema : ∀ {ℓ} {A : Type ℓ} {x : A}
                    (y : A) (p : x ≡ y)
                    (z : A) (q : x ≡ z)
                    (w : A) (s : z ≡ w)
                    (r : y ≡ w)
                 → Square p s q r
                 → (sym q ∙∙ p ∙∙ r) ∙ sym s ≡ refl
                    
      lema = J> (J> (J> λ r p
        → sym (rUnit _) ∙ sym (lUnit r) ∙ λ j i → p i (~ j)))

    open import Cubical.Foundations.Path

    main-coh : (x : _)
      → Square (λ i → ∂ₘ₊₁Hₘ₊₁''-map (susper x i))
               (λ i → bouquetSusp→ bouquetFunct-g (susper x (~ i)))
               (λ i → bouquetSusp→ bouquetFunct-f (susper x i))
               (λ i → bouquetSusp→ Hₘ∂ₘ''-map (susper x i))
    main-coh x =
        pp ▷ sym ((lUnit _
                ∙ (cong (_∙ (λ i₁ → bouquetSusp→ bouquetFunct-g (susper x (~ i₁))))
                        (funExt⁻ main-coh* x) ∙ sym (assoc (pp i1) _ _)
                  ∙ (cong (pp i1 ∙_) (rCancel _))
                  ∙ sym (rUnit _))))
       where
       pp = doubleCompPath-filler (λ i → bouquetSusp→ bouquetFunct-f (susper x (~ i)))
                                  (cong ∂ₘ₊₁Hₘ₊₁''-map (susper x))
                                  λ i → bouquetSusp→ Hₘ∂ₘ''-map (susper x i)

    mainId : ∂ₘ₊₁Hₘ₊₁+Hₘ∂ₘ ≡ fₘ₊₁-gₘ₊₁
    mainId = cong₂ (addGroupHom (ℤ[A C ] (suc m)) (ℤ[A D ] (suc m)))
                   (∂ₘ₊₁Hₘ₊₁≡∂ₘ₊₁Hₘ₊₁'
                   ∙ cong bouquetDegree
                      (∂ₘ₊₁Hₘ₊₁'-map≡ ∙ funExt (fspace-rewrite-lem ∂ₘ₊₁Hₘ₊₁''-map refl)))
                   (Hₘ∂ₘ≡Hₘ∂ₘ'
                 ∙ cong bouquetDegree
                     (funExt λ t → funExt⁻ (Hₘ∂ₘ'-map≡) t
                       ∙ fspace-rewrite-lem (bouquetSusp→ Hₘ∂ₘ''-map) refl t))
           ∙ sym (bouquetDeg+ (cong ∂ₘ₊₁Hₘ₊₁''-map ∘ susper)
                              (cong (bouquetSusp→ Hₘ∂ₘ''-map) ∘ susper))
           ∙ (cong bouquetDegree
               (cong fspace-rewrite
                (funExt (λ x → Square→compPath' (main-coh x))))
           ∙ bouquetDeg+
               (cong (bouquetSusp→ bouquetFunct-f) ∘ susper)
               (sym ∘ cong (bouquetSusp→ bouquetFunct-g) ∘ susper))
           ∙ cong₂ (addGroupHom _ _)
                   ((cong bouquetDegree
                        (sym (funExt (∈Im-fspace-rewrite (bouquetSusp→ bouquetFunct-f) .snd))))
                     ∙ sym (degreeSusp bouquetFunct-f))
                   (bouquetDegInv (∈Im-fspace-rewrite (bouquetSusp→ bouquetFunct-g) .fst)
                     ∙ cong (negGroupHom (ℤ[A C ] (suc m)) (ℤ[A D ] (suc m)))
                     (cong bouquetDegree
                       (sym (funExt (∈Im-fspace-rewrite (bouquetSusp→ bouquetFunct-g) .snd)))
                     ∙ sym (degreeSusp bouquetFunct-g)))
