{-# OPTIONS --cubical --lossy-unification #-}
module EilenbergSteenrod.ESAdditivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int renaming (_+_ to _+ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Fin.Inductive
open import Cubical.Data.Sum as ⊎

open import Cubical.CW.Base
open import Cubical.CW.ChainComplex

open import Cubical.HITs.Pushout
open import Cubical.HITs.Wedge

open import Cubical.Algebra.ChainComplex
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.AbGroup.Instances.DirectProduct

open import EilenbergSteenrod.CWWedgeSum
open import EilenbergSteenrod.CWWedgeSum

open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd

open import Cubical.CW.Map
open import Cubical.Data.Sequence.Base
open import Cubical.Data.FinSequence.Base

cellMap→finCellMap : ∀ {ℓ ℓ'} (m : ℕ) {C : CWskel ℓ} {D : CWskel ℓ'} (ϕ : cellMap C D) → finCellMap m C D
FinSequenceMap.fmap (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.map ϕ x
FinSequenceMap.fcomm (cellMap→finCellMap m ϕ) (x , p) = SequenceMap.comm ϕ x

dirProdHom : ∀ {ℓG ℓG' ℓH ℓH'} {G : Group ℓG} {G' : Group ℓG'}
  {H : Group ℓH} {H' : Group ℓH'} → GroupHom G H → GroupHom G' H'
  → GroupHom (DirProd G G') (DirProd H H')
fst (dirProdHom ϕ ψ) (g , g') = fst ϕ g , fst ψ g'
snd (dirProdHom ϕ ψ) =
  makeIsGroupHom (λ x y → ΣPathP ((IsGroupHom.pres· (snd ϕ) _ _)
                                 , (IsGroupHom.pres· (snd ψ) _ _)))


dirProdFst : ∀ {ℓG ℓH} {G : Group ℓG} {H : Group ℓH}
  → GroupHom (DirProd G H) G
fst dirProdFst = fst
snd dirProdFst = makeIsGroupHom λ _ _ → refl

dirProdSnd : ∀ {ℓG ℓH} {G : Group ℓG} {H : Group ℓH}
  → GroupHom (DirProd G H) H
fst dirProdSnd = snd
snd dirProdSnd = makeIsGroupHom λ _ _ → refl


open ChainComplex
ChainComplexProd : ∀ {ℓ ℓ'} (C : ChainComplex ℓ) (D : ChainComplex ℓ')
  → ChainComplex (ℓ-max ℓ ℓ')
chain (ChainComplexProd C D) n = dirProdAb (chain C n) (chain D n)
bdry (ChainComplexProd C D) n = dirProdHom (bdry C n) (bdry D n)
bdry²=0 (ChainComplexProd C D) n =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt λ x → ΣPathP ((funExt⁻ (cong fst (bdry²=0 C n)) (fst x))
                         , (funExt⁻ (cong fst (bdry²=0 D n)) (snd x))))

agreeOnℤFinGenerator→≡' : ∀ {ℓ} {n : ℕ} {G : AbGroup ℓ}
  → {ϕ ψ : AbGroupHom (ℤ[Fin n ]) G}
  → ((x : _) → fst ϕ (ℤFinGenerator x) ≡ fst ψ (ℤFinGenerator x))
  → ϕ ≡ ψ
agreeOnℤFinGenerator→≡' {n = n} {G = G} {ϕ} {ψ} idr =
  Σ≡Prop (λ _ → isPropIsGroupHom _ _)
   (funExt
    (elimPropℤFin _ _ (λ _ → AbGroupStr.is-set (snd G) _ _)
    (IsGroupHom.pres1 (snd ϕ) ∙ sym (IsGroupHom.pres1 (snd ψ)))
    idr
    (λ f g p q → IsGroupHom.pres· (snd ϕ) f g
                 ∙∙ cong₂ (AbGroupStr._+_ (snd G)) p q
                 ∙∙ sym (IsGroupHom.pres· (snd ψ) f g))
    λ f p → IsGroupHom.presinv (snd ϕ) f
           ∙∙ (λ i → AbGroupStr.-_ (snd G) (p i))
           ∙∙ sym (IsGroupHom.presinv (snd ψ) f)))

open import Cubical.Data.Nat.Order.Inductive

ℤFinProductGenerator : ∀ {n m : ℕ} (t : Fin (n +ℕ m))
  → (Σ[ t' ∈ Fin n ] (Iso.fun (fst (ℤFinProduct n m)) (ℤFinGenerator t) ≡ ((ℤFinGenerator t') , λ _ → 0)))
   ⊎ (Σ[ t' ∈ Fin m ] (Iso.fun (fst (ℤFinProduct n m)) (ℤFinGenerator t) ≡ ((λ _ → 0) , ℤFinGenerator t')))
ℤFinProductGenerator {n = n} {m = m} t = help (fst t ≟ᵗ n)
  where
  help : (Trichotomyᵗ (fst t) n) → _
  help (lt x) = inl ((fst t , x) , ΣPathP ((funExt main) , funExt λ w → mainR w))
    where
    main : (w : _) → fst (Iso.fun (ℤFinProductIso n m) (ℤFinGenerator t)) w ≡
      ℤFinGenerator (fst t , x) w
    main w with (fst t ≟ᵗ fst w)
    ... | lt x = refl
    ... | eq x = refl
    ... | gt x = refl

    mainR : (x₁ : Fin m) {q : (n +ℕ fst x₁) <ᵗ (n +ℕ m)} → ℤFinGenerator t (n +ℕ fst x₁ , q) ≡ pos 0
    mainR x₁ {q = q} with (fst t ≟ᵗ (n +ℕ fst x₁))
    ... | lt x₁ = refl
    ... | eq r = ⊥.rec (¬squeeze (x , (<→<ᵗ ((fst x₁)
               , ((+-suc (fst x₁) n ∙ cong suc (+-comm (fst x₁) n) ) ∙ sym (cong suc r))))))
    ... | gt x₁ = refl
  help (eq x) = inr (k , ΣPathP (funExt ML , funExt MR))
    where
    k : Fin m
    k = ((fst t ∸ n) , (subst ((fst t ∸ n) <ᵗ_)
       (∸+ m n) (<→<ᵗ (<-∸-< (fst t) (n +ℕ m) n (<ᵗ→< (snd t)) ((fst (<ᵗ→< (snd t)))
       , (cong (λ n → fst (<ᵗ→< (snd t)) +ℕ suc n) (sym x) ∙ snd (<ᵗ→< (snd t))))))))

    ML : (w : Fin n) →
      fst (Iso.fun (ℤFinProductIso n m) (ℤFinGenerator t)) w ≡ pos 0
    ML w with (fst t ≟ᵗ fst w)
    ... | lt x = refl
    ... | eq q = ⊥.rec (¬m<ᵗm (subst (_<ᵗ n) (sym q ∙ x) (snd w)))
    ... | gt x = refl

    MR : (x₁ : Fin m) →
      ℤFinGenerator t (n +ℕ fst x₁ , <→<ᵗ (<-k+ (<ᵗ→< (snd x₁)))) ≡
      ℤFinGenerator k x₁
    MR w with (fst t ≟ᵗ (n +ℕ fst w)) | ((fst t ∸ n) ≟ᵗ fst w)
    ... | lt x | lt x₁ = refl
    ... | lt p | eq q =
      ⊥.rec (¬m<ᵗm (subst (fst t <ᵗ_ ) (cong (n +ℕ_) (sym (sym (n∸n (fst t)) ∙ cong (fst t ∸_) x ∙ q)) ∙ +-comm n zero ∙ sym x) p))
    ... | lt x | gt x₁ = refl
    ... | eq p | lt q =
      ⊥.rec (subst ((fst t ∸ n) <ᵗ_) (sym (sym (n∸n n) ∙ cong (λ x → x ∸ n) (sym x ∙ p) ∙ ∸+ _ _)) q)
    ... | eq x | eq x₁ = refl
    ... | eq p | gt q = ⊥.rec (subst (fst w <ᵗ_) (cong (fst t ∸_) (sym x) ∙ n∸n (fst t)) q)
    ... | gt x | lt x₁ = refl
    ... | gt p | eq q =
      ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst t) (cong (n +ℕ_)
        (sym q ∙ cong (fst t ∸_) (sym x) ∙ n∸n (fst t)) ∙ +-comm n zero ∙ sym x) p))
    ... | gt x | gt x₁ = refl
  help (gt x) = inr (k , ΣPathP ((funExt ML) , (funExt MR)))
    where
    k : Fin m
    k = ((fst t ∸ n)
      , <→<ᵗ (≤-trans (<-∸-< (fst t) (n +ℕ m) n (<ᵗ→< (snd t)) (<ᵗ→< (<ᵗ-trans x (snd t)))) (zero , (∸+ m n))))

    ML : (w : Fin n) →
      fst (Iso.fun (ℤFinProductIso n m) (ℤFinGenerator t)) w ≡ pos 0
    ML w with (fst t ≟ᵗ fst w)
    ... | lt x = refl
    ... | eq q = ⊥.rec (¬m<ᵗm (<ᵗ-trans (subst (n <ᵗ_) q x) (snd w)))
    ... | gt x = refl

    MR : (x₁ : Fin m) →
      ℤFinGenerator t (n +ℕ fst x₁ , <→<ᵗ (<-k+ (<ᵗ→< (snd x₁)))) ≡
      ℤFinGenerator k x₁
    MR w with (fst t ≟ᵗ (n +ℕ fst w)) | ((fst t ∸ n) ≟ᵗ fst w)
    ... | lt x | lt x₁ = refl
    ... | lt p | eq q =
      ⊥.rec (¬m<ᵗm (subst (_<ᵗ (n +ℕ fst w)) (sym (≤-∸-+-cancel (<-weaken (<ᵗ→< x))) ∙ +-comm _ n ∙ cong (n +ℕ_) q) p))
    ... | lt x | gt x₁ = refl
    ... | eq p | lt q =
      ⊥.rec (¬m<ᵗm (subst (_<ᵗ fst w) (cong (_∸ n) p ∙ ∸+ _ _) q))
    ... | eq x | eq x₁ = refl
    ... | eq p | gt q = ⊥.rec (¬m<ᵗm (subst (fst w <ᵗ_) (cong (_∸ n) p ∙ ∸+ _ _) q))
    ... | gt x | lt x₁ = refl
    ... | gt p | eq q =
        ⊥.rec (¬m<ᵗm (subst ((n +ℕ fst w) <ᵗ_)
          (sym (≤-∸-+-cancel (<-weaken (<ᵗ→< x))) ∙ +-comm _ n ∙ cong (n +ℕ_) q) p))
    ... | gt x | gt x₁ = refl

module _ (ℓ : Level) (C D : CWskel ℓ) (c₀ : Fin (CWskel-fields.card C 0)) (d₀ : Fin (CWskel-fields.card D 0)) where
  open CWskel-fields

  open ChainComplex

  chainC = CW-AugChainComplex C
  chainD = CW-AugChainComplex D

  AbGroupIso-fun : ∀ {ℓ} (G H : AbGroup ℓ) → AbGroupIso G H → AbGroupHom G H
  AbGroupIso-fun G H f = f .fst .Iso.fun , f .snd

  AbGroupIso-inv : ∀ {ℓ} (G H : AbGroup ℓ) → AbGroupIso G H → AbGroupHom H G
  AbGroupIso-inv G H f = (invGroupIso f) .fst .Iso.fun , (invGroupIso f) .snd

  ℤFinProd-fun : (n m : ℕ) → AbGroupHom ℤ[Fin n +ℕ m ] (AbDirProd ℤ[Fin n ] ℤ[Fin m ])
  ℤFinProd-fun n m = AbGroupIso-fun ℤ[Fin n +ℕ m ] (AbDirProd ℤ[Fin n ] ℤ[Fin m ]) (ℤFinProduct n m)

  ℤFinProd-inv : (n m : ℕ) → AbGroupHom (AbDirProd ℤ[Fin n ] ℤ[Fin m ]) ℤ[Fin n +ℕ m ]
  ℤFinProd-inv n m = AbGroupIso-inv ℤ[Fin n +ℕ m ] (AbDirProd ℤ[Fin n ] ℤ[Fin m ]) (ℤFinProduct n m)

  ℤFin-compwise : (n m n' m' : ℕ) → AbGroupHom ℤ[Fin n ] ℤ[Fin m ] → AbGroupHom ℤ[Fin n' ] ℤ[Fin m' ]
                                  → AbGroupHom (AbDirProd ℤ[Fin n ] ℤ[Fin n' ]) (AbDirProd ℤ[Fin m ] ℤ[Fin m' ])
  ℤFin-compwise n m n' m' f f' = (λ x → (f .fst) (x .fst) , (f' .fst) (x .snd))
                                 , makeIsGroupHom λ a b → ΣPathP (IsGroupHom.pres· (snd f) (fst a) (fst b)
                                                                 , IsGroupHom.pres· (snd f') (snd a) (snd b))

  ⋁-src₀ : Fin (card C 1) ⊎ Fin (card D 1) → (Fin (card C zero) , c₀) ⋁ (Fin (card D zero) , d₀)
  ⋁-src₀ (inl c) = inl (∂₀.src₀ C c)
  ⋁-src₀ (inr d) = inr (∂₀.src₀ D d)

  ⋁-src₁ : Fin ((card C 1) +ℕ (card D 1)) → Fin ((card C zero) +ℕ (predℕ (card D zero)))
  ⋁-src₁ = (Iso-Fin⊎Fin-Fin+ {card C zero}{predℕ (card D zero)} .Iso.fun)
           ∘ (wedgeFinIso (card C zero) (card D zero) c₀ d₀ .Iso.fun)
           ∘ ⋁-src₀
           ∘ (Iso-Fin⊎Fin-Fin+ {card C 1}{card D 1} .Iso.inv)

  ⋁-src : AbGroupHom ℤ[Fin card C 1 +ℕ card D 1 ] ℤ[Fin card C zero +ℕ predℕ (card D zero) ]
  ⋁-src = ℤFinFunct {card C 1 +ℕ card D 1}{card C zero +ℕ predℕ (card D zero)} ⋁-src₁

  ⋁-dest₀ : Fin (card C 1) ⊎ Fin (card D 1) → (Fin (card C zero) , c₀) ⋁ (Fin (card D zero) , d₀)
  ⋁-dest₀ (inl c) = inl (∂₀.dest₀ C c)
  ⋁-dest₀ (inr d) = inr (∂₀.dest₀ D d)

  ⋁-dest₁ : Fin ((card C 1) +ℕ (card D 1)) → Fin ((card C zero) +ℕ (predℕ (card D zero)))
  ⋁-dest₁ = (Iso-Fin⊎Fin-Fin+ {card C zero}{predℕ (card D zero)} .Iso.fun)
           ∘ (wedgeFinIso (card C zero) (card D zero) c₀ d₀ .Iso.fun)
           ∘ ⋁-dest₀
           ∘ (Iso-Fin⊎Fin-Fin+ {card C 1}{card D 1} .Iso.inv)

  ⋁-dest : AbGroupHom ℤ[Fin card C 1 +ℕ card D 1 ] ℤ[Fin card C zero +ℕ predℕ (card D zero) ]
  ⋁-dest = ℤFinFunct {card C 1 +ℕ card D 1}{card C zero +ℕ predℕ (card D zero)} ⋁-dest₁



  C∨D : CWskel ℓ
  C∨D = wedgeSkel _ C D c₀ d₀

  chainC⋁DChain : (n : ℕ) → AbGroup ℓ-zero
  chainC⋁DChain = chain (CW-AugChainComplex C∨D)


  chainC⋁DBdry : (n : ℕ) → AbGroupHom (chainC⋁DChain (suc n)) (chainC⋁DChain n)
  chainC⋁DBdry zero = sumCoefficients (card C zero +ℕ predℕ (card D zero))
  chainC⋁DBdry (suc zero) =
    subtrGroupHom ℤ[Fin card C 1 +ℕ card D 1 ] ℤ[Fin card C zero +ℕ predℕ (card D zero) ] ⋁-dest ⋁-src
  chainC⋁DBdry (suc (suc n)) =
    compGroupHom (ℤFinProd-fun (card C (suc (suc n))) (card D (suc (suc n))))
    (compGroupHom (ℤFin-compwise (card C (suc (suc n))) (card C (suc n)) (card D (suc (suc n))) (card D (suc n))
                                 (chainC .bdry (suc (suc n))) (chainD .bdry (suc (suc n))))
                  (ℤFinProd-inv (card C (suc n)) (card D (suc n))))

  <ᵗ-trans' : {n m k : ℕ} → n <ᵗ m → m <ᵗ suc k → n <ᵗ k
  <ᵗ-trans' {n = zero} {suc m} {suc k} _ _ = tt
  <ᵗ-trans' {n = suc n} {suc m} {suc k} = <ᵗ-trans' {n = n} {m} {k}

  skipFin← : {n : ℕ} (x : Fin (suc (suc n))) → Fin (suc (suc n)) → Fin (suc n)
  skipFin← {n = n} x (d , s) with (fst x ≟ᵗ d)
  ... | lt p = {!snd x!}
  ... | eq q = zero , tt
  ... | gt p = d , <ᵗ-trans' p (snd x)

  skipFin : {n : ℕ} (x : Fin n) → Fin (predℕ n) → Fin n
  skipFin {n = suc n} x (d , s) with (fst x ≟ᵗ d)
  ... | lt p = d , <ᵗ-trans s <ᵗsucm
  ... | eq q = suc d , s
  ... | gt p = suc d , s

  C∨D→C×D' : ChainComplexMap (CW-AugChainComplex C∨D) (ChainComplexProd (CW-AugChainComplex C) (CW-AugChainComplex D))
  fst (ChainComplexMap.chainmap C∨D→C×D' zero) x = {!!}
  snd (ChainComplexMap.chainmap C∨D→C×D' zero) = {!!}
  ChainComplexMap.chainmap C∨D→C×D' (suc zero) =
    compGroupHom (ℤFinProd-fun _ _)
                 (dirProdHom idGroupHom (ℤFinFunct (skipFin d₀)))
  ChainComplexMap.chainmap C∨D→C×D' (suc (suc n)) = ℤFinProd-fun _ _
  ChainComplexMap.bdrycomm C∨D→C×D' zero =
    agreeOnℤFinGenerator→≡' λ t → {!fst (ℤFinProd-fun (C .snd .fst zero) (predℕ (card D 0)))
         (ℤFinGenerator t)!}
  {- Σ≡Prop {!!} (funExt
    λ t → ΣPathP (funExt⁻ (cong fst (augmentation.ϵ-alt C))
                    (fst (fst (ℤFinProd-fun (C .snd .fst zero) (predℕ (card D 0))) t))
                ∙ funExt (λ { (zero , tt) → {!!}})
                ∙ sym (funExt⁻ (cong fst (augmentation.ϵ-alt C∨D)) t)
               , {!refl!}))
               -}
    where
    help : (s : _) → augmentation.ϵ C .fst s ≡ {!!}
    help s = funExt⁻ (cong fst (augmentation.ϵ-alt C)) s
           ∙ {!!}
  ChainComplexMap.bdrycomm C∨D→C×D' (suc n) = {!!}

  finInject' : {n : ℕ} → Fin (predℕ n) → Fin n
  finInject' {n = suc n} x = fst x , <ᵗ-trans (snd x) <ᵗsucm

  C∨D→C×D : ChainComplexMap (ChainComplexProd (CW-AugChainComplex C) (CW-AugChainComplex D))
                             (CW-AugChainComplex C∨D)
  fst (ChainComplexMap.chainmap C∨D→C×D zero) (f , g) s = (f s - g s) 
  snd (ChainComplexMap.chainmap C∨D→C×D zero) = makeIsGroupHom λ f g → funExt λ q → {!q!}
  ChainComplexMap.chainmap C∨D→C×D (suc zero) =
    compGroupHom (dirProdHom idGroupHom ((λ f z → f (finInject' z)) , {!f!}))
                 (ℤFinProd-inv _ _)
  ChainComplexMap.chainmap C∨D→C×D (suc (suc n)) = ℤFinProd-inv _ _
  ChainComplexMap.bdrycomm C∨D→C×D zero = Σ≡Prop {!!}
    (funExt λ q → {!snd q!})
  ChainComplexMap.bdrycomm C∨D→C×D (suc zero) = Σ≡Prop {!!} {!∂ C∨D 0!}
  ChainComplexMap.bdrycomm C∨D→C×D (suc (suc n)) = {!!}


  C∨D' : (n : ℕ)
    → chainC⋁DBdry n ≡ bdry (CW-AugChainComplex C∨D) n
  C∨D' zero = sym (augmentation.ϵ-alt _)
  C∨D' (suc n) = agreeOnℤFinGenerator→≡'
    λ t → {!!}
    ∙ funExt λ s → isGeneratorℤFinGenerator' _ t
  -- C∨D' (suc ) = {!!}


--   H⋁→ₗ : cellMap C C∨D
--   SequenceMap.map H⋁→ₗ zero s = s
--   SequenceMap.map H⋁→ₗ (suc m) s = inl s
--   SequenceMap.comm H⋁→ₗ zero s = ⊥.rec (snd C .snd .snd .fst s)
--   SequenceMap.comm H⋁→ₗ (suc m) s = refl

--   H⋁→ᵣ : cellMap D C∨D
--   SequenceMap.map H⋁→ᵣ zero s = ⊥.rec (snd D .snd .snd .fst s)
--   SequenceMap.map H⋁→ᵣ (suc m) s = inr s
--   SequenceMap.comm H⋁→ᵣ zero s = ⊥.rec (snd D .snd .snd .fst s)
--   SequenceMap.comm H⋁→ᵣ (suc m) s = refl

--   open import Cubical.HITs.SetQuotients as SQ
--   HAb̃ˢᵏᵉˡ : ∀ {ℓ} (C : CWskel ℓ) (n : ℕ) → AbGroup ℓ-zero 
--   HAb̃ˢᵏᵉˡ C n = Group→AbGroup (H̃ˢᵏᵉˡ C n)
--     (SQ.elimProp2 (λ _ _ → GroupStr.is-set ((H̃ˢᵏᵉˡ C n) .snd) _ _)
--       λ f g → cong [_] (Σ≡Prop (λ _ → AbGroupStr.is-set (snd (chain (CW-AugChainComplex C) n)) _ _)
--         (funExt λ _ → +Comm _ _)))

--   H⋁→ : (n : ℕ) → AbGroupHom (AbDirProd (HAb̃ˢᵏᵉˡ C n) (HAb̃ˢᵏᵉˡ D n)) (HAb̃ˢᵏᵉˡ C∨D n)
--   H⋁→ n = subtrGroupHom _ _
--     (compGroupHom dirProdFst (finCellMap→HomologyMap n (cellMap→finCellMap (suc (suc (suc n))) H⋁→ₗ)))
--     (compGroupHom dirProdSnd (finCellMap→HomologyMap n (cellMap→finCellMap (suc (suc (suc n))) H⋁→ᵣ)))

--   H⋁←Map : (n : ℕ) → fst (ℤ[A C∨D ] n) → fst (ℤ[A C ] n) × fst (ℤ[A D ] n)
--   H⋁←Map zero f = ℤFinProd-fun _ _ .fst f .fst
--                  , ℤFinFunct (skipFin d₀) .fst (ℤFinProd-fun (card C 0) (predℕ (card D 0)) .fst f .snd)
--   H⋁←Map (suc n) f = ℤFinProd-fun _ _ .fst f --  .fst , AbGroupStr.-_ ((ℤ[A D ] (suc n)) .snd) (ℤFinProd-fun _ _ .fst f .snd)

--   H⋁←MapKer : (n : ℕ) (x : fst (ℤ[A C∨D ] n))
--     → (bdry (CW-AugChainComplex C∨D) n .fst x ≡ AbGroupStr.0g (snd (chain (CW-AugChainComplex C∨D) n)))
--     → dirProdHom (bdry (CW-AugChainComplex C) n) (bdry (CW-AugChainComplex D) n) .fst (H⋁←Map n x)
--     ≡ ((AbGroupStr.0g (snd (chain (CW-AugChainComplex C) n))) , ((AbGroupStr.0g (snd (chain (CW-AugChainComplex D) n)))))
--   H⋁←MapKer zero f q = ΣPathP ({!!} , {!!})
--   {- -- refl
--    -- ∙ help (F .fst) (F .snd) (cong (augmentation.ϵ C∨D .fst)
--       elimPropℤFin _ _ {!λ _ → !}
--         (λ p → {!!})
--         (λ p q → {!!})
--         (λ f g p q r → {!q!})
--         {!!} -- (Iso.leftInv (ℤFinProductIso (snd C .fst zero) (predℕ (card D zero))) f) ∙ p)
--     where
--     -}
--     {-
--     F = ℤFinProd-fun (snd C .fst zero) (predℕ (card D zero)) .fst f
--     help : (x : _) (y : _) → augmentation.ϵ C∨D .fst
--            (ℤFinProd-inv (snd C .fst zero) (predℕ (card D zero)) .fst (x , y))
--          ≡ AbGroupStr.0g (snd ℤ[Fin 1 ])
--         → (x , ℤFinFunctFun (skipFin d₀) y) ≡ ((λ _ → 0) , λ _ → 0)
--     help x y q = ΣPathP ({!l!} , {!funExt⁻ l fzero!})
--       where
--       l : fst (sumCoefficients (snd C∨D .fst 0))
--             (ℤFinProd-inv (snd C .fst zero) (predℕ (card D zero)) .fst (x , y))
--             ≡ AbGroupStr.0g (snd ℤ[Fin 1 ])
--       l = sym (funExt⁻ (cong fst (augmentation.ϵ-alt C∨D)) (ℤFinProd-inv (snd C .fst zero) (predℕ (card D zero)) .fst (x , y))) ∙ q
--       -}
--   H⋁←MapKer (suc zero) f p = {!!}
--   H⋁←MapKer (suc (suc n)) f p =
--     sym ((sym (IsGroupHom.pres1 (ℤFinProd-fun (snd C .fst (suc n)) (card D (suc n)) .snd))
--     ∙ sym (cong (ℤFinProd-fun (snd C .fst (suc n)) (card D (suc n)) .fst) p))
--     ∙ cong (ℤFinProd-fun (snd C .fst (suc n)) (card D (suc n)) .fst)
--            ( (funExt⁻ (cong fst hom1≡hom2) f))
--     ∙ Iso.rightInv (fst (ℤFinProduct (snd C .fst (suc n)) (card D (suc n)))) _)
--     where
--     hom1 hom2 : AbGroupHom (ℤ[A C∨D ] (suc (suc n)))
--                            (ℤ[A C∨D ] (suc n))
--     hom1 = ∂ C∨D (suc n)
--     hom2 = compGroupHom (ℤFinProd-fun (snd C .fst (suc (suc n))) (card D (suc (suc n))))
--                         (compGroupHom (dirProdHom (∂ C (suc n)) (∂ D (suc n)))
--                         (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n))))

--     open import Cubical.HITs.Sn.Degree
--     open import Cubical.HITs.SphereBouquet
--     open import Cubical.HITs.SphereBouquet.Degree

--     hom1≡hom2 : hom1 ≡ hom2
--     hom1≡hom2 = agreeOnℤFinGenerator→≡'
--       λ t → ⊎.rec
--             (λ {(t' , q) → funExt (λ x → sym (isGeneratorℤFinGenerator' (λ a → degree (suc (suc n)) _) t))
--             {- cong (fst hom1)
--               (sym (Iso.leftInv (ℤFinProductIso (card C (suc (suc n))) (card D (suc (suc n))))
--                     (ℤFinGenerator t))
--                   ∙ cong (fst (ℤFinProd-inv (snd C .fst (suc (suc n))) (card D (suc (suc n))))) q)
--              ∙ refl
--              -}
--              ∙ funExt (λ s → lem1 t t' q s)
--              ∙ cong (fst (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n))))
--                     (ΣPathP (funExt (λ x →
--                       (isGeneratorℤFinGenerator' (λ a → degree (suc (suc n)) _) t')) , refl))
--              ∙ cong (fst (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n))))
--                     (ΣPathP (refl , sym (IsGroupHom.pres1 (∂ D (suc n) .snd))) ∙ cong (fst (dirProdHom (∂ C (suc n)) (∂ D (suc n))))
--                       (sym (Iso.rightInv (ℤFinProductIso (card C (suc (suc n))) (card D (suc (suc n)))) ((ℤFinGenerator t') , (λ _ → 0)))))
--              ∙ cong (fst hom2) (sym (sym (Iso.leftInv (ℤFinProductIso (card C (suc (suc n))) (card D (suc (suc n))))
--                     (ℤFinGenerator t))
--                   ∙ cong (fst (ℤFinProd-inv (snd C .fst (suc (suc n))) (card D (suc (suc n))))) q))})
--             {!!}
--         (ℤFinProductGenerator {n = card C (suc (suc n))} {card D (suc (suc n))} t)
--         where
--         lem1 : (t : Fin _) (t' : _) (q : _) (s : _)
--           → degree (suc (suc n)) (λ x → pickPetal s (preboundary.pre∂ C∨D (suc n) (inr (t , x))))
--           ≡ _
--         lem1 t t' q s with (fst s ≟ᵗ snd C .fst (suc n))
--         ... | lt x = {!!}
--         ... | eq x = {!!}
--         ... | gt x = {!!} ∙ {!fst (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n))) ?
--       s!}
--     help : (t : fst (ℤ[Fin snd C .fst (suc n) ]) × fst (ℤ[Fin card D (suc n) ]))
--          → ∂ C∨D n .fst (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n)) .fst t) ≡ (λ _ → 0)
--         → fst (∂ C n) (fst t) ≡ AbGroupStr.0g (snd (ℤ[A C ] n))
--     help (t , s) l = {!!}
--       where

  

--       help2 : snd (ℤ[A C∨D ] n) .AbGroupStr._+_
--                (fst (∂ C∨D n)
--                  (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n)) .fst (t , (λ _ → 0))))
--                (fst (∂ C∨D n)
--                  (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n)) .fst ((λ _ → 0) , s)))
--              ≡ λ _ → 0
--       help2 = sym (IsGroupHom.pres· (∂ C∨D n .snd)
--                (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n)) .fst (t , (λ _ → 0)))
--                (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n)) .fst ((λ _ → 0) , s)))
--         ∙ (cong (∂ C∨D n .fst))
--           (sym (IsGroupHom.pres· (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n)) .snd)
--                              (t , (λ _ → 0)) ((λ _ → 0) , s))
--           ∙ cong (ℤFinProd-inv (snd C .fst (suc n)) (card D (suc n)) .fst)
--                  (ΣPathP (refl , (funExt (λ x → +Comm 0 (s x))))))
--           ∙ l
--   {-
--     cong (∂ C n .fst) {!Iso.leftInv (ℤFinProductIso (snd C .fst (suc n)) (snd D .fst (suc n))) f!}
--     ∙ {!p!}
-- -}
--   open import Cubical.HITs.PropositionalTruncation as PT
--   H⋁← : (n : ℕ) → HAb̃ˢᵏᵉˡ C∨D n .fst → HAb̃ˢᵏᵉˡ C n .fst × (HAb̃ˢᵏᵉˡ D n .fst)
--   H⋁← n =
--     SQ.rec (isSet× (AbGroupStr.is-set (HAb̃ˢᵏᵉˡ C n .snd)) (AbGroupStr.is-set (HAb̃ˢᵏᵉˡ D n .snd)))
--       (λ f → [ (H⋁←Map n (fst f) .fst) , cong fst (H⋁←MapKer n (fst f) (snd f)) ]
--             , [ (H⋁←Map n (fst f) .snd) , cong snd (H⋁←MapKer n (fst f) (snd f)) ])
--       λ f g → PT.rec {!!}
--         (λ p → ΣPathP (cong [_] (Σ≡Prop (λ _ → isPropIsInKer _ _) (funExt {!!})) , {!!}))
-- {-
--   HAb̃ˢᵏᵉˡ C∨D n
--   -}


--   -- H⋁→ : (n : ℕ) → H̃ˢᵏᵉˡ C n .fst × H̃ˢᵏᵉˡ D n .fst → H̃ˢᵏᵉˡ C∨D n .fst
--   -- H⋁→ n (f , g) =
--   --   GroupStr._·_ (H̃ˢᵏᵉˡ C∨D n .snd) {!!}
--   --     (GroupStr.inv (H̃ˢᵏᵉˡ C∨D n .snd) (finCellMap→HomologyMap n (cellMap→finCellMap (suc (suc (suc n))) H⋁→ᵣ) .fst g))
--   --       -- finCellMap→HomologyMap n (cellMap→finCellMap (suc (suc (suc n))) {!!}) .fst f , {!!}

--   chainC⋁D : ChainComplex ℓ-zero
--   chainC⋁D .chain = chainC⋁DChain
--   chainC⋁D .bdry = chainC⋁DBdry
--   chainC⋁D .bdry²=0 zero = {!!}
--   chainC⋁D .bdry²=0 (suc n) = agreeOnℤFinGenerator→≡' main -- Σ≡Prop {!!} (funExt λ x → {!!})
--     where
--     M1 = chainC⋁DBdry (suc n) .fst
--     M2 = fst (ℤFinProd-inv (card C (suc n)) (card D (suc n)))
--     M3 = fst (ℤFin-compwise (card C (suc (suc n))) (card C (suc n))
--                   (card D (suc (suc n))) (card D (suc n))
--                   (chainC .bdry (suc (suc n))) (chainD .bdry (suc (suc n))))
--     M4 = fst (ℤFinProd-fun (card C (suc (suc n))) (card D (suc (suc n))))

--     main' : (x : _) → chainC⋁DBdry (suc n) .fst
--           (fst (ℤFinProd-inv (card C (suc n)) (card D (suc n)))
--             (fst (ℤFin-compwise (card C (suc (suc n))) (card C (suc n))
--                   (card D (suc (suc n))) (card D (suc n))
--                   (chainC .bdry (suc (suc n))) (chainD .bdry (suc (suc n))))
--                   x)) ≡ snd (chainC⋁DChain (suc n)) .AbGroupStr.0g
--     main' (x , y) = cong (chainC⋁DBdry (suc n) .fst ∘ fst (ℤFinProd-inv (card C (suc n)) (card D (suc n))))
--                          (ΣPathP ((λ _ → chainC .bdry (suc (suc n)) .fst x) , (λ _ → chainD .bdry (suc (suc n)) .fst y)))
--                  ∙ {!!}
--                  ∙ {!!}

--     main : (x : Fin (card C (suc (suc n)) +ℕ card D (suc (suc n))))
--       → M1 (M2 (M3 (M4 (ℤFinGenerator x))))
--         ≡ snd (chainC⋁DChain (suc n)) .AbGroupStr.0g
--     main x with (ℤFinProductGenerator x)
--     ... | inl k = cong M1 (cong M2 (cong M3 (k .snd)))
--                 ∙ (λ i → M1 (M2 ((chainC .bdry (suc (suc n)) .fst (ℤFinGenerator (fst k)))
--                 , (IsGroupHom.pres1 (snd (chainD .bdry (suc (suc n)))) i))))
--                 ∙ {!chainC .bdry (suc (suc n)) .fst (ℤFinGenerator (fst k))!}
--     ... | inr r = {!!}
--    -- Σ≡Prop {!!} (funExt {!!})
