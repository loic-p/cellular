{-# OPTIONS --cubical #-}
module EilenbergSteenrod.ESAdditivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int renaming (_+_ to _+ℤ_)
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

  chainC⋁D : ChainComplex ℓ-zero
  chainC⋁D .chain zero = ℤ[Fin 1 ]
  chainC⋁D .chain (suc zero) = ℤ[Fin card C zero +ℕ predℕ (card D zero) ]
  chainC⋁D .chain (suc (suc n)) = ℤ[Fin card C (suc n) +ℕ card D (suc n) ]
  chainC⋁D .bdry zero = sumCoefficients (card C zero +ℕ predℕ (card D zero))
  chainC⋁D .bdry (suc zero) = subtrGroupHom ℤ[Fin card C 1 +ℕ card D 1 ] ℤ[Fin card C zero +ℕ predℕ (card D zero) ] ⋁-dest ⋁-src
  chainC⋁D .bdry (suc (suc n)) = compGroupHom (ℤFinProd-fun (card C (suc (suc n))) (card D (suc (suc n))))
    (compGroupHom (ℤFin-compwise (card C (suc (suc n))) (card C (suc n)) (card D (suc (suc n))) (card D (suc n))
                                 (chainC .bdry (suc (suc n))) (chainD .bdry (suc (suc n))))
                  (ℤFinProd-inv (card C (suc n)) (card D (suc n))))
  chainC⋁D .bdry²=0 = {!!}
