{-# OPTIONS --safe #-}
module Game where

open import Prelude
open import Data.Maybe
open import Data.Maybe.Correspondences.Unary.Any

open import LFSet
open import LFSet.Membership

-- from https://www.ps.uni-saarland.de/extras/fol-completeness-ext/website/Undecidability.FOLC.Sorensen.html

private variable
  ℓ ℓ′ ℓ″ ℓa ℓatk ℓd : Level
  A : 𝒰 ℓ

record rule-set (A : 𝒰 ℓ)
                (ℓa ℓatk ℓd : Level) : 𝒰 (ℓ ⊔ ℓsuc ℓa ⊔ ℓsuc ℓatk ⊔ ℓsuc ℓd) where
  constructor mkruleset
  field
    atomic : A → Prop ℓa
    attack : A → Maybe A → 𝒰 ℓatk
    defense : {phi : A} {adm : Maybe A} → attack phi adm → A → Prop ℓd

open rule-set public

justified : {A : 𝒰 ℓ}
          → {R : rule-set A ℓa ℓatk ℓd}
          → (S : LFSet A)
          → A
          → 𝒰 (ℓa ⊔ ℓ)
justified {R} S φ = ⌞ R .atomic φ ⌟ → φ ∈ S

justified-weak : {A : 𝒰 ℓ}
               → {R : rule-set A ℓa ℓatk ℓd}
               → {S T : LFSet A}
               → S ⊆ T
               → {φ : A} → justified {R = R} S φ → justified {R = R} T φ
justified-weak sub js = sub ∘ js

data challenge (A : 𝒰 ℓ)
               (R : rule-set A ℓa ℓatk ℓd) : 𝒰 (ℓ ⊔ ℓatk) where
  C : ∀ {phi adm}
    → R .attack phi adm
    → challenge A R

ch-def : {A : 𝒰 ℓ}
         {R : rule-set A ℓa ℓatk ℓd}
       → challenge A R
       → A → 𝒰 ℓd
ch-def {R} (C atk) ψ = ⌞ R .defense atk ψ ⌟

data opening (A : 𝒰 ℓ)
             (R : rule-set A ℓa ℓatk ℓd)
             (φ : A)
             : LFSet A → challenge A R → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk) where
  OP : ∀ {adm s}
     → justified {R = R} [] φ
     → (atk : R .attack φ adm)
     → s ＝ from-maybe adm
     → opening A R φ s (C atk)
