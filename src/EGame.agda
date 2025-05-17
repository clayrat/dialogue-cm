{-# OPTIONS --safe #-}
module EGame where

open import Prelude
open import Data.Maybe
open import Data.Maybe.Correspondences.Unary.Any

open import LFSet
open import LFSet.Membership

-- from https://www.ps.uni-saarland.de/extras/fol-completeness-ext/website/Undecidability.FOLC.Sorensen.html

{- Generalized Intuitionistic E-Dialogues -}

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
  OP : ∀ {adm}
     → justified {R = R} [] φ
     → (atk : R .attack φ adm)
     → opening A R φ (from-maybe adm) (C atk)  -- TODO ford

data epmove (A : 𝒰 ℓ)
            (R : rule-set A ℓa ℓatk ℓd)
            : LFSet A → challenge A R → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd) where
  EPAtk : ∀ {S c φ adm}
        → φ ∈ S
        → Any (justified {R = R} S) adm
        → R .attack φ adm
        → epmove A R S c
  EPDef : ∀ {S φ adm}
            {atk : R .attack φ adm}
            {ψ : A}
        → justified {R = R} S ψ
        → ⌞ R .defense atk ψ ⌟
        → epmove A R S (C atk)

data eomove (A : 𝒰 ℓ)
            (R : rule-set A ℓa ℓatk ℓd)
            (S : LFSet A)
            : (c : challenge A R) → epmove A R S c
            → LFSet A → challenge A R → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd) where
  EODef : ∀ {φ c adm h g}
            {atk : R .attack φ adm}
            {ψ : A}
        → ⌞ R .defense atk ψ ⌟
        → eomove A R S c (EPAtk h g atk) (ψ ∷ S) c
  EOCounter : ∀ {c φ ψ adm}
                {h : φ ∈ S}
                {g : Any (justified {R = R} S) (just ψ)}
                {atk : R .attack φ (just ψ)}
                {atk′ : R .attack ψ adm}
            → eomove A R S c (EPAtk h g atk) (from-maybe adm ∪∷ S) (C atk′) -- TODO ford?
  EOAtk : ∀ {φ adm}
            {atk : R .attack φ adm}
            {ψ : A}
            {hj : justified {R = R} S ψ}
            {def : ⌞ R .defense atk ψ ⌟}
            {adm′ : Maybe A}
            {atk′ : R .attack ψ adm′}
        → eomove A R S (C atk) (EPDef hj def) (from-maybe adm′ ∪∷ S) (C atk′) -- TODO ford?

data ewin-strat (A : 𝒰 ℓ)
                (R : rule-set A ℓa ℓatk ℓd)
                : LFSet A → challenge A R → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd) where
  EWS : ∀ {S c}
          {pm : epmove A R S c}
      → (∀ {T : LFSet A} {c′ : challenge A R}
         → eomove A R S c pm T c′ → ewin-strat A R T c′)
      → ewin-strat A R S c

-- TODO
{-
ewin-strat-prop : ∀ {A : 𝒰 ℓ}
                    {R : rule-set A ℓa ℓatk ℓd}
                    {S c}
                → is-prop (ewin-strat A R S c)
ewin-strat-prop (EWS s1) (EWS s2) = {!!}
-}

evalid : {A : 𝒰 ℓ}
         {R : rule-set A ℓa ℓatk ℓd}
       → A → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd)
evalid {A} {R} φ =
    justified {R = R} [] φ
  × (∀ S c → opening A R φ S c → ewin-strat A R S c)
