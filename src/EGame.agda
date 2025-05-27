{-# OPTIONS --safe #-}
module EGame where

open import Prelude
open import Data.Maybe
open import Data.Maybe.Correspondences.Unary.Any

open import LFSet
open import LFSet.Membership

open import Game

-- from https://www.ps.uni-saarland.de/extras/fol-completeness-ext/website/Undecidability.FOLC.Sorensen.html

private variable
  ℓ ℓ′ ℓ″ ℓa ℓatk ℓd : Level
  A : 𝒰 ℓ

{- Generalized Intuitionistic E-Dialogues -}

-- they restrict the opponent to only ever react to the proponent’s
-- directly preceding move, whereas the proponent may always respond
-- to any of the opponent’s previous moves

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
