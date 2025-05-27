{-# OPTIONS --safe #-}
module SGame where

open import Prelude
open import Data.Maybe
open import Data.Maybe.Correspondences.Unary.Any
open import Data.List
open import Data.List.Operations.Properties

open import LFSet
open import LFSet.Membership

open import Game
open import DGame
--open import LJD

-- from https://www.ps.uni-saarland.de/extras/fol-completeness-ext/website/Undecidability.FOLC.Sorensen.html

-- a “subset of D-dialogues”

private variable
  ℓ ℓ′ ℓ″ ℓa ℓatk ℓd : Level
  A : 𝒰 ℓ

deferred : (A : 𝒰 ℓ)
           (R : rule-set A ℓa ℓatk ℓd)
         → 𝒰 (ℓ ⊔ ℓatk)
deferred A R = challenge A R × challenge A R

sstate : (A : 𝒰 ℓ)
         (R : rule-set A ℓa ℓatk ℓd)
       → 𝒰 (ℓ ⊔ ℓatk)
sstate A R = LFSet A × LFSet A × List (deferred A R)

data spmove (A : 𝒰 ℓ)
            (R : rule-set A ℓa ℓatk ℓd)
            : sstate A R → challenge A R → sstate A R → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd) where
  SPAtk : ∀ {pA oA ds c ϕ adm} {atk : R .attack ϕ adm}
        → ϕ ∈ oA
        → Any (justified {R = R} oA) adm
        → spmove A R (                  pA , oA       ,         ds)
                     c
                     (from-maybe adm ∪∷ pA , oA , (C atk , c) ∷ ds)
  SPDef : ∀ {pA oA ds ϕ adm} {atk : R .attack ϕ adm} {ψ}
        → justified {R = R} oA ψ
        → ⌞ R .defense atk ψ ⌟
        → spmove A R (    pA , oA , ds)
                     (C atk)
                     (ψ ∷ pA , oA , ds)

data somove (A : 𝒰 ℓ)
            (R : rule-set A ℓa ℓatk ℓd)
            : sstate A R → sstate A R → challenge A R → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd) where
  SOAtk : ∀ {S pA pA' oA ds ϕ adm} {atk : R .attack ϕ adm}
        → S ＝ (pA ∪∷ ϕ ∷ pA' ,                   oA , ds)
        → somove A R S
                     (pA ∪∷     pA' , from-maybe adm ∪∷ oA , ds)
                     (C atk)
  SODef : ∀ {pA oA ds c ϕ adm} {atk : R .attack ϕ adm} {ψ}
        → ⌞ R .defense atk ψ ⌟
        → somove A R (pA ,     oA , (C atk , c) ∷ ds)
                     (pA , ψ ∷ oA ,               ds)
                     c

data swin-strat (A : 𝒰 ℓ)
                (R : rule-set A ℓa ℓatk ℓd)
                : sstate A R → challenge A R → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd) where
  SWS : ∀ {S S′ : sstate A R} {C}
      → spmove A R S C S′
      → (∀ {S″ : sstate A R} {C′}
         → somove A R S′ S″ C′ → swin-strat A R S″ C′)
      → swin-strat A R S C

svalid : {A : 𝒰 ℓ}
         {R : rule-set A ℓa ℓatk ℓd}
       → A → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd)
svalid {A} {R} φ =
    justified {R = R} [] φ
  × (∀ S c → opening A R φ S c → swin-strat A R ([] , S , []) c)

swin-dwin-embed : {A : 𝒰 ℓ}
                  {R : rule-set A ℓa ℓatk ℓd}
                → (s : sstate A R) → (c : challenge A R)
                → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd)
swin-dwin-embed {A} {R} (pA , oA , ds) c =
    ∀ {oC pC}
  → (oC , pC) ＝ unzip ds
  → dwin-strat A R (pA , c ∷ pC , oA , oC)

swin-dwin : {A : 𝒰 ℓ}
            {R : rule-set A ℓa ℓatk ℓd}
          → {s : sstate A R} {c : challenge A R}
          → swin-strat A R s c
          → swin-dwin-embed s c
-- Player attacks
swin-dwin {c}     (SWS (SPAtk {pA} {ds} {atk} ϕ∈ aj)    ih) {oC} {pC} e =
  DWS (DPAtk {atk = atk} ϕ∈ aj)
      λ {S″} → λ where
                   -- Opponent attacks
                   (DOAtk {pA = pA0} {pA'} ei) →
                       swin-dwin (ih (SOAtk {pA = pA0} {pA' = pA'}
                                            (×-path ei refl)))
                                 (×-path (ap (λ q → C atk ∷ fst q) e)
                                         (ap (λ q → c ∷ snd q) e))
                   -- Opponent defends
                   (DODef rd) →
                       swin-dwin (ih (SODef rd))
                                 e
-- Player defends
swin-dwin {A} {R} (SWS (SPDef {pA} {oA} {ds} {ψ} pj rd) ih) {oC} {pC} e =
  DWS (DPDef pj rd)
      λ {S″} → λ where
                   -- Opponent attacks
                   (DOAtk {pA = pA0} {pA'} ei) →
                      swin-dwin (ih (SOAtk {pA = pA0} {pA' = pA'}
                                           (×-path ei refl)))
                                e
                   -- Opponent defends
                   (DODef {oC} {ψ = ψ0} rd0) →
                      let (p , pC′ , ds′ , eoc , eds) = unzip-∷-l {abs = ds} (e ⁻¹) in
                      subst (λ q → dwin-strat A R (ψ ∷ pA , q , ψ0 ∷ oA , oC))
                            eoc
                            (swin-dwin (ih (subst (λ q → somove A R (ψ ∷ pA ,      oA ,  q )
                                                                    (ψ ∷ pA , ψ0 ∷ oA , ds′)
                                                                    p)
                                                  (eds ⁻¹)
                                                  (SODef rd0)))
                                       let (e1 , e2) = ×-path-inv (e ∙ ap unzip eds) in
                                       ×-path (∷-tail-inj e1) (∷-tail-inj (eoc ∙ e2)))

svalid-dvalid : {A : 𝒰 ℓ}
                {R : rule-set A ℓa ℓatk ℓd}
                {φ : A}
              → svalid {R = R} φ → dvalid {R = R} φ
svalid-dvalid (j , w) = j , (λ S c o → swin-dwin (w S c o) refl)
