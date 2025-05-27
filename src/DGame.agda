{-# OPTIONS --safe #-}
module DGame where

open import Prelude
open import Data.Maybe
open import Data.Maybe.Correspondences.Unary.Any
open import Data.List

open import LFSet
open import LFSet.Membership

open import Game
open import EGame
open import LJD

-- from https://www.ps.uni-saarland.de/extras/fol-completeness-ext/website/Undecidability.FOLC.Sorensen.html

{- Generalized Intuitionistic D-Dialogues -}

-- lightens the E-restriction to the opponent to only being able
-- to react to each proponent attack and admission only once, to
-- prevent ‘stalling’-tactics

private variable
  ℓ ℓ′ ℓ″ ℓa ℓatk ℓd : Level
  A : 𝒰 ℓ

-- TODO record?
dstate : (A : 𝒰 ℓ)
         (R : rule-set A ℓa ℓatk ℓd)
       → 𝒰 (ℓ ⊔ ℓatk)
dstate A R = LFSet A × List (challenge A R) × LFSet A × List (challenge A R)

data dpmove (A : 𝒰 ℓ)
            (R : rule-set A ℓa ℓatk ℓd)
            : dstate A R → dstate A R → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd) where
  DPAtk : ∀ {pA pC oA oC ϕ adm} {atk : R .attack ϕ adm}
        → ϕ ∈ oA
        → Any (justified {R = R} oA) adm
        → dpmove A R (                  pA , pC , oA ,         oC)
                     (from-maybe adm ∪∷ pA , pC , oA , C atk ∷ oC)
  DPDef : ∀ {pA pC oA oC ϕ adm} {atk : R .attack ϕ adm} {ψ}
        → justified {R = R} oA ψ
        → ⌞ R .defense atk ψ ⌟
        → dpmove A R (    pA , C atk ∷ pC , oA , oC)
                     (ψ ∷ pA ,         pC , oA , oC)

data domove (A : 𝒰 ℓ)
            (R : rule-set A ℓa ℓatk ℓd)
            : dstate A R → dstate A R → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd) where
  DOAtk : ∀ {pA pA' pC oA oC ϕ adm} {atk : R .attack ϕ adm}
        → domove A R (pA ∪∷ ϕ ∷ pA' ,         pC ,                   oA , oC)
                     (pA ∪∷     pA' , C atk ∷ pC , from-maybe adm ∪∷ oA , oC)
  DODef : ∀ {pA pC oA oC ϕ adm} {atk : R .attack ϕ adm} {ψ}
        → ⌞ R .defense atk ψ ⌟
        → domove A R (pA , pC ,     oA , C atk ∷ oC)
                     (pA , pC , ψ ∷ oA ,         oC)

data dwin-strat (A : 𝒰 ℓ)
                (R : rule-set A ℓa ℓatk ℓd)
                : dstate A R → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd) where
  DWS : ∀ {S S′ : dstate A R}
      → dpmove A R S S′
      → (∀ {S″ : dstate A R}
         → domove A R S′ S″ → dwin-strat A R S″)
      → dwin-strat A R S

dvalid : {A : 𝒰 ℓ}
         {R : rule-set A ℓa ℓatk ℓd}
       → A → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓd)
dvalid {A} {R} φ =
    justified {R = R} [] φ
  × (∀ S c → opening A R φ S c → dwin-strat A R ([] , c ∷ [] , S , []))

dwin-Dprv-embed : {A : 𝒰 ℓ}
                  {R : rule-set A ℓa ℓatk ℓd}
                → (s : dstate A R) → 𝒰 (ℓ ⊔ ℓa ⊔ ℓatk ⊔ ℓsuc ℓd)
dwin-Dprv-embed         (_ , []        , _ , _) = ⊤
dwin-Dprv-embed {A} {R} (_ , C atk ∷ _ , S , _) = DPrv A R S λ ζ → ⌞ R .defense atk ζ ⌟

dwin-Dprv : {A : 𝒰 ℓ}
            {R : rule-set A ℓa ℓatk ℓd}
          → {S : dstate A R}
          → dwin-strat A R S
          → dwin-Dprv-embed S
-- Player attacks
dwin-Dprv         (DWS (DPAtk      {pC = []}                  ϕ∈ aj)       ih) = lift tt
dwin-Dprv {A} {R} (DWS (DPAtk {pA} {pC = C ak ∷ pC} {oA} {oC} {atk} ϕ∈ aj) ih) =
  Att ϕ∈
      (λ {χ} rd → dwin-Dprv (ih (DODef rd)))
      aj
      (any-map∈
         (λ {x} x∈ jx adm′ atk′ →
                dwin-Dprv {S = pA , C atk′ ∷ C ak ∷ pC , from-maybe adm′ ∪∷ oA , C atk ∷ oC}
                          (ih (subst (λ q → domove A R (q ∪∷ pA , C ak ∷ pC , oA , C atk ∷ oC)
                                            (pA , C atk′ ∷ C ak ∷ pC , from-maybe adm′ ∪∷ oA , C atk ∷ oC))
                                     (from-maybe-= x∈ ⁻¹)
                                     (DOAtk {pA = []} {pA' = pA})))
         )
         aj)
dwin-Dprv         (DWS (DPDef {pA} {pC} {oA} {oC} pj rd)                   ih) =
  -- Player defends
  Def rd pj
    λ {adm = adm′} {atk = atk′} →
        dwin-Dprv {S = pA , C atk′ ∷ pC , from-maybe adm′ ∪∷ oA , oC}
                  (ih (DOAtk {pA = []} {pA' = pA}))

dcompleteness : {A : 𝒰 ℓ}
                {R : rule-set A ℓa ℓatk ℓd}
                {φ : A}
              → dvalid {R = R} φ → DPrv A R [] (_＝ φ)
dcompleteness (j , w) =
  Def refl j λ {adm} {atk} →
                 dwin-Dprv (w (from-maybe adm ∪∷ []) (C atk)
                              (OP j atk (∪∷-id-r (from-maybe adm))))
