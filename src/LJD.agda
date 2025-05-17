{-# OPTIONS --safe #-}
module LJD where

open import Prelude
open import Data.Empty
open import Data.Acc
open import Data.Reflects as Reflects
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any

open import LFSet
open import LFSet.Membership
open import EGame

-- from https://www.ps.uni-saarland.de/extras/fol-completeness-ext/website/Undecidability.FOLC.Sorensen.html

{- Dialogical Sequent Calculus -}

private variable
  ℓ ℓ′ ℓ″ ℓa ℓatk ℓd : Level
  A : 𝒰 ℓ

data DPrv {ℓ′}
          (A : 𝒰 ℓ)
          (R : rule-set A ℓa ℓatk ℓd)
          : LFSet A → (A → 𝒰 ℓ′) → 𝒰 (ℓ ⊔ ℓsuc ℓ′ ⊔ ℓa ⊔ ℓatk ⊔ ℓsuc ℓd) where
  Def : ∀ {S T φ}
      → T φ
      → justified {R = R} S φ
      → (∀ {adm} {atk : R .attack φ adm}
          → DPrv A R (from-maybe adm ∪∷ S) (λ ψ → ⌞ R .defense atk ψ ⌟))
      → DPrv A R S T
  Att : ∀ {S T ψ adm} {atk : R .attack ψ adm}
      → ψ ∈ S
      → (∀ {χ} → ⌞ R .defense atk χ ⌟ → DPrv A R (χ ∷ S) T)
      → Any (justified {R = R} S) adm
      → Any (λ q → ∀ adm′ (atk′ : R .attack q adm′)
                 → DPrv A R (from-maybe adm′ ∪∷ S) (λ ζ → ⌞ R .defense atk′ ζ ⌟)) adm
      → DPrv A R S T

-- TODO prop

{- Soundness and Completeness -}

DPrv-ewin : ∀ {A : 𝒰 ℓ}
              {R : rule-set A ℓa ℓatk ℓd}
              {S T}
          → DPrv A R S T
          → ∀ {φ adm} {atk : R .attack φ adm}
          → (∀ ψ → T ψ → ⌞ R .defense atk ψ ⌟)
          → ewin-strat A R S (C atk)
DPrv-ewin                 (Def {φ} tf hj dp)                 hdef =
  EWS {pm = EPDef hj (hdef φ tf)}
      (λ where EOAtk → DPrv-ewin dp λ _ → id)
DPrv-ewin {A} {R} {S} {T} (Att {ψ} {atk = atka} ps dp ja da) hdef =
  EWS {pm = EPAtk ps ja atka}
      (DPrv-ewin-att dp da hdef)
  where
  DPrv-ewin-att :
      ∀ {ψ adm}
        {atka : R .attack ψ adm}
        {ps}
        (dp : ∀ {χ} → ⌞ R .defense atka χ ⌟ → DPrv A R (χ ∷ S) T)
        {ja}
        (da : Any (λ q → ∀ adm′ (atk′ : R .attack q adm′)
                       → DPrv A R (from-maybe adm′ ∪∷ S)
                                (λ ζ → ⌞ R .defense atk′ ζ ⌟)) adm)
        {φ adm′} {atk : R .attack φ adm′}
        (hdef : (ψ′ : A) → T ψ′ → ⌞ defense R atk ψ′ ⌟)
        {T′ c′}
    → eomove A R S (C atk) (EPAtk ps ja atka) T′ c′
    → ewin-strat A R T′ c′
  DPrv-ewin-att dp  _         hdef (EODef d) =
    -- Opponent defends
    DPrv-ewin (dp d) hdef
  DPrv-ewin-att _  (here daj) _    (EOCounter {adm = admd} {atk′}) =
    -- Opponent countered
    DPrv-ewin (daj admd atk′) λ _ → id

esoundness : ∀ {A : 𝒰 ℓ}
               {R : rule-set A ℓa ℓatk ℓd}
               {φ}
           → DPrv A R [] (_＝ φ) → evalid {R = R} φ
esoundness {A} {R} (Def {φ = φ′} ef hj dp) =
  Jₚ (λ q _ → evalid q)
     (hj , λ where
               S (C atk) (OP {adm} _ .atk) →
                   DPrv-ewin
                       (subst (λ q → DPrv _ R q λ ψ → ⌞ R .defense atk ψ ⌟)
                              (∪∷-id-r (from-maybe adm))
                              dp)
                        λ ψ → id)
     ef

ewin-DPrv : ∀ {A : 𝒰 ℓ}
              {R : rule-set A ℓa ℓatk ℓd}
              {S}
              {c : challenge A R}
          → ewin-strat A R S c → DPrv A R S (ch-def c)
ewin-DPrv {c = C a} (EWS {pm = EPAtk {adm = just m} ps ja atk} k) =
  -- Player attacks
  Att ps (λ rd → ewin-DPrv (k (EODef rd)))
      ja (here λ adm′ atk′ → ewin-DPrv (k EOCounter))
ewin-DPrv           (EWS {pm = EPDef hj hd}                    k) =
  -- Player defends
  Def hd hj (ewin-DPrv (k EOAtk))

ecompleteness : ∀ {A : 𝒰 ℓ}
                  {R : rule-set A ℓa ℓatk ℓd}
                  {φ}
              → evalid {R = R} φ → DPrv A R [] (_＝ φ)
ecompleteness {A} {R} {φ} (hj , hw) =
  Def refl hj
    λ {adm} {atk} →
       ewin-DPrv (hw (from-maybe adm ∪∷ []) (C atk)
                     (subst (λ q → opening A R φ q (C atk))
                            (∪∷-id-r (from-maybe adm) ⁻¹)
                            (OP hj atk)))

-- TODO equiv

DPrv-weak : ∀ {A : 𝒰 ℓ}
              {R : rule-set A ℓa ℓatk ℓd}
              {S P}
              {T : A → 𝒰 ℓ′}
              {T′ : A → 𝒰 ℓ″}
          → S ⊆ P
          → (∀ φ → T φ → T′ φ)
          → DPrv A R S T
          → DPrv A R P T′
DPrv-weak     sp tf (Def ef hj dp)                                 =
  Def (tf _ ef) (sp ∘ hj) λ {adm} {atk} →
    DPrv-weak (⊆-∪∷-l {xs = from-maybe adm} sp) (λ _ → id) dp
DPrv-weak {R} sp tf (Att {adm = just m} ps dp (here ja) (here da)) =
  Att (sp ps)
      (λ df → DPrv-weak (⊆-∷ sp) tf (dp df))
      (here (justified-weak {R = R} sp ja))
      (here λ adm′ atk′ → DPrv-weak (⊆-∪∷-l {xs = from-maybe adm′} sp)
                                    (λ _ → id)
                                    (da adm′ atk′))

DPrv-defend : ∀ {A : 𝒰 ℓ}
                {R : rule-set A ℓa ℓatk ℓd}
                {S φ}
                {T : A → 𝒰 ℓ′}
            → (∀ ψ → T ψ → φ ＝ ψ)
            → DPrv A R S T
            → ∀ adm (atk : R .attack φ adm)
            → DPrv A R (from-maybe adm ∪∷ S) (λ ζ → ⌞ R .defense atk ζ ⌟)
DPrv-defend {A} {R} {S} ht (Def {φ = φ′} ef hj dp)                                     adm atk =
  Jₚ (λ q eq → (∀ {adm′} {atk′ : R .attack q adm′}
                       → DPrv A R (from-maybe adm′ ∪∷ S) (λ ζ → ⌞ R .defense atk′ ζ ⌟))
             → DPrv A R (from-maybe adm ∪∷ S) (λ ζ → ⌞ R .defense atk ζ ⌟))
      (λ q → q)
      (ht φ′ ef) dp
DPrv-defend     {R}     ht (Att {adm = just m} {atk = atka} ps dp (here ja) (here da)) adm atk =
  Att {atk = atka}
      (∈ₛ-∪∷←r {s₁ = from-maybe adm} ps)
      (λ d → DPrv-weak (λ {x} → subst (x ∈_) (∪∷-swap {s = from-maybe adm} ⁻¹))
                       (λ _ → id)
                       (DPrv-defend ht (dp d) adm atk))
      (here (justified-weak {R = R} (∈ₛ-∪∷←r {s₁ = from-maybe adm}) ja))
      (here λ adm′ atk′ → DPrv-weak (⊆-∪∷-l {xs = from-maybe adm′}
                                            (∈ₛ-∪∷←r {s₁ = from-maybe adm}))
                                    (λ _ → id)
                                    (da adm′ atk′))

DPrv-exp : ∀ {A : 𝒰 ℓ}
             {R : rule-set A ℓa ℓatk ℓd}
             {S}
             {T : A → 𝒰 ℓ′}
             {T′ : A → 𝒰 ℓ″}
         → (∀ φ → ¬ (T φ))
         → DPrv A R S T
         → DPrv A R S T′
DPrv-exp nt = DPrv-weak id λ φ tφ → absurd (nt φ tφ)

DPrv-echo : ∀ {A : 𝒰 ℓ}
              {R : rule-set A ℓa ℓatk ℓd}
              {Q : A → A → 𝒰 ℓ′}
          → is-wf Q
          → (∀ {φ adm} {atk : R .attack φ adm}
             → Any (λ a → Q a φ) adm × ∀ χ → ⌞ R .defense atk χ ⌟ → Q χ φ)
          → ∀ {φ S} → φ ∈ S → ∀ {adm} {atk : R .attack φ adm}
          → DPrv A R (from-maybe adm ∪∷ S) (λ ζ → ⌞ R .defense atk ζ ⌟)
DPrv-echo {A} {R} {Q} wfq hdes {φ}  =
  to-induction wfq
    (λ q → ∀ {S} → q ∈ₛ S
         → ∀ {adm} {atk : R .attack q adm}
         → DPrv A R (from-maybe adm ∪∷ S)
                    (λ ζ → ⌞ R .defense atk ζ ⌟))
    (λ q ih {S} q∈ {adm} {atk} →
         let (had , hdf) = hdes {φ = q} {adm = adm} {atk = atk} in
         Att {atk = atk}
             (∈ₛ-∪∷←r {s₁ = from-maybe adm} q∈)
             (λ {χ} d → Def {φ = χ}
                            d (λ _ → hereₛ refl)
                            λ {adm = adm′} {atk = atk′} → ih χ (hdf χ d) (hereₛ refl))
             -- TODO abstract out
             (Maybe.elim (λ z → Any (λ a → Q a q) z
                              → Any (justified {R = R} (from-maybe z ∪∷ S)) z)
                         false!
                         (λ z _ → here λ _ → hereₛ refl)
                         adm had)
             (Maybe.elim (λ z → Any (λ a → Q a q) z
                              → Any (λ w → ∀ adm′ (atk′ : R .attack w adm′)
                                         → DPrv A R (from-maybe adm′ ∪∷ from-maybe z ∪∷ S)
                                                    (λ ζ → ⌞ R .defense atk′ ζ ⌟)) z)
                         false!
                         (λ z az → here λ adm′ atk′ → ih z (unhere az) (hereₛ refl))
                         adm had))
    φ

DPrv-ax : ∀ {A : 𝒰 ℓ}
            {R : rule-set A ℓa ℓatk ℓd}
            {T : A → 𝒰 ℓ′}
            {Q : A → A → 𝒰 ℓ′}
          → is-wf Q
          → (∀ {φ adm} {atk : R .attack φ adm}
             → Any (λ a → Q a φ) adm × ∀ χ → ⌞ R .defense atk χ ⌟ → Q χ φ)
          → ∀ {φ S} → φ ∈ S → T φ → DPrv A R S T
DPrv-ax wfq hdes {φ} φi tφ =
  Def {φ = φ} tφ (λ _ → φi) (DPrv-echo wfq hdes φi)

DPrv-just : ∀ {A : 𝒰 ℓ}
              {R : rule-set A ℓa ℓatk ℓd}
              {S φ}
              {T : A → 𝒰 ℓ′}
              {T′ : A → 𝒰 ℓ″}
          → (∀ ψ → T ψ → φ ＝ ψ)
          → DPrv A R S T
          → (∀ {P} → S ⊆ P -> justified {R = R} P φ → DPrv A R P T′)
          → DPrv A R S T′
DPrv-just {R} {S} {φ} te (Def {φ = φ′} ef hj dp)    jd =
  jd id (Jₚ (λ q eq → justified {R = R} S q → justified {R = R} S φ)
            id
            (te φ′ ef) hj)
DPrv-just             te (Att {adm = adma} {atk = atka} ps dp ja da) jd =
  Att {atk = atka}
      ps
      (λ d → DPrv-just te (dp d) λ sp → jd (sp ∘ thereₛ))
      ja da
