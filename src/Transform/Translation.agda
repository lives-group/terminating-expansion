module Transform.Translation where

open import Common.Fuel
open import Common.Type
open import Common.Context
open import R.Syntax.Base
open import R.Syntax
open import R.Syntax.Properties
open import R.Syntax.Unrolling
open import L.Syntax

open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to _/\_)

⊢-to-⊪ : ∀{Γ τ} → Γ ⊢ τ → Γ ⊪ τ
⊢-to-⊪  zero´          = zero´
⊢-to-⊪ (suc´ t)        = suc´ (⊢-to-⊪ t)
⊢-to-⊪ (var x)         = var x
⊢-to-⊪ (abs t)         = abs (⊢-to-⊪ t)
⊢-to-⊪ (app t t₁)      = app (⊢-to-⊪ t) (⊢-to-⊪ t₁)
⊢-to-⊪ (match t t₁ t₂) = match (⊢-to-⊪ t) (⊢-to-⊪ t₁) (⊢-to-⊪ t₂)

call-elimination : ∀{Γ τ τ₁}{t : Γ ⊢ τ} → τ₁ called-in t → Γ ⊪ τ
call-elimination {t = .(var _)}    call-var
  = error
call-elimination {t = .(abs _)}   (call-abs c)
  = abs (call-elimination c)
call-elimination {t = .(suc´ _)}  (call-suc c)
  = suc´ (call-elimination c)
call-elimination {t = app _ t₂}   (call-app1 c _)
  = app (call-elimination c) (⊢-to-⊪ t₂)
call-elimination {t = app t₁ _}   (call-app2 _ c)
  = app (⊢-to-⊪ t₁) (call-elimination c)
call-elimination {t = .(app _ _)} (call-app12 c c₁)
  = app (call-elimination c) (call-elimination c₁)
call-elimination {t = match _ t₁ t₂} (call-match1 c _ _)
  = match (call-elimination c) (⊢-to-⊪ t₁) (⊢-to-⊪ t₂)
call-elimination {t = match t _ t₂} (call-match2 _ c _)
  = match (⊢-to-⊪ t) (call-elimination c) (⊢-to-⊪ t₂)
call-elimination {t = match t t₁ _} (call-match3 _ _ c)
  = match (⊢-to-⊪ t) (⊢-to-⊪ t₁) (call-elimination c)
call-elimination {t = match _ _ t₂} (call-match12 c c₁ _)
  = match (call-elimination c) (call-elimination c₁) (⊢-to-⊪ t₂)
call-elimination {t = match _ t₁ _} (call-match13 c _ c₁)
  = match (call-elimination c) (⊢-to-⊪ t₁) (call-elimination c₁)
call-elimination {t = match t _ _} (call-match23 _ c c₁)
  = match (⊢-to-⊪ t) (call-elimination c) (call-elimination c₁)
call-elimination {t = .(match _ _ _)} (call-match123 c c₁ c₂)
  = match (call-elimination c) (call-elimination c₁) (call-elimination c₂)



-- -- Doesn't not perform unroll
-- translate : ∀{τ} → ∅ ⊩ τ → ∅ ⊪ τ
-- translate (rec t x)  = something (call-elimination x)
-- translate (rec∙ t x) = app (translate t) (⊢-to-⊪ x)
