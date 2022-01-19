module R.Syntax.Unrolling where

open import Common.Depth using (Depth; ⇓; ⇑)
open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_; _⊆_; ∈-subs; keep; drop)
open import R.Syntax
open import R.Syntax.Properties

open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to _/\_)

{-
Inlines term t₂ into t₁ replacing τ₂.
Inlining preserves variable calls.
-}
inline : ∀{Γ Δ τ₁ τ₂}{t₁ : Γ ⊢ τ₁ ⊚ ⇓}{t₂ : Δ ⊢ τ₂ ⊚ ⇓}
  → τ₂ called-in t₁
  → τ₂ called-in t₂
  → Δ ⊆ Γ
  → ∃ (λ (t₃ : Γ ⊢ τ₁ ⊚ ⇓) → τ₂ called-in t₃)
inline {t₂ = t₂} call-var c₂ Δ⊆Γ
  = ⊆-subs Δ⊆Γ t₂ /\ call-subs Δ⊆Γ c₂
inline (call-abs c₁) c₂ Δ⊆Γ
  = abs (proj₁ (inline c₁ c₂ (drop Δ⊆Γ)))
    /\ call-abs (proj₂ (inline c₁ c₂ (drop Δ⊆Γ)))
inline (call-suc c₁) c₂ Δ⊆Γ
  = suc´ (proj₁ (inline c₁ c₂ Δ⊆Γ))
    /\ call-suc (proj₂ (inline c₁ c₂ Δ⊆Γ))
inline {t₁ = app t t'} (call-app1 c₁ x) c₂ Δ⊆Γ
  = app (proj₁ (inline c₁ c₂ Δ⊆Γ)) t'
    /\ call-app1 (proj₂ (inline c₁ c₂ Δ⊆Γ)) x
inline {t₁ = app t t'} (call-app2 x c₁) c₂ Δ⊆Γ
  = (app t (proj₁ (inline c₁ c₂ Δ⊆Γ)))
    /\ (call-app2 x (proj₂ (inline c₁ c₂ Δ⊆Γ)))
inline (call-app12 c₁ c₃) c₂ Δ⊆Γ
  = (app (proj₁ (inline c₁ c₂ Δ⊆Γ)) (proj₁ (inline c₃ c₂ Δ⊆Γ)))
    /\ (call-app12 (proj₂ (inline c₁ c₂ Δ⊆Γ)) (proj₂ (inline c₃ c₂ Δ⊆Γ)))
inline {t₁ = match t t₁ t₂}(call-match1 c₁ x x₁) c₂ Δ⊆Γ
  = match (proj₁ (inline c₁ c₂ Δ⊆Γ)) t₁ t₂
    /\ call-match1 (proj₂ (inline c₁ c₂ Δ⊆Γ)) x x₁
inline {t₁ = match t t₁ t₂} (call-match2 x c₁ x₁) c₂ Δ⊆Γ
  = match t (proj₁ (inline c₁ c₂ Δ⊆Γ)) t₂
    /\ call-match2 x (proj₂ (inline c₁ c₂ Δ⊆Γ)) x₁
inline {t₁ = match t t₁ t₂} (call-match3 x x₁ c₁) c₂ Δ⊆Γ
  = match t t₁ (proj₁ (inline c₁ c₂ (drop Δ⊆Γ)))
    /\ call-match3 x x₁ (proj₂ (inline c₁ c₂ (drop Δ⊆Γ)))
inline {t₁ = match t t₁ t₂} (call-match12 c₁ c₃ x) c₂ Δ⊆Γ
  = match (proj₁ (inline c₁ c₂ Δ⊆Γ)) (proj₁ (inline c₃ c₂ Δ⊆Γ)) t₂
    /\ call-match12 (proj₂ (inline c₁ c₂ Δ⊆Γ)) (proj₂ (inline c₃ c₂ Δ⊆Γ)) x
inline {t₁ = match t t₁ t₂} (call-match13 c₁ x c₃) c₂ Δ⊆Γ
  = match (proj₁ (inline c₁ c₂ Δ⊆Γ)) t₁ (proj₁ (inline c₃ c₂ (drop Δ⊆Γ)))
    /\ call-match13 (proj₂ (inline c₁ c₂ Δ⊆Γ)) x
      (proj₂ (inline c₃ c₂ (drop Δ⊆Γ)))
inline {t₁ = match t t₁ t₂} (call-match23 x c₁ c₃) c₂ Δ⊆Γ
  = match t (proj₁ (inline c₁ c₂ Δ⊆Γ)) (proj₁ (inline c₃ c₂ (drop Δ⊆Γ)))
    /\ call-match23 x (proj₂ (inline c₁ c₂ Δ⊆Γ))
      (proj₂ (inline c₃ c₂ (drop Δ⊆Γ)))
inline (call-match123 c₁ c₃ c₄) c₂ Δ⊆Γ
  = match (proj₁ (inline c₁ c₂ Δ⊆Γ)) (proj₁ (inline c₃ c₂ Δ⊆Γ))
   (proj₁ (inline c₄ c₂ (drop Δ⊆Γ)))
    /\ call-match123  (proj₂ (inline c₁ c₂ Δ⊆Γ)) (proj₂ (inline c₃ c₂ Δ⊆Γ))
     (proj₂ (inline c₄ c₂ (drop Δ⊆Γ)))
