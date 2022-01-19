module R.Syntax.Properties where

open import Common.Depth using (Depth; ⇓; ⇑)
open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_; _⊆_; ∈-subs; keep)
open import R.Syntax

⊆-subs : ∀{Γ Δ τ ρ} → Γ ⊆ Δ → Γ ⊢ τ ⊚ ρ → Δ ⊢ τ ⊚ ρ
⊆-subs Γ⊆Δ zero´      = zero´
⊆-subs Γ⊆Δ (suc´ t)   = suc´ (⊆-subs Γ⊆Δ t)
⊆-subs Γ⊆Δ (var x)    = var (∈-subs Γ⊆Δ x)
⊆-subs Γ⊆Δ (abs t)    = abs (⊆-subs (keep Γ⊆Δ) t)
⊆-subs Γ⊆Δ (app t t₁) = app (⊆-subs Γ⊆Δ t) (⊆-subs Γ⊆Δ t₁)
⊆-subs Γ⊆Δ (match t t₁ t₂) = match (⊆-subs Γ⊆Δ t) (⊆-subs Γ⊆Δ t₁) (⊆-subs (keep Γ⊆Δ) t₂)
⊆-subs Γ⊆Δ (rec t)    = rec (⊆-subs (keep Γ⊆Δ) t)
