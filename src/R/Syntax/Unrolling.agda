module R.Syntax.Unrolling where

{-
Inlines term t₂ into t₁ replacing τ₂.
Inlining preserves variable calls.
-}
postulate inline : ∀{Γ Δ τ₁ τ₂}{t₁ : Γ ⊢ τ₁ ⊚ ⇓}{t₂ : Δ ⊢ τ₂ ⊚ ⇓}
  → τ₂ called-in t₁
  → τ₂ called-in t₂
  → Δ ⊆ Γ
  → ∃ (λ (t₃ : Γ ⊢ τ₁ ⊚ ⇓) → τ₂ called-in t₃)
