module R.Semantics where

open import Common.Depth
open import Common.Type
open import Common.Context
open import R.Syntax

data Value : ∀{Γ τ ρ} → Γ ⊢ τ ⊚ ρ → Set where
  v-zero : ∀{Γ}
    → Value (zero´ {Γ})

  v-suc : ∀{Γ}{t : Γ ⊢ ℕ´ ⊚ ⇓}
    → Value t
    --------------
    → Value (suc´ t)

  v-abs : ∀{Γ τ₁ τ₂}{t : Γ , τ₁ ⊢ τ₂ ⊚ ⇓}
    → Value (abs t)
