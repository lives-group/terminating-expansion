module R.Semantics where

open import Common.Depth
open import Common.Type
open import Common.Context
open import R.Syntax
open import R.Syntax.Properties

data Value : ∀{Γ τ ρ} → Γ ⊢ τ ⊚ ρ → Set where
  v-zero : ∀{Γ}
    → Value (zero´ {Γ})

  v-suc : ∀{Γ}{t : Γ ⊢ ℕ´ ⊚ ⇓}
    → Value t
    --------------
    → Value (suc´ t)

  v-abs : ∀{Γ τ₁ τ₂}{t : Γ , τ₁ ⊢ τ₂ ⊚ ⇓}
    → Value (abs t)

infix 8 _—→_
data _—→_ : ∀ {Γ τ ρ₁ ρ₂} → (Γ ⊢ τ ⊚ ρ₁) → (Γ ⊢ τ ⊚ ρ₂) → Set where
  ξ-1 : ∀{Γ τ₁ τ₂ ρ}{t₁ t₃ : Γ ⊢ τ₁ ⇒ τ₂ ⊚ ρ}{t₂ : Γ ⊢ τ₁ ⊚ ⇓}
    → t₁ —→ t₃
      ----------------------
    → app t₁ t₂ —→ app t₃ t₂

  ξ-2 : ∀{Γ τ₁ τ₂ ρ}{t₁ : Γ ⊢ τ₁ ⇒ τ₂ ⊚ ρ}{t₂ t₃ : Γ ⊢ τ₁ ⊚ ⇓}
    → Value t₁
    → t₂ —→ t₃
    ----------------
    → app t₁ t₂ —→ app t₁ t₃

  β-abs : ∀{Γ τ₁ τ₂}{t₁ : Γ , τ₁ ⊢ τ₂ ⊚ ⇓}{t₂ : Γ ⊢ τ₁ ⊚ ⇓}
    → Value t₂
    → app (abs t₁) t₂ —→ subs-lemma t₁ t₂

  ξ-suc : ∀{Γ}{t₁ t₂ : Γ ⊢ ℕ´ ⊚ ⇓}
    → t₁ —→ t₂
    → suc´ t₁ —→ suc´ t₂

  ξ-mtc : ∀{Γ τ}{t₁ t₂ : Γ ⊢ ℕ´ ⊚ ⇓}{t₃ : Γ ⊢ τ ⊚ ⇓}{t₄ : Γ , ℕ´ ⊢ τ ⊚ ⇓}
    → t₁ —→ t₂
    → match t₁ t₃ t₄ —→ match t₂ t₃ t₄

  β-zero : ∀{Γ τ}{t₁ : Γ ⊢ τ ⊚ ⇓}{t₂ : Γ , ℕ´ ⊢ τ ⊚ ⇓}
    → match zero´ t₁ t₂ —→ t₁

  β-suc : ∀{Γ τ}{t₁ : Γ ⊢ ℕ´ ⊚ ⇓}{t₂ : Γ ⊢ τ ⊚ ⇓}{t₃ : Γ , ℕ´ ⊢ τ ⊚ ⇓}
    → Value t₁
    → match (suc´ t₁) t₂ t₃ —→ subs-lemma t₃ t₁

  -- TODO: think of a way to solve this problem
  -- β-rec : ∀{Γ τ}{t : Γ , τ ⊢ τ ⊚ ⇓}
  --   → rec t —→ subs-lemma t (rec t)
