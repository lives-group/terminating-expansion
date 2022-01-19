module R.Syntax where

open import Common.Depth using (Depth; ⇓; ⇑)
open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_)

infix 9 _⊢_⊚_
data _⊢_⊚_ : Context → Type → Depth → Set where
  zero´ : ∀{Γ}
    → Γ ⊢ ℕ´ ⊚ ⇓

  suc´ : ∀{Γ}
    → Γ ⊢ ℕ´ ⊚ ⇓
    ---------
    → Γ ⊢ ℕ´ ⊚ ⇓

  var : ∀{Γ τ}
    → τ ∈ Γ
    ---------
    → Γ ⊢ τ ⊚ ⇓

  abs : ∀{Γ τ₁ τ₂}
    → Γ , τ₁ ⊢ τ₂ ⊚ ⇓
    ------------------
    → Γ ⊢ τ₁ ⇒ τ₂ ⊚ ⇓

  app : ∀{Γ τ₁ τ₂ ρ}
    → Γ ⊢ τ₁ ⇒ τ₂ ⊚ ρ
    → Γ ⊢ τ₁ ⊚ ⇓
    -------------
    → Γ ⊢ τ₂ ⊚ ρ

  match : ∀{Γ τ}
    → Γ ⊢ ℕ´ ⊚ ⇓
    → Γ ⊢ τ ⊚ ⇓
    → Γ , ℕ´ ⊢ τ ⊚ ⇓
    ----------------
    → Γ ⊢ τ ⊚ ⇓

  rec : ∀{Γ τ}
    → Γ , τ ⊢ τ ⊚ ⇓
    ----------------
    → Γ ⊢ τ ⊚ ⇑
