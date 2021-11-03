module PCF.TypeSystem where

open import PCF.Syntax
open import Common.Context
open import Common.Name
open import Common.Type

data _⊢_⦂_ : Context → Term → Type → Set where
    tzer : ∀{Γ}     → Γ ⊢ trm zer ⦂ nat
    tsuc : ∀{Γ t}   → Γ ⊢ trm t ⦂ nat → Γ ⊢ trm (suc t) ⦂ nat
    tvar : ∀{Γ v τ} → v ⦂ τ ∈ Γ
                    → Γ ⊢ trm (var v) ⦂ τ
    tabs : ∀{Γ v t τ₁ τ₂} → (Γ , v ⦂ τ₁) ⊢ trm t ⦂ τ₂
                          → Γ ⊢ trm (abs v t) ⦂ (τ₁ ⇒ τ₂)
    tapp : ∀{Γ t t' τ₁ τ₂} → Γ ⊢ trm t ⦂ (τ₁ ⇒ τ₂)
                           → Γ ⊢ trm t' ⦂ τ₁
                           → Γ ⊢ trm (app t t') ⦂ τ₂
    tfix : ∀{Γ v t τ} → (Γ , v ⦂ τ) ⊢ trm t ⦂ τ
                      → Γ ⊢ fix v t ⦂ τ
    tmch : ∀{Γ t t₁ v t₂ τ} → Γ ⊢ trm t ⦂ nat
                            → Γ ⊢ trm t₁ ⦂ τ
                            → (Γ , v ⦂ nat) ⊢ trm t₂ ⦂ τ
                            → Γ ⊢ trm (match t [z⇨ t₁ suc v ⇨ t₂ ]) ⦂ τ
