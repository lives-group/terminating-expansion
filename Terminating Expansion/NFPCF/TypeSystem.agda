module NFPCF.TypeSystem where

open import NFPCF.Syntax 
open import Common.Context
open import Common.Name 
open import Common.Type

data _⊢_⦂_ : Context → Term → Type → Set where
    tufn : ∀{Γ}     → Γ ⊢ ufn ⦂ nat 
    tzer : ∀{Γ}     → Γ ⊢ zer ⦂ nat
    tsuc : ∀{Γ t}   → Γ ⊢ t ⦂ nat → Γ ⊢ suc t ⦂ nat
    tvar : ∀{Γ v τ} → v ⦂ τ ∈ Γ 
                    → Γ ⊢ var v ⦂ τ
    tabs : ∀{Γ v t τ₁ τ₂} → (Γ , v ⦂ τ₁) ⊢ t ⦂ τ₂ 
                          → Γ ⊢ abs v t ⦂ (τ₁ ⇒ τ₂)
    tapp : ∀{Γ t t' τ₁ τ₂} → Γ ⊢ t ⦂ (τ₁ ⇒ τ₂) 
                           → Γ ⊢ t' ⦂ τ₁ 
                           → Γ ⊢ app t t' ⦂ τ₂
    tout : ∀{Γ τ} → Γ ⊢ out ⦂ τ
    tmch : ∀{Γ t t₁ v t₂ τ} → Γ ⊢ t ⦂ nat 
                            → Γ ⊢ t₁ ⦂ τ 
                            → (Γ , v ⦂ nat) ⊢ t₂ ⦂ τ 
                            → Γ ⊢ match t [z⇨ t₁ suc v ⇨ t₂ ] ⦂ τ
