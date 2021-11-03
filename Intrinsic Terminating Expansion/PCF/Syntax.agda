module PCF.Syntax where

open import Common.Context using (Context; ø; _,_⦂_; _⦂_∈_; here; there)
open import Common.Type using (Type; nat; _⇒_)
open import Common.Name using (Name)

infix 9 _⊢_

data _⊢_ : Context → Type → Set where
  zer : ∀{Γ} → Γ ⊢ nat
  suc : ∀{Γ} → Γ ⊢ nat → Γ ⊢ nat
  var : ∀{Γ τ v} → v ⦂ τ ∈ Γ → Γ ⊢ τ
  abs : ∀{Γ τ τ'} (v : Name) → Γ , v ⦂ τ ⊢ τ' → Γ ⊢ τ ⇒ τ'
  app : ∀{Γ τ τ'} → Γ ⊢ τ ⇒ τ' → Γ ⊢ τ → Γ ⊢ τ'
  match_[z⇨_suc_⇨_] : ∀{Γ τ} → Γ ⊢ nat → Γ ⊢ τ → (v : Name) → Γ , v ⦂ nat ⊢ τ → Γ ⊢ τ
  fix : ∀{Γ τ} (v : Name) → Γ , v ⦂ τ ⊢ τ → Γ ⊢ τ
