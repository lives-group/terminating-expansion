module Common.Context where

open import Common.Name using (Name)
open import Common.Type using (Type)

data Context : Set where
    ø : Context
    _,_⦂_ : Context → Name → Type → Context

data _⦂_∈_ : Name → Type → Context → Set where
    here  : ∀{v τ Γ} → v ⦂ τ ∈ (Γ , v ⦂ τ)
    there : ∀{v v' τ τ' Γ} → v ⦂ τ ∈ Γ → v ⦂ τ ∈ (Γ , v' ⦂ τ')