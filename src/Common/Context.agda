module Common.Context where

open import Common.Type using (Type)

infixr 15 _,_
data Context : Set where
  ø   : Context
  _,_ : Context → Type → Context

infix  10 _∈_
data _∈_ : Type → Context → Set where
  here : ∀{Γ τ}→ τ ∈ Γ , τ
  there : ∀{Γ τ₁ τ₂} → τ₁ ∈ Γ → τ₁ ∈ Γ , τ₂

infix 9 _⊆_
data _⊆_ : Context → Context → Set where
  empty : ø ⊆ ø
  keep  : ∀{Γ Δ τ} → Γ ⊆ Δ → Γ , τ ⊆ Δ , τ
  drop  : ∀{Γ Δ τ} → Γ ⊆ Δ → Γ ⊆ Δ , τ

∈-subs : ∀{Γ Δ τ} → Γ ⊆ Δ → τ ∈ Γ → τ ∈ Δ
∈-subs empty ()
∈-subs (keep Γ⊆Δ)  here       = here
∈-subs (keep Γ⊆Δ) (there τ∈Γ) = there (∈-subs Γ⊆Δ τ∈Γ)
∈-subs (drop Γ⊆Δ)  τ∈Γ        = there (∈-subs Γ⊆Δ τ∈Γ)
