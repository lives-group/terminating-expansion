module PCF.Syntax where

open import Common.Context using (Context; ø; _,_⦂_; _⦂_∈_; here; there)
open import Common.Type using (Type; nat; _⇒_)
open import Common.Name using (Name)

infix 9 _⊢_

{-
  A Depth indicates if an expression has
  let_in_ constructions. This is useful because
  in this simply typed calculus, only such expressions
  can have recursion. The Depth ⇑ indicates the presence
  of a let_in_ in the expression. The Depth ⇓ indicates its
  absence.
-}
data Depth : Set where
  ⇑ : Depth
  ⇓ : Depth

data _⊢_ : Context → Type → Depth → Set where
  zer : ∀{Γ} → (Γ ⊢ nat) ⇓
  suc : ∀{Γ} → (Γ ⊢ nat) ⇓ → (Γ ⊢ nat) ⇓
  var : ∀{Γ τ} (v : Name) → v ⦂ τ ∈ Γ → (Γ ⊢ τ) ⇓
  abs : ∀{Γ τ τ'} (v : Name) → (Γ , v ⦂ τ ⊢ τ') ⇓ → (Γ ⊢ τ ⇒ τ') ⇓
  app : ∀{Γ τ τ'} → (Γ ⊢ τ ⇒ τ') ⇓ → (Γ ⊢ τ) ⇓ → (Γ ⊢ τ') ⇓
  match_[z⇨_suc_⇨_] : ∀{Γ τ} → (Γ ⊢ nat) ⇓ → (Γ ⊢ τ) ⇓ → (v : Name) → (Γ , v ⦂ nat ⊢ τ) ⇓ → (Γ ⊢ τ) ⇓
  let´_←_in´_ : ∀{Γ τ τ' ρ} (v : Name) → (Γ , v ⦂ τ ⊢ τ) ⇓ → (Γ , v ⦂ τ ⊢ τ') ρ → (Γ ⊢ τ') ⇑

infix 9 _⊢´_⊚_

_⊢´_⊚_ : Context → Type → Depth → Set
Γ ⊢´ τ ⊚ ρ = (Γ ⊢ τ) ρ
