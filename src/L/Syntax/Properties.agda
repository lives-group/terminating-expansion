{-# OPTIONS --safe #-}
module L.Syntax.Properties where

open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_; here; there)
open import L.Syntax

{- plfa substitution properties -}
ext : ∀ {Γ Δ}
  → (∀ {τ₁} → τ₁ ∈ Γ → τ₁ ∈ Δ)
    ---------------------------------
  → (∀ {τ₁ τ₂} → τ₁ ∈ Γ , τ₂ → τ₁ ∈ Δ , τ₂)
ext f  here       =  here
ext f (there τ∈Γ) =  there (f τ∈Γ)

rename : ∀ {Γ Δ}
  → (∀ {τ} → τ ∈ Γ → τ ∈ Δ)
    -----------------------
  → (∀ {τ} → Γ ⊪ τ → Δ ⊪ τ)
rename f  error     = error
rename f  zero´     = zero´
rename f (suc´ t)   = suc´ (rename f t)
rename f (var x)    = var (f x)
rename f (abs t)    = abs (rename (ext f) t)
rename f (app t t₁) = app (rename f t) (rename f t₁)
rename f (match t t₁ t₂) = match (rename f t) (rename f t₁) (rename (ext f) t₂)

exts : ∀ {Γ Δ}
  → (∀ {τ₁} → τ₁ ∈ Γ → Δ ⊪ τ₁)
    -------------------------------------------
  → (∀ {τ₁ τ₂} → τ₁ ∈ Γ , τ₂ → Δ , τ₂ ⊪ τ₁)
exts f here      = var here
exts f (there x) = rename there (f x)

subst : ∀ {Γ Δ}
  → (∀ {τ} → τ ∈ Γ → Δ ⊪ τ)
    --------------------------------
  → (∀ {τ} → Γ ⊪ τ → Δ ⊪ τ)
subst f  error     = error
subst f  zero´     = zero´
subst f (suc´ t)   = suc´ (subst f t)
subst f (var x)    = f x
subst f (abs t)    = abs (subst (exts f) t)
subst f (app t t₁) = app (subst f t) (subst f t₁)
subst f (match t t₁ t₂) = match (subst f t) (subst f t₁) (subst (exts f) t₂)

subs-lemma : ∀ {Γ τ₁ τ₂} → Γ , τ₂ ⊪ τ₁ → Γ ⊪ τ₂ → Γ ⊪ τ₁
subs-lemma {Γ} {τ₁} {τ₂} t₁ t₂
  = subst {Γ , τ₂} {Γ} (λ {here → t₂ ; (there x) → var x}) {τ₁} t₁
{- end of plfa substitution properties -}
