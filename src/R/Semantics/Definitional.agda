{-# OPTIONS --safe #-}

module R.Semantics.Definitional where

open import Common.Type
open import Common.Context
open import Common.Fuel
open import R.Syntax.Base
open import R.Syntax

open import Data.Nat     using (ℕ; suc; zero)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; just; nothing)

T⟦_⟧ : Type → Set
T⟦ ℕ´ ⟧      = ℕ
T⟦ τ₁ ⇒ τ₂ ⟧ = T⟦ τ₁ ⟧ → T⟦ τ₂ ⟧

C⟦_⟧ : Context → Set
C⟦ ∅ ⟧     = ⊤
C⟦ Γ , τ ⟧ = T⟦ τ ⟧ × C⟦ Γ ⟧

V⟦_⟧ : ∀{Γ τ} → τ ∈ Γ → C⟦ Γ ⟧ → T⟦ τ ⟧
V⟦ here ⟧    (x /\ env) = x
V⟦ there e ⟧ (x /\ env) = V⟦ e ⟧ env

eval' : ∀{Γ τ} → Γ ⊢ τ → C⟦ Γ ⟧ → T⟦ τ ⟧
eval'  zero´          env = zero
eval' (suc´ t)        env = suc (eval' t env)
eval' (var x)         env = V⟦ x ⟧ env
eval' (abs t)         env = λ z → eval' t (z /\ env)
eval' (app t t₁)      env = (eval' t env) (eval' t₁ env)
eval' (match t t₁ t₂) env
  with eval' t env
... | zero                = eval' t₁ env
... | (suc n)             = eval' t₂ (n /\ env)

-- eval : ∀{Γ τ n} → Fuel n → Γ ⊩ τ → C⟦ Γ ⟧ → Maybe T⟦ τ ⟧
-- eval (gas zero)     t _   = nothing
-- eval (gas (suc f)) (rec t x)  env = {!   !}
-- eval (gas (suc f)) (rec∙ t x) env = {!   !}
