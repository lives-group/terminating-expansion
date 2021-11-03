module PCF.Syntax.Properties where

open import Common.Type
open import Common.Context
open import Common.Name
open import PCF.Syntax
open import Data.Bool using (Bool; true; false) renaming (_∨_ to _∥_)

is-var-used : ∀{Γ τ} → Name → Γ ⊢ τ → Bool
is-var-used v (var {v = v'} x) = v equals v'
is-var-used v (fix v' t) = is-var-used v t
is-var-used v (abs v' t) = is-var-used v t
is-var-used v (app t t') = is-var-used v t ∥ is-var-used v t'
is-var-used v (match t [z⇨ t₁ suc v' ⇨ t₂ ]) = is-var-used v t ∥ is-var-used v t₁ ∥ is-var-used v t₂
is-var-used _ _ = false

is-recursive : ∀{Γ τ} → Γ ⊢ τ → Bool
is-recursive (abs v t)  = is-recursive t
is-recursive (app t t₁) = is-recursive t ∥ is-recursive t₁
is-recursive match t [z⇨ t₁ suc v ⇨ t₂ ] = is-recursive t ∥ is-recursive t₁ ∥ is-recursive t₂
is-recursive (fix v t)  = is-var-used v t ∥ is-recursive t
is-recursive _  = false
