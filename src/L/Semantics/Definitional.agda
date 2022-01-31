module L.Semantics.Definitional where

open import Common.Type
open import Common.Context
open import L.Syntax
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Maybe using (Maybe; just; nothing)

T⟦_⟧ : Type → Set
T⟦ ℕ´ ⟧     = ℕ
T⟦ τ₁ ⇒ τ₂ ⟧ = T⟦ τ₁ ⟧ → T⟦ τ₂ ⟧

C⟦_⟧ : Context → Set
C⟦ ∅ ⟧     = ⊤
C⟦ Γ , τ ⟧ = T⟦ τ ⟧ × C⟦ Γ ⟧

V⟦_⟧ : ∀{τ Γ} → τ ∈ Γ → C⟦ Γ ⟧ → T⟦ τ ⟧
V⟦ here ⟧    (x /\ xs) = x
V⟦ there e ⟧ (x /\ xs) = V⟦ e ⟧ xs

eval : ∀{Γ τ} → Γ ⊪ τ → C⟦ Γ ⟧ → Maybe T⟦ τ ⟧
eval  error            env = nothing
eval  zero´            env = just zero
eval (suc´ t)          env with eval t env
... | nothing = nothing
... | just x  = just (suc x)
eval (var x)           env = just (V⟦ x ⟧ env)
eval (abs {τ₁ = τ₁} t) env = {!   !}
eval (app t t₁)        env with eval t env | eval t₁ env
... | just x | just y = just (x y)
... | _      | _      = nothing
eval (match t t₁ t₂)   env with eval t env
... | just zero    = eval t₁ env
... | just (suc x) = eval t₂ (x /\ env)
... | nothing      = nothing
