module NPCF.Semantics where

open import Common.Name
open import Common.Type
open import Common.Depth
open import Common.Context
open import NPCF.Syntax

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Data.Product using (∃; _×_; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)

T⟦_⟧ : Type → Set
T⟦ nat ⟧ = ℕ
T⟦ τ₁ ⇒ τ₂ ⟧ = T⟦ τ₁ ⟧ → T⟦ τ₂ ⟧

C⟦_⟧ : Context → Set
C⟦ ø ⟧ = ⊤
C⟦ Γ , v ⦂ τ ⟧ = T⟦ τ ⟧ × C⟦ Γ ⟧

V⟦_⟧ : ∀ {v τ Γ} → v ⦂ τ ∈ Γ → C⟦ Γ ⟧ → T⟦ τ ⟧
V⟦ here ⟧    env = proj₁ env
V⟦ there x ⟧ env = V⟦ x ⟧ (proj₂ env)

-- eval : ∀{Γ τ ρ} → Γ ⊢´ τ ⊚ ρ → C⟦ Γ ⟧ → T⟦ τ ⟧
-- eval
