module PCF.Semantics where

open import Common.Depth
open import Common.Name
open import Common.Type
open import Common.Context
open import PCF.Syntax
open import PCF.Syntax.Properties
open import PCF.Syntax.Unrolling
open import Data.Nat using (ℕ; zero; _+_)
open import Data.Product using (∃; _×_; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)

data Variable : Name → Set where
  #_ : ∀(v : Name) → Variable v

Τ⟦_⟧ : Type → Set
Τ⟦ nat ⟧ = ℕ
Τ⟦ τ₁ ⇒ τ₂ ⟧ = Τ⟦ τ₁ ⟧ → Τ⟦ τ₂ ⟧

γ⟦_⟧ : Context → Set
γ⟦ ø ⟧ = ⊤
γ⟦ Γ , v ⦂ τ ⟧ = ((Variable v) × Τ⟦ τ ⟧) × γ⟦ Γ ⟧

v⟦_⟧ : ∀{Γ v τ} → v ⦂ τ ∈ Γ → γ⟦ Γ ⟧ → Τ⟦ τ ⟧
v⟦ here ⟧    ctx = proj₂ (proj₁ ctx)
v⟦ there p ⟧ ctx = v⟦ p ⟧ (proj₂ ctx)

data Value : Set where
  vnat : ℕ → Value
  vabs : ∀{Γ τ τ'} → List Value → (v : Name) →  Γ , v ⦂ τ ⊢´ τ' ⊚ ⇓ → Value

Environment : Set
Environment = List Value

mutual
  data _has-type_ : Value → Type → Set where
    v-nat : ∀{n} → (vnat n) has-type nat
    v-abs : ∀{Γ H v τ τ'} → Γ ⊨ H → (t : Γ , v ⦂ τ ⊢´ τ' ⊚ ⇓) → (vabs H v t) has-type (τ ⇒ τ')

  data _⊨_ : Context → Environment → Set where
    nil  : ø ⊨ []
    cons : ∀{Γ H τ v vl} → vl has-type τ → Γ ⊨ H → (Γ , v ⦂ τ) ⊨ (vl ∷ H)
