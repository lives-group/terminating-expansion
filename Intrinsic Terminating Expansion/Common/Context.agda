module Common.Context where

open import Common.Type using (Type)
open import Common.Name using (Name)

infixl 15 _,_⦂_
infix  10 _⦂_∈_

data Context : Set where
  ø   : Context
  _,_⦂_ : Context → Name → Type → Context

data _⦂_∈_ : Name → Type → Context → Set where
  here  : ∀{Γ τ v} → v ⦂ τ ∈ Γ , v ⦂ τ
  there : ∀{Γ τ τ' v v'} → v ⦂ τ ∈ Γ → v ⦂ τ ∈ Γ , v' ⦂ τ'
