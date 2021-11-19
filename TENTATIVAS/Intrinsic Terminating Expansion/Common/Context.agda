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

{-
Here, _⊆_ is the Order Preserving Embedding relation.
It means that a context is contained inside another,
where the order of elements are all preserved.
Based on Andras Kovacs STLC-NbE
-}
infix 9 _⊆_

data _⊆_ : Context → Context → Set where
  empty : ø ⊆ ø
  keep  : ∀{v₁ τ₁ Γ Δ} → Γ ⊆ Δ → Γ , v₁ ⦂ τ₁ ⊆ Δ , v₁ ⦂ τ₁
  drop  : ∀{v₁ τ₁ Γ Δ} → Γ ⊆ Δ → Γ ⊆ Δ , v₁ ⦂ τ₁

∈-substitution : ∀{Γ Δ x τ} → Γ ⊆ Δ → x ⦂ τ ∈ Γ → x ⦂ τ ∈ Δ
∈-substitution (keep p) here = here
∈-substitution (keep p) (there e) = there (∈-substitution p e)
∈-substitution (drop p) e = there (∈-substitution p e)

⊆-refl : ∀{Γ} → Γ ⊆ Γ
⊆-refl {ø} = empty
⊆-refl {Γ , x ⦂ x₁} = keep ⊆-refl
