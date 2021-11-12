module PCF.Syntax.Properties where

open import Common.Type
open import Common.Context
open import Common.Name
open import PCF.Syntax
open import Relation.Nullary using (¬_)

data _called-in_ : ∀{Γ τ} → Name → Γ ⊢´ τ ⊚ ⇓ → Set where
  call-var  : ∀{Γ τ v}{t : v ⦂ τ ∈ Γ} → v called-in (var v t)
  call-suc  : ∀{Γ v}{t : Γ ⊢´ nat ⊚ ⇓} → v called-in t → v called-in (suc t)
  call-abs  : ∀{Γ v v' τ τ'}{t : Γ , v' ⦂ τ ⊢´ τ' ⊚ ⇓} → v called-in t → v called-in (abs v' t)
  call-app1 : ∀{Γ v τ τ'}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓} → v called-in t → v called-in (app t t')
  call-app2 : ∀{Γ v τ τ'}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓} → v called-in t' → v called-in (app t t')
  call-mtc1 : ∀{Γ v v' τ}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v called-in t → v called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc2 : ∀{Γ v v' τ}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v called-in t₁ → v called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc3 : ∀{Γ v v' τ}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v called-in t₂ → v called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])

data _not-called-in_ : ∀{Γ τ} → Name → Γ ⊢´ τ ⊚ ⇓ → Set where
  no-call-zer : ∀{Γ v} → v not-called-in (zer {Γ})
  no-call-var : ∀{Γ v₁ v₂ τ}{t : v₂ ⦂ τ ∈ Γ} → ¬(v₁ equals v₂) → v₁ not-called-in (var v₂ t)
  no-call-suc : ∀{Γ v}{t : Γ ⊢´ nat ⊚ ⇓} → v not-called-in t → v not-called-in (suc t)
  no-call-abs : ∀{Γ v v' τ τ'}{t : Γ , v' ⦂ τ ⊢´ τ' ⊚ ⇓} → v not-called-in t → v not-called-in (abs v' t)
  no-call-app : ∀{Γ v τ τ'}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓}
                → v not-called-in t → v not-called-in t' → v not-called-in (app t t')
  no-call-match : ∀{Γ v v' τ}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
                → v not-called-in t → v not-called-in t₁ → v not-called-in t₂ → v not-called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])

data _▸rec_ : ∀{Γ τ ρ} → Γ ⊢´ τ ⊚ ρ → Context → Set where
  no-rec-⇓ : ∀{Γ τ}{t : Γ ⊢´ τ ⊚ ⇓} → t ▸rec ø
  no-rec-⇑ : ∀{Γ Δ τ v τ' ρ}{t : Γ , v ⦂ τ ⊢´ τ' ⊚ ρ}{t' : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}
             → t ▸rec Δ → v not-called-in t' → (let´ v ← t' in´ t) ▸rec Δ
  rec-⇑    : ∀{Γ Δ τ v τ' ρ}{t : Γ , v ⦂ τ ⊢´ τ' ⊚ ρ}{t' : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}
             → t ▸rec Δ → v called-in t' → (let´ v ← t' in´ t) ▸rec (Δ , v ⦂ τ)


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

context-substitution : ∀{Γ Δ τ ρ} → Γ ⊆ Δ → Γ ⊢´ τ ⊚ ρ → Δ ⊢´ τ ⊚ ρ
context-substitution p zer = zer
context-substitution p (suc t) = suc (context-substitution p t)
context-substitution p (var v x) = var v (∈-substitution p x)
context-substitution p (abs v t) = abs v (context-substitution (keep p) t)
context-substitution p (app t t₁) = app (context-substitution p t) (context-substitution p t₁)
context-substitution p match t [z⇨ t₁ suc v ⇨ t₂ ] = match context-substitution p t
  [z⇨ context-substitution p t₁
   suc v ⇨ context-substitution (keep p) t₂ ]
context-substitution p (let´ v ← t in´ t₁) = let´ v ← context-substitution (keep p) t in´ context-substitution (keep p) t₁
