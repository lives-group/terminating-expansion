module L.Syntax.Properties where

open import Common.Type
open import Common.Context
open import Common.Name
open import Common.Depth using (Depth; ⇑; ⇓)
open import L.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Nullary using (¬_; yes; no)
open import Data.String using (_≟_)
open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Empty using (⊥-elim)

{-
Evidence for variable calls
-}

data _⦂_not-called-in_ : ∀{Γ τ} → Name → Type → Γ ⊢´ τ ⊚ ⇓ → Set where
  no-call-err   : ∀{Γ v τ τ'} → v ⦂ τ not-called-in (err {Γ} {τ'})
  no-call-zer   : ∀{Γ v τ} → v ⦂ τ not-called-in (zer {Γ})
  no-call-varn  : ∀{Γ v₁ v₂ τ τ'}{t : v₂ ⦂ τ ∈ Γ} → ¬(v₁ ≡ v₂)
                → v₁ ⦂ τ' not-called-in (var v₂ t)
  no-call-vart  : ∀{Γ v τ τ'}{t : v ⦂ τ ∈ Γ} → ¬(τ' ≡ τ)
                → v ⦂ τ' not-called-in (var v t)
  no-call-suc   : ∀{Γ v τ'}{t : Γ ⊢´ nat ⊚ ⇓}
                → v ⦂ τ' not-called-in t → v ⦂ τ' not-called-in (suc t)
  no-call-abs   : ∀{Γ v v' τ τ' τ₁}{t : Γ , v' ⦂ τ ⊢´ τ' ⊚ ⇓}
                → v ⦂ τ₁ not-called-in t → v ⦂ τ₁ not-called-in (abs v' t)
  no-call-app   : ∀{Γ v τ τ' τ₁}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓}
                → v ⦂ τ₁ not-called-in t → v ⦂ τ₁ not-called-in t'
                → v ⦂ τ₁ not-called-in (app t t')
  no-call-match : ∀{Γ v v' τ τ₁}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
                → v ⦂ τ₁ not-called-in t → v ⦂ τ₁ not-called-in t₁ → v ⦂ τ₁ not-called-in t₂
                → v ⦂ τ₁ not-called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])

data _⦂_called-in_ : ∀{Γ τ} → Name → Type → Γ ⊢´ τ ⊚ ⇓ → Set where
  call-var : ∀{Γ τ v}{t : v ⦂ τ ∈ Γ} → v ⦂ τ called-in (var v t)
  call-suc : ∀{Γ v τ}{t : Γ ⊢´ nat ⊚ ⇓}
              → v ⦂ τ called-in t → v ⦂ τ called-in (suc t)
  call-abs : ∀{Γ v v' τ τ' τ₁}{t : Γ , v' ⦂ τ ⊢´ τ' ⊚ ⇓}
              → v ⦂ τ₁ called-in t → v ⦂ τ₁ called-in (abs v' t)
  call-app1 : ∀{Γ v τ τ' τ₁}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓}
              → v ⦂ τ₁ called-in t → v ⦂ τ₁ not-called-in t' → v ⦂ τ₁ called-in (app t t')
  call-app2 : ∀{Γ v τ τ' τ₁}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓}
              → v ⦂ τ₁ not-called-in t → v ⦂ τ₁ called-in t' → v ⦂ τ₁ called-in (app t t')
  call-app12 : ∀{Γ v τ τ' τ₁}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓}
               → v ⦂ τ₁ called-in t → v ⦂ τ₁ called-in t' → v ⦂ τ₁ called-in (app t t')
  call-mtc1 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' called-in t → v ⦂ τ' not-called-in t₁ → v ⦂ τ' not-called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc2 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' not-called-in t → v ⦂ τ' called-in t₁ → v ⦂ τ' not-called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc3 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' not-called-in t → v ⦂ τ' not-called-in t₁ → v ⦂ τ' called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc12 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' called-in t → v ⦂ τ' called-in t₁ → v ⦂ τ' not-called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc13 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' called-in t → v ⦂ τ' not-called-in t₁ → v ⦂ τ' called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc23 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' not-called-in t → v ⦂ τ' called-in t₁ → v ⦂ τ' called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc123 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
                → v ⦂ τ' called-in t → v ⦂ τ' called-in t₁ → v ⦂ τ' called-in t₂
                → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])

{-
It is decidable to check a var calling in a term
-}
data CallTotal : ∀{Γ τ} → Name → Type → Γ ⊢´ τ ⊚ ⇓ → Set where
  is-called  : ∀{Γ v τ τ'}{t : Γ ⊢´ τ' ⊚ ⇓}
               → v ⦂ τ called-in t → CallTotal v τ t
  not-called : ∀{Γ v τ τ'}{t : Γ ⊢´ τ' ⊚ ⇓}
               → v ⦂ τ not-called-in t → CallTotal v τ t

dec-called : ∀{Γ τ'}(v : Name)(τ : Type)(t : Γ ⊢´ τ' ⊚ ⇓) → CallTotal v τ t
dec-called v τ err = not-called no-call-err
dec-called v τ zer = not-called no-call-zer
dec-called {τ' = τ'} v τ (var v₁ x) with v ≟ v₁ | dec-equals τ τ'
dec-called {τ' = τ'} v τ (var v₁ x) | yes refl | yes refl = is-called call-var
dec-called {τ' = τ'} v τ (var v₁ x) | yes refl | no τ≢τ₁  = not-called (no-call-vart τ≢τ₁)
dec-called {τ' = τ'} v τ (var v₁ x) | no v≢v₁  | _        = not-called (no-call-varn v≢v₁)
dec-called v τ (suc t) with dec-called v τ t
... | is-called x  = is-called (call-suc x)
... | not-called x = not-called (no-call-suc x)
dec-called v τ (abs v₁ t) with dec-called v τ t
... | is-called  x = is-called (call-abs x)
... | not-called x = not-called (no-call-abs x)
dec-called v τ (app t t₁) with dec-called v τ t | dec-called v τ t₁
dec-called v τ (app t t₁) | is-called x  | is-called x₁  = is-called (call-app12 x x₁)
dec-called v τ (app t t₁) | is-called x  | not-called x₁ = is-called (call-app1 x x₁)
dec-called v τ (app t t₁) | not-called x | is-called x₁  = is-called (call-app2 x x₁)
dec-called v τ (app t t₁) | not-called x | not-called x₁ = not-called (no-call-app x x₁)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] with dec-called v τ t | dec-called v τ t₁ | dec-called v τ t₂
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | is-called x  | is-called x₁  | is-called x₂  = is-called (call-mtc123 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | is-called x  | is-called x₁  | not-called x₂ = is-called (call-mtc12 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | is-called x  | not-called x₁ | is-called x₂  = is-called (call-mtc13 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | is-called x  | not-called x₁ | not-called x₂ = is-called (call-mtc1 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | not-called x | is-called x₁  | is-called x₂  = is-called (call-mtc23 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | not-called x | is-called x₁  | not-called x₂ = is-called (call-mtc2 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | not-called x | not-called x₁ | is-called x₂  = is-called (call-mtc3 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | not-called x | not-called x₁ | not-called x₂ = not-called (no-call-match x x₁ x₂)
