{-# OPTIONS --safe #-}

module L.Semantics.Normalization where

open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_; here; there; ∅)
open import L.Syntax
open import L.Syntax.Properties
open import L.Semantics

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃; ∄; proj₁; proj₂) renaming (_,_ to _/\_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

{-
Tait's Normalization Proof as seen in Pierce (2002) and
https://github.com/gergoerdi/syntactic-stlc/blob/master/STLC/Norm.agda
-}

data Halts : ∀{Γ τ} → Γ ⊪ τ → Set where
  halts : ∀{Γ τ}{t t' : Γ ⊪ τ} → NormalForm t' → t —↠ t' → Halts t

nf-halts : ∀{Γ τ}{t : Γ ⊪ τ} → NormalForm t → Halts t
nf-halts {t = t}      (value x) = halts (value x) (t ∎)
nf-halts {t = .error}  nf-err   = halts nf-err (error ∎)

NF : ∀ {a b} {A : Set a} → Rel A b → A → Set _
NF next x = ∄ (next x)

nf-¬-—→ : ∀{Γ τ t}{t' : Γ ⊪ τ} → NormalForm {Γ} {τ} t → ¬ (t —→ t')
nf-¬-—→ (value v-zero) ()
nf-¬-—→ (value v-abs)  ()
nf-¬-—→  nf-err        ()
nf-¬-—→ (value (v-suc x)) (ξ-suc y) = nf-¬-—→ (value x) y

deterministic : ∀{Γ τ}{t₁ t₂ t₃ : Γ ⊪ τ} → t₁ —→ t₂ → t₁ —→ t₃ → t₂ ≡ t₃
deterministic (ξ-1 x) (ξ-1 y) rewrite deterministic x y = refl
deterministic (ξ-1 x) (ξ-2 x₁ y)     = ⊥-elim (nf-¬-—→ (value x₁) x)
deterministic (ξ-1 x) (β-err3 x₁)    = ⊥-elim (nf-¬-—→ (value x₁) x)
deterministic (ξ-2 x x₁) (ξ-1 y)     = ⊥-elim (nf-¬-—→ (value x) y)
deterministic (ξ-2 x x₁) (ξ-2 x₂ y) rewrite deterministic x₁ y = refl
deterministic (ξ-2 x x₁) (β-abs x₂)  = ⊥-elim (nf-¬-—→ (value x₂) x₁)
deterministic (β-abs x) (ξ-2 x₁ y)   = ⊥-elim (nf-¬-—→ (value x) y)
deterministic (β-abs x) (β-abs x₁)   = refl
deterministic (ξ-suc x) (ξ-suc y) rewrite deterministic x y = refl
deterministic (ξ-mtc x) (ξ-mtc y) rewrite deterministic x y = refl
deterministic (ξ-mtc x) (β-suc x₁)   = ⊥-elim (nf-¬-—→ (value (v-suc x₁)) x)
deterministic β-zero β-zero          = refl
deterministic (β-suc x) (ξ-mtc y)    = ⊥-elim (nf-¬-—→ (value (v-suc x)) y)
deterministic (β-suc x) (β-suc x₁)   = refl
deterministic β-err1 β-err1          = refl
deterministic β-err2 β-err2          = refl
deterministic (β-err3 x) (ξ-1 y)     = ⊥-elim (nf-¬-—→ (value x) y)
deterministic (β-err3 x) (β-err3 x₁) = refl
deterministic β-err4 β-err4          = refl

mutual
  data Saturated : ∀{τ} → ∅ ⊪ τ → Set where
    sat : ∀{τ}{t : ∅ ⊪ τ} → Halts t → Saturated' _ t → Saturated t

  data Saturated' : (τ : Type) → ∅ ⊪ τ → Set where
    s-nat : ∀{t : ∅ ⊪ ℕ´} → Saturated' ℕ´ t
    s-fun : ∀{τ₁ τ₂}{t : ∅ ⊪ τ₁ ⇒ τ₂} → ∀{e} → Saturated e → Saturated' (τ₂) (app t e)

sat-halts : ∀ {τ}{t : ∅ ⊪ τ} → Saturated t → Halts t
sat-halts (sat h _) = h

infix 0 _↔_
record _↔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _↔_

—→-halts-→ : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Halts t → Halts t'
—→-halts-→ {t = t} x (halts nf (_ ∎)) = ⊥-elim (nf-¬-—→ nf x)
—→-halts-→ {t = t} x (halts nf (t —→⟨ x₂ ⟩ y)) rewrite deterministic x x₂
  = halts nf y

—→-halts-← : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Halts t' → Halts t
—→-halts-← {t = t} x (halts nf y) = halts nf (t —→⟨ x ⟩ y)

—→-halts : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Halts t ↔ Halts t'
—→-halts x = record {to = —→-halts-→ x; from = —→-halts-← x}
