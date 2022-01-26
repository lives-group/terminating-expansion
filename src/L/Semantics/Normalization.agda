{-# OPTIONS --safe #-}

module L.Semantics.Normalization where

open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_; here; there; ∅)
open import L.Syntax
open import L.Syntax.Properties
open import L.Semantics

open import Data.Product using (∃; ∄; proj₁; proj₂; _×_) renaming (_,_ to _/\_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id)
{-
Tait's Normalization Proof as seen in Pierce (2002) and
https://github.com/gergoerdi/syntactic-stlc/blob/master/STLC/Norm.agda
-}

{-
   The —→ and —↠ are defined in L.Semantics and
   they follow PLFA with additional rules for error.
   Definition of Value and NormalForm are also on L.Semantics.
   The syntax of System L is in L.Syntax
   Substitution Lemma (following PLFA) for System L is in L.Syntax.Properties
-}

-- A term halts if there is a normal form to which it evaluates
data Halts : ∀{Γ τ} → Γ ⊪ τ → Set where
  halts : ∀{Γ τ}{t t' : Γ ⊪ τ} → NormalForm t' → t —↠ t' → Halts t

-- Trivially, normal forms halts
nf-halts : ∀{Γ τ}{t : Γ ⊪ τ} → NormalForm t → Halts t
nf-halts {t = t}      (value x) = halts (value x) (t ∎)
nf-halts {t = .error}  nf-err   = halts nf-err (error ∎)

-- This is the defitinion of NormalForm used on georgi's repo, ignore it
-- NF : ∀ {a b} {A : Set a} → Rel A b → A → Set _
-- NF next x = ∄ (next x)

-- NormalForms do not reduce (Following PLFA). Needed for proving determinism
nf-¬-—→ : ∀{Γ τ t}{t' : Γ ⊪ τ} → NormalForm {Γ} {τ} t → ¬ (t —→ t')
nf-¬-—→ (value v-zero) ()
nf-¬-—→ (value v-abs)  ()
nf-¬-—→  nf-err        ()
nf-¬-—→ (value (v-suc x)) (ξ-suc y) = nf-¬-—→ (value x) y

-- The evaluation relation is deterministic. This is needed to prove halt preservation
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

{-
This definition of Saturated is from georgi's repo. I don't really understand it
but the definition I tried, commented below, is accused to be not strictly positive
by Agda.
-}
mutual
  Saturated : ∀{τ} → ∅ ⊪ τ → Set
  Saturated t = Halts t × Saturated' _ t

  Saturated' : ∀(τ : Type) → ∅ ⊪ τ → Set
  Saturated' (τ₁ ⇒ τ₂) f  = ∀{e} → Saturated e → Saturated (app f e)
  Saturated'  ℕ´        _  = ⊤

    -- data Saturated : ∀{τ} → ∅ ⊪ τ → Set where
    --   s-nat : ∀{t : ∅ ⊪ ℕ´} → Saturated' ℕ´ t
    --   s-fun : ∀{τ₁ τ₂}{t : ∅ ⊪ τ₁ ⇒ τ₂} → ∀{e} → Saturated e → Saturated' (τ₂) (app t e)

-- A saturated term halts. Trivial, because it is part of the definition.
sat-halts : ∀ {τ}{t : ∅ ⊪ τ} → Saturated t → Halts t
sat-halts = proj₁

-- My own definition for biconditional because georgi uses some deep stuff from
-- the standard library
infix 0 _↔_
record _↔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
open _↔_

-- The evaluation relation preserves halting (-->)
—→-halts-→ : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Halts t → Halts t'
—→-halts-→ {t = t} x (halts nf (_ ∎)) = ⊥-elim (nf-¬-—→ nf x)
—→-halts-→ {t = t} x (halts nf (t —→⟨ x₂ ⟩ y)) rewrite deterministic x x₂
  = halts nf y

-- The evaluation relation preserves halting (<--)
—→-halts-← : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Halts t' → Halts t
—→-halts-← {t = t} x (halts nf y) = halts nf (t —→⟨ x ⟩ y)

-- The evaluation relation preserves halting (<-->)
—→-halts : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Halts t ↔ Halts t'
—→-halts x = record {to = —→-halts-→ x; from = —→-halts-← x}

{- Those proofs are needed for proving a lot of lemmas in which georgi
finally gets to normalize. I don't even know what is happening. The proofs
below are needed as well -}

-- The evaluation relation preserves saturation (-->)
—→-saturated-→ : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Saturated t → Saturated t'
—→-saturated-→ {ℕ´}      x (h /\ _)  = (—→-halts-→ x h) /\ tt
—→-saturated-→ {τ₁ ⇒ τ₂} x (h /\ s)  = (—→-halts-→ x h) /\ λ e → —→-saturated-→ (ξ-1 x) (s e)

-- The evaluation relation preserves saturation (<--)
—→-saturated-← : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Saturated t' → Saturated t
—→-saturated-← {ℕ´}      x (h /\ _)  = (—→-halts-← x h) /\ tt
—→-saturated-← {τ₁ ⇒ τ₂} x (h /\ s)  = (—→-halts-← x h) /\ λ e → —→-saturated-← (ξ-1 x) (s e)

-- The evaluation relation preserves saturation (<-->)
—→-saturated : ∀{τ}{t t' : ∅ ⊪ τ} → t —→ t' → Saturated t ↔ Saturated t'
—→-saturated x = record {to = —→-saturated-→ x; from = —→-saturated-← x}

-- The closure also preserves saturation. The proof for (<--) is not accepted
-- by Agda, but it is supposed to be the same. I don't know what is happening.
-- Georgi proves them by using function composition. I tried to copy the strategy.

-- —↠-saturated-→ : ∀{τ}{t t' : ∅ ⊪ τ} → t —↠ t' → Saturated t → Saturated t'
-- —↠-saturated-→ (_ ∎)          = id
-- —↠-saturated-→ (_ —→⟨ x ⟩ x₁) = —↠-saturated-→ x₁ ∘ —→-saturated-→ x
--
-- HERE IS WHERE THE ERROR COMES
-- —↠-saturated-← : ∀{τ}{t t' : ∅ ⊪ τ} → t —↠ t' → Saturated t' → Saturated t
-- —↠-saturated-← (_ ∎)          = id
-- —↠-saturated-← (z —→⟨ x ⟩ x₁) = —↠-saturated-← {! x₁  !} ∘ —→-saturated-← {! x  !}
--
-- —↠-saturated : ∀{τ}{t t' : ∅ ⊪ τ} → t —↠ t' → Saturated t ↔ Saturated t'
-- —↠-saturated x = record { to = —↠-saturated-→ x ; from = —↠-saturated-← x}
