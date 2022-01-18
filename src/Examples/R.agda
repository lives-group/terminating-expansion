module Examples.R where

open import Common.Type
open import Common.Context
open import Common.Name
open import Common.Depth using (Depth; ⇑; ⇓)
open import R.Syntax
open import R.Syntax.Properties
open import R.Syntax.Unrolling

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; proj₁; proj₂)

-- Syntatic Sugar for function application
infixl 20 _∙_

_∙_ : ∀{Γ τ τ'} → Γ ⊢´ τ ⇒ τ' ⊚ ⇓ → Γ ⊢´ τ ⊚ ⇓ → Γ ⊢´ τ' ⊚ ⇓
_∙_ = app
