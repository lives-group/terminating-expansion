module Common.Type where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)

infixr 16 _⇒_

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

dec-equals : ∀(τ₁ τ₂ : Type) → Dec (τ₁ ≡ τ₂)
dec-equals nat       nat       = yes refl
dec-equals nat       (τ' ⇒ _)  = no (λ ())
dec-equals (τ' ⇒ _)  nat       = no (λ ())
dec-equals (τ₁ ⇒ τ₂) (τ₃ ⇒ τ₄) with dec-equals τ₁ τ₃ | dec-equals τ₂ τ₄
dec-equals (τ₁ ⇒ τ₂) (τ₃ ⇒ τ₄) | yes refl | yes refl = yes refl
dec-equals (τ₁ ⇒ τ₂) (τ₃ ⇒ τ₄) | yes x    | no y     = no λ {refl → y refl}
dec-equals (τ₁ ⇒ τ₂) (τ₃ ⇒ τ₄) | no  x    | yes refl = no λ {refl → x refl}
dec-equals (τ₁ ⇒ τ₂) (τ₃ ⇒ τ₄) | no  x    | no y     = no λ {refl → x refl}
