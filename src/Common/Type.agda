module Common.Type where

data Type : Set where
  ℕ´  : Type
  _⇒_ : Type → Type → Type
