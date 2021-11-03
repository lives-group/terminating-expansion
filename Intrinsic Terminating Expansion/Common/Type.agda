module Common.Type where

infixr 16 _⇒_

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type
