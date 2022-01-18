module Common.Type where

infixr 15 _⇒_

data Type : Set where
    nat  : Type
    _⇒_  : Type → Type → Type