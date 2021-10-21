module Common.Name where

-- Agda Stdlib 1.7
open import Data.String using (String; _==_; _++_)
open import Data.Bool using (Bool)

Name : Set
Name = String

infixl 4 _equals_

_equals_ : Name → Name → Bool 
_equals_ = _==_

newName : Name → Name
newName n = n ++ "'"