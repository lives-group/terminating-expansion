module Common.Name where

-- Agda Stdlib 1.7
open import Data.String using (String; _==_) renaming (_++_ to concat)
open import Data.Bool using (Bool)

Name : Set
Name = String

infixl 4 _equals_

_equals_ : Name → Name → Bool
_equals_ = _==_

_++_ : Name → Name → Name
_++_ = concat
