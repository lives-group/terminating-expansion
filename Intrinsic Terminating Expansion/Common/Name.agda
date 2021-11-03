module Common.Name where

open import Data.String using (String; _==_)
open import Data.Bool using (Bool)

Name : Set
Name = String

_equals_ = _==_
