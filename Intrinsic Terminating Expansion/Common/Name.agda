module Common.Name where

open import Data.String using (String; _≈_)
-- open import Data.String.Properties using (_≟_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Name : Set
Name = String

_equals_ = _≡_

-- dec-equals = _≟_
