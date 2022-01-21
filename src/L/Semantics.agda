{-# OPTIONS --safe #-}
module L.Semantics where

open import Common.Type using (Type; ℕ´; _⇒_)
open import Common.Context using (Context; _,_; _∈_; here; there)
open import L.Syntax
open import L.Syntax.Properties
