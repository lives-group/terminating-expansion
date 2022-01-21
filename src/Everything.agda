{-
Maycon Amaro, 2021. Federal University of Ouro Preto.

Some notes:
  ∙ Typecheck this file to typecheck everything
  ∙ You can run a grep or similiar  in the project
    to confirm no TERMINATING pragma or postulates
    are used on any file.
  ∙ This was typechecked with
    - Agda 2.6.2.1
    - Standard Library 1.7.1
    - Kubuntu 21.10 (impish)
-}

open import Common.Depth
open import Common.Type
open import Common.Context

open import R.Syntax
open import R.Syntax.Properties
open import R.Syntax.Unrolling
open import R.Semantics

open import Examples.Context
open import Examples.R
