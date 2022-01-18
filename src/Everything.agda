{-
Maycon Amaro, 2021. Federal University of Ouro Preto.

Some notes:
  ∙ Typecheck this file to typecheck everything
  ∙ You can run a grep in the project to confirm
    no TERMINATING pragma or postulates are
    used on any file.
  ∙ This was typechecked with Agda 2.6.2.1
    using Standard Library 1.7.1
    and Ubuntu 21.10 (impish)
-}

open import Common.Depth
open import Common.Type
open import Common.Name
open import Common.Context

open import PCF.Syntax
open import PCF.Syntax.Properties
open import PCF.Syntax.Unrolling
open import PCF.Semantics

open import Transformation

open import PCF.Examples
