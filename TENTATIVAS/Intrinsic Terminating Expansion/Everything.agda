{-
Maycon Amaro, 2021. Federal University of Ouro Preto.

Some notes:
  ∙ Typecheck this file to typecheck everything
  ∙ You can run a grep in the project to confirm
    no TERMINATING pragma or postulates are
    used on any file.
  ∙ This was typechecked with Agda 2.6.2
    using Standard Library 1.7
    and Ubuntu 21.04 (hirsute hippo)
-}

open import Common.Depth
open import Common.Type
open import Common.Name
open import Common.Context

open import PCF.Syntax
open import PCF.Syntax.Properties
open import PCF.Syntax.Unrolling
open import PCF.Examples

-- open import NPCF.Syntax

open import Transformation
