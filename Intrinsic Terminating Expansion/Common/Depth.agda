module Common.Depth where


{-
A Depth indicates if an expression has
let_in_ constructions. This is useful because
in this (recursive) simply typed calculus, only such expressions
can have recursion. The Depth ⇑ indicates the presence
of a let_in_ in the expression. The Depth ⇓ indicates its
absence.

In some moment Depth loses its role to help us
identify recursive terms, since the non-recursive calculus
has no recursion, as its name says. However, we'll keep let
as top-level only construction there too, to simplify things.
This makes Depth useful on the non-recursive calculus.
-}
data Depth : Set where
  ⇑ : Depth
  ⇓ : Depth
