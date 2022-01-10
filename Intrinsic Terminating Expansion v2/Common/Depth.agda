module Common.Depth where


{-
A Depth indicates if an expression has
let_in_ constructions. This is useful because
in this simply typed calculus, only such expressions
can have recursion. The Depth ⇑ indicates the presence
of a let_in_ in the expression. The Depth ⇓ indicates its
absence. Notice, however, that existing a let_in_ doesn't imply
it is recursive.
-}
data Depth : Set where
  ⇑ : Depth
  ⇓ : Depth
