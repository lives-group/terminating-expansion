module Examples.R where

open import Common.Depth using (Depth; ⇓; ⇑)
open import Common.Type using (Type; ℕ´; _⇒_)
import Common.Context as C
open C using (Context; _,_; _∈_; _⊆_; ∈-subs; keep; drop; ⊆-refl; ø; here; there)
open import R.Syntax
open import R.Syntax.Properties

open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{- Function that sums naturals -}
sum : ø ⊢ ℕ´ ⇒ ℕ´ ⇒ ℕ´ ⊚ ⇑
sum = rec {- sum -}
      (abs {- x -}
        (abs {- y -}
          (match (var {- x -} (there here))
{- zero -}  (var {- y -} here)
{- suc w -}   (app
                (app (var {- sum -} (there (there (there here)))) (var {- w -} here)
                )
              (suc´ (var (there here)))
              )
           )
         )
      )
