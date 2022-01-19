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

infixl 20 _∙_
_∙_ : ∀{Γ τ₁ τ₂ ρ} → Γ ⊢ τ₁ ⇒ τ₂ ⊚ ρ → Γ ⊢ τ₁ ⊚ ⇓ → Γ ⊢ τ₂ ⊚ ρ
_∙_ = app

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

1+2 : ø ⊢ ℕ´ ⊚ ⇑
1+2 = sum ∙ suc´ zero´ ∙ suc´ (suc´ zero´)

id : ∀{τ} → ø , τ ⊢ τ ⊚ ⇑
id = rec (var (there here))
