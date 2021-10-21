module PCF.Unrolling where

-- Agda Stdlib 1.7 
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Name
open import PCF.Syntax
open import PCF.Examples

{-- 
Change calls from one name to other name 
It has the same effect of renaming a variable
No capture-avoiding caution is taken here
--}
renameVar : Term → Name → Name → Term
renameVar ufn v₁ v₂ = ufn
renameVar zer v₁ v₂ = zer
renameVar (suc t) v₁ v₂ = suc (renameVar t v₁ v₂)
renameVar (var x) v₁ v₂ with v₁ equals x
...                    | true  = var v₂
...                    | false = var x
renameVar (abs x t) v₁ v₂ = abs x (renameVar t v₁ v₂)
renameVar (app t t₁) v₁ v₂ = app (renameVar t v₁ v₂) (renameVar t₁ v₁ v₂)
renameVar (fix x t) v₁ v₂ = fix x (renameVar t v₁ v₂)
renameVar match t [z⇨ t₁ suc x ⇨ t₂ ] v₁ v₂ = match (renameVar t v₁ v₂) 
                                               [z⇨ (renameVar t₁ v₁ v₂) 
                                                suc x ⇨ (renameVar t₂ v₁ v₂) ] 

{-- 
Inlines a function into another
It has the same effect of variable
substituion. No capture-avoiding caution 
is taken here
--}
inline : Term → Name → Term → Term
inline ufn v₂ t₂ = ufn
inline zer v₂ t₂ = zer
inline (suc t₁) v₂ t₂ = suc (inline t₁ v₂ t₂)
inline (var x) v₂ t₂ with v₂ equals x
...                  | true  = t₂
...                  | false = var x
inline (abs x t₁) v₂ t₂ = abs x (inline t₁ v₂ t₂)
inline (app t₁ t₃) v₂ t₂ = app (inline t₁ v₂ t₂) (inline t₃ v₂ t₂)
inline (fix x t₁) v₂ t₂ = fix x (inline t₁ v₂ t₂)
inline match t₁ [z⇨ t₃ suc x ⇨ t₄ ] v₂ t₂ = match inline t₁ v₂ t₂
                                             [z⇨ inline t₃ v₂ t₂
                                              suc x ⇨ inline t₄ v₂ t₂ ]

{--
Changes the name of a named fix function
without changing the recursive calls
Leaves it unchanged if not a named function
--}
changeFixName : Term → Name → Term
changeFixName (fix x t) v = fix v t
changeFixName t v = t

{-- 
expand a recursion of a fix function
does nothing if not fix
--}
expand : ℕ → Term → Term
expand 0       t         = t
expand 1       (fix v t) = inline (fix v (renameVar t v v₁)) v₁ t
    where
        v₁ = newName v
expand (suc n) (fix v t) = inline (fix v (renameVar t v v₁)) v₁ (expand n (fix v t))
    where 
        v₁ = newName v
expand _       t         = t

data NamedFun : Term → Set where
    funName : ∀{t : Term}(v : Name) → NamedFun (fix v t)

{-- Theorem : changeFixName only changes name --}
changeFixNameSoudness : ∀{t : Term}{v v' : Name} 
                     → NamedFun (fix v t) 
                     → NamedFun (changeFixName (fix v t) v') ≡ NamedFun (fix v' t)
changeFixNameSoudness n = refl 