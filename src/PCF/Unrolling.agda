module PCF.Unrolling where

-- Agda Stdlib 1.7
open import Data.Bool using (Bool; true; false) renaming (_∨_ to _or_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using (show)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Name
open import PCF.Syntax
open import PCF.Examples

{--
Creates a name that is not
used by the term yet
--}
name-is-used' : Term' → Name → Bool
name-is-used' (var x) v = x equals v
name-is-used' (abs x t) v = (x equals v) or (name-is-used' t v)
name-is-used' (app t t₁) v = name-is-used' t v or name-is-used' t₁ v
name-is-used' match t [z⇨ t₁ suc x ⇨ t₂ ] v = name-is-used' t v or name-is-used' t₁ v or name-is-used' t₂ v
name-is-used' (suc t) v = name-is-used' t v
name-is-used' zer v = false

name-is-used : Term → Name → Bool
name-is-used (trm t) v    = name-is-used' t v
name-is-used (fix v' t) v = (v' equals v) or (name-is-used' t v)

countNames' : Term' → ℕ
countNames' zer = 0
countNames' (suc t) = countNames' t
countNames' (var x) = 1
countNames' (abs x t) = 1 + countNames' t
countNames' (app t t₁) = countNames' t + countNames' t₁
countNames' match t [z⇨ t₁ suc x ⇨ t₂ ] = 1 + countNames' t + countNames' t₁ + countNames' t₂

countNames : Term → ℕ
countNames (trm t)   = countNames' t
countNames (fix v t) = 1 + countNames' t

newName' : Term → ℕ → Name
newName' t 0 = "x0"
newName' t (suc n) with name-is-used t ("x" ++ show (suc n))
...                | true = newName' t n
...                | false = "x" ++ show (suc n)

newName : Term → Name
newName t = newName' t (countNames t)

{--
Change calls from one name to other name
It has the same effect of renaming a variable
No capture-avoiding caution is taken here
because I always generate a real new name
--}
renameVar' : Term' → Name → Name → Term'
renameVar' zer v₁ v₂ = zer
renameVar' (suc t) v₁ v₂ = suc (renameVar' t v₁ v₂)
renameVar' (var x) v₁ v₂ with v₁ equals x
...                    | true  = var v₂
...                    | false = var x
renameVar' (abs x t) v₁ v₂ = abs x (renameVar' t v₁ v₂)
renameVar' (app t t₁) v₁ v₂ = app (renameVar' t v₁ v₂) (renameVar' t₁ v₁ v₂)
renameVar' match t [z⇨ t₁ suc x ⇨ t₂ ] v₁ v₂ = match (renameVar' t v₁ v₂)
                                               [z⇨ (renameVar' t₁ v₁ v₂)
                                                suc x ⇨ (renameVar' t₂ v₁ v₂) ]

renameVar : Term → Name → Name → Term
renameVar (trm t)   v₁ v₂ = trm (renameVar' t v₁ v₂)
renameVar (fix v t) v₁ v₂ = fix v (renameVar' t v₁ v₂)

{--
Inlines a function into another
It has the same effect of variable
substituion. No capture-avoiding caution
is taken here, because I always generate
a real new name
--}
inline' : Term' → Name → Term' → Term'
inline' zer v₂ t₂ = zer
inline' (suc t₁) v₂ t₂ = suc (inline' t₁ v₂ t₂)
inline' (var x) v₂ t₂ with v₂ equals x
...                  | true  = t₂
...                  | false = var x
inline' (abs x t₁) v₂ t₂ = abs x (inline' t₁ v₂ t₂)
inline' (app t₁ t₃) v₂ t₂ = app (inline' t₁ v₂ t₂) (inline' t₃ v₂ t₂)
inline' match t₁ [z⇨ t₃ suc x ⇨ t₄ ] v₂ t₂ = match inline' t₁ v₂ t₂
                                             [z⇨ inline' t₃ v₂ t₂
                                              suc x ⇨ inline' t₄ v₂ t₂ ]

inline : Term → Name → Term' → Term
inline (trm t) v₂ t₂    = trm (inline' t v₂ t₂)
inline (fix v₁ t) v₂ t₂ = fix v₁ (inline' t v₂ t₂)

{--
Changes the name of a named fix function
without changing the recursive calls
Leaves it unchanged if not a named function
--}
changeFixName : Term → Name → Term
changeFixName (fix _ t) v = fix v t
changeFixName t _ = t

{--
expand a recursion of a fix function
does nothing if not fix
--}
extract : Term → Term'
extract (trm t)   = t
extract (fix v t) = t

expand : ℕ → Term → Term
expand 0       t         = t
expand 1       (fix v t) = inline (fix v (renameVar' t v v₁)) v₁ t
    where
        v₁ = newName (fix v t)
expand (suc n) (fix v t) = inline (fix v (renameVar' t v v₁)) v₁ (extract (expand n (fix v t)))
    where
        v₁ = newName (fix v t)
expand _       t         = t

data NamedFun : Term → Set where
    funName : ∀{t : Term'}(v : Name) → NamedFun (fix v t)

{-- Theorem : changeFixName only changes name --}
changeFixNameSoudness : ∀{t : Term'}{v v' : Name}
                     → NamedFun (fix v t)
                     → NamedFun (changeFixName (fix v t) v') ≡ NamedFun (fix v' t)
changeFixNameSoudness n = refl
