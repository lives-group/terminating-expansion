{-- 
PCF’s Syntax following doi:10.1006/inco.2000.2917 
We made some adaptations following PLFA by Kokke & Wadler 
--}

module PCF.Syntax where

open import Common.Name using (Name)
open import Common.Type using (Type)

data Term : Set where
    ufn : Term -- undefined term
    zer : Term
    suc : Term → Term
    var : Name → Term
    abs : Name → Term → Term
    app : Term → Term → Term
    fix : Name → Term → Term -- general recursion
    match_[z⇨_suc_⇨_] : Term → Term → Name → Term → Term

data Value : Term → Set where
    vabs : ∀ {x : Name}{t : Term} → Value (abs x t)
    vzer : Value zer
    vsuc : ∀ {n : Term} → Value n → Value (suc n)