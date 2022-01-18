{--
PCF’s Syntax following doi:10.1006/inco.2000.2917
We made some adaptations following PLFA by Kokke & Wadler
--}

module PCF.Syntax where

open import Common.Name using (Name)
open import Common.Type using (Type)

data Term' : Set where
    zer : Term'
    suc : Term' → Term'
    var : Name → Term'
    abs : Name → Term' → Term'
    app : Term' → Term' → Term'
    match_[z⇨_suc_⇨_] : Term' → Term' → Name → Term' → Term'

data Term : Set where
    trm : Term' → Term
    fix  : Name  → Term' → Term -- general recursion

data Value : Term → Set where
    vabs : ∀ {x : Name}{t : Term'} → Value (trm (abs x t))
    vzer : Value (trm zer)
    vsuc : ∀ {n : Term'} → Value (trm n) → Value (trm (suc n))
