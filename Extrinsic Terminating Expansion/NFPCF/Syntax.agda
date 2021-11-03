{--
Our Proposed No-Fix PCF.
It is just the PCF without fix and with
an additional constructor to represent
the “out of fuel” error.
--}

module NFPCF.Syntax where

open import Common.Name using (Name)
open import Common.Type using (Type)

data Term : Set where
    zer : Term
    suc : Term → Term
    var : Name → Term
    abs : Name → Term → Term
    app : Term → Term → Term
    out : Term -- out of fuel error
    match_[z⇨_suc_⇨_] : Term → Term → Name → Term → Term

data Value : Term → Set where
    vabs : ∀ {x : Name}{t : Term} → Value (abs x t)
    vzer : Value zer
    vsuc : ∀ {n : Term} → Value n → Value (suc n)
    vout : Value out
