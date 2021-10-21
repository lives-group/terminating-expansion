{--
Fuel is a part of Petrol Semantics, a way
to embed an additional parameter to a function
that behaves just like a decreasing natural
to ensure termination.
--}

module Expansion.Fuel where

open import Data.Nat using (ℕ; zero; suc)

Fuel : Set
Fuel = ℕ

noGas : Fuel
noGas = zero

fuel : Fuel → Fuel
fuel = suc