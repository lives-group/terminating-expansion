module PCF.Syntax.Unrolling where

open import Common.Type
open import Common.Context
open import Common.Name
open import PCF.Syntax
open import PCF.Syntax.Properties
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc)

-- inline : ∀{Γ Δ τ v τ'}{t : Γ ⊢´ τ ⊚ ⇓}
--          → v ⦂ τ' called-in t
--          → Δ ⊢´ τ' ⊚ ⇓ → Δ ⊆ Γ
--          → Γ ⊢´ τ ⊚ ⇓
-- inline call-var      q r
--   = context-substitution r q
-- inline (call-suc p)  q r
--   = suc (inline p q r)
-- inline (call-abs  {v' = v'} p) q r
--   = abs v' (inline p q (drop r))
-- inline (call-app1 {t' = t'} p) q r
--   = app (inline p q r) t'
-- inline (call-app2 {t = t}   p) q r
--   = app t (inline p q r)
-- inline (call-app12 p₁ p₂) q r
--   = app (inline p₁ q r) (inline p₂ q r)
-- inline (call-mtc1 {v' = v'} {t₁ = t₁} {t₂ = t₂} p) q r
--   = match inline p q r [z⇨ t₁ suc v' ⇨ t₂ ]
-- inline (call-mtc2 {v' = v'} {t = t} {t₂ = t₂} p) q r
--   = match t [z⇨ inline p q r suc v' ⇨ t₂ ]
-- inline (call-mtc3 {v' = v'} {t = t} {t₁ = t₁} p) q r
--   = match t [z⇨ t₁ suc v' ⇨ inline p q (drop r) ]
-- inline (call-mtc12 {v' = v'} {t₂ = t₃} p₁ p₂) q r
--   = match inline p₁ q r [z⇨ inline p₂ q r suc v' ⇨ t₃ ]
-- inline (call-mtc13 {v' = v'} {t₁ = t₂} p₁ p₃) q r
--   = match inline p₁ q r [z⇨ t₂ suc v' ⇨ inline p₃ q (drop r) ]
-- inline (call-mtc23 {v' = v'} {t = t₁} p₂ p₃) q r
--   = match t₁ [z⇨ inline p₂ q r suc v' ⇨ inline p₃ q (drop r) ]
-- inline (call-mtc123 {v' = v'} p₁ p₂ p₃) q r
--   = match inline p₁ q r [z⇨ inline p₂ q r suc v' ⇨ inline p₃ q (drop r) ]


-- data Fuel : ℕ → Set where
--   last : Fuel 1
--   gas  : ∀{n} → Fuel n → Fuel (suc n)
--
-- expand : ∀{Γ τ v n}{t : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}
--          (p : v ⦂ τ called-in t) → inline p t ⊆-refl
--          → Fuel n
--          → v ⦂ τ called-in i
-- expand p f = ?

-- data VecFuel : ℕ → Set where
--   []  : VecFuel 0
--   _∷_ : ∀{n} → ℕ → VecFuel n → VecFuel (suc n)
--
-- unroll : ∀{Γ Δ v ρ τ τ' n}{t : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}{t' : Γ , v ⦂ τ ⊢´ τ' ⊚ ρ}
--          → (let´ v ← t in´ t') ▸rec Δ [ suc n ] → VecFuel (suc n) → Γ ⊢´ τ' ⊚ ⇑
-- unroll {Γ} {Δ} {v} {⇑} {τ} {τ'} {n} {t} {let´ v₁ ← t' in´ t''} (no-rec-⇑ r x) fs
--   = let´ v ← t in´ unroll r fs
-- unroll {Γ} {Δ} {v} {ρ} {τ} {τ'} {zero} {t} {t'} (rec-⇑ r x) (f ∷ [])
--   = let´ v ← expand x f in´ t'
-- unroll {Γ} {Δ} {v} {⇑} {τ} {τ'} {suc n} {t} {let´ v₁ ← t' in´ t''} (rec-⇑ r x) (f ∷ fs)
--   = let´ v ← expand x f in´ unroll r fs
