module PCF.Syntax.Unrolling where

open import Common.Type
open import Common.Context
open import Common.Name
open import Common.Depth using (Depth; ⇑; ⇓)
open import PCF.Syntax
open import PCF.Syntax.Properties
open import Relation.Nullary using (¬_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (∃) renaming (_,_ to _/\_)

inline : ∀{Γ Δ τ v τ'}{t₁ : Γ ⊢´ τ ⊚ ⇓}
         → v ⦂ τ' called-in t₁
         → Δ ⊢´ τ' ⊚ ⇓
         → Δ ⊆ Γ
         → Γ ⊢´ τ ⊚ ⇓
inline call-var      q r
  = context-substitution r q
inline (call-suc p)  q r
  = suc (inline p q r)
inline (call-abs  {v' = v'} p) q r
  = abs v' (inline p q (drop r))
inline (call-app1 {t' = t'} p _) q r
  = app (inline p q r) t'
inline (call-app2 {t = t}  _ p) q r
  = app t (inline p q r)
inline (call-app12 p₁ p₂) q r
  = app (inline p₁ q r) (inline p₂ q r)
inline (call-mtc1 {v' = v'} {t₁ = t₁} {t₂ = t₂} p _ _) q r
  = match inline p q r [z⇨ t₁ suc v' ⇨ t₂ ]
inline (call-mtc2 {v' = v'} {t = t} {t₂ = t₂} _ p _) q r
  = match t [z⇨ inline p q r suc v' ⇨ t₂ ]
inline (call-mtc3 {v' = v'} {t = t} {t₁ = t₁} _ _ p) q r
  = match t [z⇨ t₁ suc v' ⇨ inline p q (drop r) ]
inline (call-mtc12 {v' = v'} {t₂ = t₃} p₁ p₂ _) q r
  = match inline p₁ q r [z⇨ inline p₂ q r suc v' ⇨ t₃ ]
inline (call-mtc13 {v' = v'} {t₁ = t₂} p₁ _ p₃) q r
  = match inline p₁ q r [z⇨ t₂ suc v' ⇨ inline p₃ q (drop r) ]
inline (call-mtc23 {v' = v'} {t = t₁} _ p₂ p₃) q r
  = match t₁ [z⇨ inline p₂ q r suc v' ⇨ inline p₃ q (drop r) ]
inline (call-mtc123 {v' = v'} p₁ p₂ p₃) q r
  = match inline p₁ q r [z⇨ inline p₂ q r suc v' ⇨ inline p₃ q (drop r) ]

{- Inline preserves variable calls -}
vcp-inline : ∀{Γ Δ τ v τ'}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Δ ⊢´ τ' ⊚ ⇓}
             (p : v ⦂ τ' called-in t₁)
             (r : Δ ⊆ Γ)
             → v ⦂ τ' called-in t₂
             → v ⦂ τ' called-in (inline p t₂ r)
vcp-inline call-var              r q = call-preserving r q
vcp-inline (call-suc p)          r q = call-suc (vcp-inline p r q)
vcp-inline (call-abs p)          r q = call-abs (vcp-inline p (drop r) q)
vcp-inline (call-app1 p x)       r q = call-app1 (vcp-inline p r q) x
vcp-inline (call-app2 x p)       r q = call-app2 x (vcp-inline p r q)
vcp-inline (call-app12 p p₁)     r q = call-app12 (vcp-inline p r q) (vcp-inline p₁ r q)
vcp-inline (call-mtc1 p x x₁)    r q = call-mtc1 (vcp-inline p r q) x x₁
vcp-inline (call-mtc2 x p x₁)    r q = call-mtc2 x (vcp-inline p r q) x₁
vcp-inline (call-mtc3 x x₁ p)    r q = call-mtc3 x x₁ (vcp-inline p (drop r) q)
vcp-inline (call-mtc12 p p₁ x)   r q = call-mtc12 (vcp-inline p r q) (vcp-inline p₁ r q) x
vcp-inline (call-mtc13 p x p₁)   r q = call-mtc13 (vcp-inline p r q) x (vcp-inline p₁ (drop r) q)
vcp-inline (call-mtc23 x p p₁)   r q = call-mtc23 x (vcp-inline p r q) (vcp-inline p₁ (drop r) q)
vcp-inline (call-mtc123 p p₁ p₂) r q = call-mtc123
                                          (vcp-inline p r q)
                                          (vcp-inline p₁ r q)
                                          (vcp-inline p₂ (drop r) q)

{-
Inlining a term into itself preserves
variable calls
-}
expand-once : ∀{Γ τ v}{t : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}
              (p : v ⦂ τ called-in t)
              → v ⦂ τ called-in (inline p t ⊆-refl)
expand-once p = vcp-inline p ⊆-refl p

inductively-expand : ∀{Γ τ v}{t : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}
                     {p  : v ⦂ τ called-in t}
                     (ps : v ⦂ τ called-in (inline p t ⊆-refl))
                     → v ⦂ τ called-in (inline ps t ⊆-refl)
inductively-expand {p = p} ps = vcp-inline ps ⊆-refl p

data Fuel : ℕ → Set where
  gas : ∀ n → Fuel n

data _expands-to_in´_steps : ∀{Γ v τ}{t t' : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}
                             (p : v ⦂ τ called-in t)(p' : v ⦂ τ called-in t')
                             → ℕ → Set where
  none   : ∀{Γ τ v}{t : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}{p : v ⦂ τ called-in t}
           → p expands-to p in´ 0 steps
  simple : ∀{Γ τ v}{t t' : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}{p : v ⦂ τ called-in t}{p' : v ⦂ τ called-in t'}
           → p expands-to (vcp-inline p ⊆-refl p') in´ 1 steps
  trans  : ∀{Γ τ v n₁ n₂}{t₁ t₂ t₃ : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}
           {p₁ : v ⦂ τ called-in t₁} {p₂ : v ⦂ τ called-in t₂} {p₃ : v ⦂ τ called-in t₃}
           → p₁ expands-to p₂ in´ n₁ steps → p₂ expands-to p₃ in´ n₂ steps
           → p₁ expands-to p₃ in´ (n₂ + n₁) steps

expand : ∀{Γ v τ n}{t : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}(p₁ : v ⦂ τ called-in t) → Fuel n
         → ∃ (λ (t' : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓) → ∃ (λ (p₂ : v ⦂ τ called-in t') → p₁ expands-to p₂ in´ n steps))
expand {t = t} p (gas 0)    = t /\ p /\ none
expand {t = t} p (gas 1)    = inline p t ⊆-refl /\ (expand-once p) /\ simple
expand {t = t} p (gas (suc f)) with expand p (gas f)
... | t₁ /\ p₁ /\ p▸p₁ = (inline p₁ t ⊆-refl) /\ (vcp-inline p₁ ⊆-refl p /\ trans p▸p₁ simple)

extract : ∀{Γ τ v}{t : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓} → v ⦂ τ called-in t → Γ , v ⦂ τ ⊢´ τ ⊚ ⇓
extract {_} {_} {_} {t} _ = t

extractExpansion : ∀{Γ τ v n}{t : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}{p₁ : v ⦂ τ called-in t}
                   → ∃ (λ (t' : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓) → ∃ (λ (p₂ : v ⦂ τ called-in t') → p₁ expands-to p₂ in´ n steps))
                   → Γ , v ⦂ τ ⊢´ τ ⊚ ⇓
extractExpansion (t' /\ _) = t'

data VecFuel : ℕ → Set where
  []  : VecFuel 0
  _∷_ : ∀{n n₁} → Fuel n₁ → VecFuel n → VecFuel (suc n)

unroll : ∀{Γ Δ v ρ τ τ' n}{t : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}{t' : Γ , v ⦂ τ ⊢´ τ' ⊚ ρ}
         → (let´ v ← t in´ t') ▸rec Δ [ suc n ] → VecFuel (suc n) → Γ ⊢´ τ' ⊚ ⇑
unroll {Γ} {Δ} {v} {⇑} {τ} {τ'} {n} {t} {let´ v₁ ← t' in´ t''} (no-rec-⇑ r x) fs
  = let´ v ← t in´ unroll r fs
unroll {Γ} {Δ} {v} {ρ} {τ} {τ'} {zero} {t} {t'} (rec-⇑ r x) (f ∷ [])
  = let´ v ← extractExpansion (expand x f) in´ t'
unroll {Γ} {Δ} {v} {⇑} {τ} {τ'} {suc n} {t} {let´ v₁ ← t' in´ t''} (rec-⇑ r x) (f ∷ fs)
  = let´ v ← extractExpansion (expand x f) in´ unroll r fs
