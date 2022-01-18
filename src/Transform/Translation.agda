module Transform.Translation where

open import Common.Depth using (Depth; ⇑; ⇓)
open import Common.Type using (Type; nat; _⇒_)
open import Common.Name using (Name)
open import Common.Context
open import R.Syntax
open import R.Syntax.Properties
open import R.Syntax.Unrolling
open import L.Syntax renaming (_⊢´_⊚_ to _⊩´_⊚_)
open import L.Syntax.Properties hiding (_⦂_called-in_)
  renaming (_⦂_not-called-in_ to _⦂_n-not-called-in_)
open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- call-elimination : ∀ {Γ v τ τ'}{t : Γ ⊢´ τ' ⊚ ⇓}
--   → v ⦂ τ called-in t
--   → ∃ ( λ (t' : Γ ⊩´ τ' ⊚ ⇓) → v ⦂ τ n-not-called-in t' )
-- call-elimination {t = zer} ()
-- call-elimination {t = suc t} (call-suc x)
--   = L.Syntax.suc (proj₁ (call-elimination x))
--     /\ no-call-suc (proj₂ (call-elimination x))
-- call-elimination {t = var v x} call-var
--   = err
--     /\ no-call-err
-- call-elimination {t = abs v t} (call-abs x)
--   = L.Syntax.abs v (proj₁ (call-elimination x))
--     /\ no-call-abs (proj₂ (call-elimination x))
-- call-elimination {t = app t t₁} (call-app1 x x₁)
--   = {!   !}
--     /\ {!   !}
-- call-elimination {t = app t t₁} (call-app2 x x₁)
--   = {!   !}
-- call-elimination {t = app t t₁} (call-app12 x x₁)
--   = {!   !}
-- call-elimination {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc1 x x₁ x₂)
--   = {!   !}
-- call-elimination {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc2 x x₁ x₂)
--   = {!   !}
-- call-elimination {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc3 x x₁ x₂)
--   = {!   !}
-- call-elimination {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc12 x x₁ x₂)
--   = {!   !}
-- call-elimination {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc13 x x₁ x₂)
--   = {!   !}
-- call-elimination {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc23 x x₁ x₂)
--   = {!   !}
-- call-elimination {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc123 x x₁ x₂)
--   = {!   !}

-- call-elimination : ∀ {Γ v τ τ'}{t : Γ ⊢´ τ' ⊚ ⇓}
--                    → v ⦂ τ called-in t
--                    → ∃ ( λ (Δ : Context)
--                      → ( ∃ ( λ (r : Δ ⊆ Γ)
--                        → ∃ ( λ (t' : Δ ⊩´ τ' ⊚ ⇓)
--                          → v ⦂ τ n-not-called-in t' ) ) ) )
-- call-elimination {Γ = Γ} {t = var _ _} call-var
--   = Γ /\ ⊆-refl /\ err /\ no-call-err
-- call-elimination {Γ = Γ} {t = suc t} (call-suc x)
--   = proj₁ (call-elimination x)
--     /\ proj₁ (proj₂ (call-elimination x))
--     /\ L.Syntax.suc (proj₁ (proj₂ (proj₂ (call-elimination x))))
--     /\ no-call-suc (proj₂ (proj₂ (proj₂ (call-elimination x))))
-- call-elimination {Γ = Γ} {t = abs v t} (call-abs x)
--   = drop-operation (proj₁ (call-elimination x))
--     /\ {! proj₁ (proj₂ (call-elimination x)) !}
--     /\ {!   !}
--     /\ {!   !}
-- call-elimination {Γ = Γ} {t = app t t₁} (call-app1 x x₁)
--   = {!   !}
-- call-elimination {Γ = Γ} {t = app t t₁} (call-app2 x x₁)
--   = {!   !}
-- call-elimination {Γ = Γ} {t = app t t₁} (call-app12 x x₁)
--   = {!   !}
-- call-elimination {Γ = Γ} {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc1 x x₁ x₂)
--   = {!   !}
-- call-elimination {Γ = Γ} {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc2 x x₁ x₂)
--   = {!   !}
-- call-elimination {Γ = Γ} {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc3 x x₁ x₂)
--   = {!   !}
-- call-elimination {Γ = Γ} {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc12 x x₁ x₂)
--   = {!   !}
-- call-elimination {Γ = Γ} {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc13 x x₁ x₂)
--   = {!   !}
-- call-elimination {Γ = Γ} {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc23 x x₁ x₂)
--   = {!   !}
-- call-elimination {Γ = Γ} {t = match t [z⇨ t₁ suc v ⇨ t₂ ]} (call-mtc123 x x₁ x₂)
--   = {!   !}

-- call-elimination : ∀ {Γ v τ τ'}{t : Γ ⊢´ τ' ⊚ ⇓}
--                   → v ⦂ τ called-in t
--                   → ∃ ( λ (t' : Γ ⊢´ τ' ⊚ ⇓) → v ⦂ τ not-called-in t')
-- call-elimination {t = var _ _} call-var
--   = {!   !}
-- call-elimination {t = suc t'}  (call-suc p)
--   = suc (proj₁ (call-elimination p)) /\ no-call-suc (proj₂ (call-elimination p))
-- call-elimination {t = abs v' t'} (call-abs p)
--   = abs v' (proj₁ (call-elimination p)) /\ no-call-abs (proj₂ (call-elimination p))
-- call-elimination {t = app _ t₂} (call-app1 p x)
--   = app (proj₁ (call-elimination p)) t₂ /\ no-call-app (proj₂ (call-elimination p)) x
-- call-elimination {t = app t₁ _} (call-app2 x p)
--   = app t₁ (proj₁ (call-elimination p)) /\ no-call-app x (proj₂ (call-elimination p))
-- call-elimination {t = app _ _} (call-app12 p p₁)
--   = app (proj₁ (call-elimination p)) (proj₁ (call-elimination p₁))
--     /\ no-call-app (proj₂ (call-elimination p)) (proj₂ (call-elimination p₁))
-- call-elimination {t = match _ [z⇨ t₂ suc v ⇨ t₃ ]} (call-mtc1 p x x₁)
--   = match proj₁ (call-elimination p) [z⇨ t₂ suc v ⇨ t₃ ]
--     /\ no-call-match (proj₂ (call-elimination p)) x x₁
-- call-elimination {t = match t₁ [z⇨ _ suc v ⇨ t₃ ]} (call-mtc2 x p x₁)
--   = match t₁ [z⇨ proj₁ (call-elimination p) suc v ⇨ t₃ ]
--     /\ no-call-match x (proj₂ (call-elimination p)) x₁
-- call-elimination {t = match t₁ [z⇨ t₂ suc v ⇨ _ ]} (call-mtc3 x x₁ p)
--   = match t₁ [z⇨ t₂ suc v ⇨ proj₁ (call-elimination p) ]
--     /\ no-call-match x x₁ (proj₂ (call-elimination p))
-- call-elimination {t = match _ [z⇨ _ suc v ⇨ t₃ ]} (call-mtc12 p p₁ x)
--   = match proj₁ (call-elimination p) [z⇨ proj₁ (call-elimination p₁) suc v ⇨ t₃ ]
--     /\ no-call-match (proj₂ (call-elimination p)) (proj₂ (call-elimination p₁) ) x
-- call-elimination {t = match _ [z⇨ t₂ suc v ⇨ _ ]} (call-mtc13 p x p₁)
--   = match proj₁ (call-elimination p) [z⇨ t₂ suc v ⇨ proj₁ (call-elimination p₁) ]
--     /\ no-call-match (proj₂ (call-elimination p)) x (proj₂ (call-elimination p₁) )
-- call-elimination {t = match t₁ [z⇨ _ suc v ⇨ _ ]} (call-mtc23 x p p₁)
--   = match t₁ [z⇨ proj₁ (call-elimination p) suc v ⇨ proj₁ (call-elimination p₁) ]
--     /\ no-call-match x (proj₂ (call-elimination p)) (proj₂ (call-elimination p₁) )
-- call-elimination {t = match _ [z⇨ _ suc v ⇨ _ ]} (call-mtc123 p p₁ p₂)
--   = match proj₁ (call-elimination p) [z⇨ proj₁ (call-elimination p₁) suc v ⇨ proj₁ (call-elimination p₂) ]
--     /\ no-call-match (proj₂ (call-elimination p)) (proj₂ (call-elimination p₁)) (proj₂ (call-elimination p₂))
--
-- recursion-elimination : ∀{Γ Δ τ ρ}{t : Γ ⊢´ τ ⊚ ρ} → t ▸rec Δ [ length Δ ]
--                         → ∃ ( λ (t' : Γ ⊢´ τ ⊚ ρ) → t' ▸rec ø [ 0 ] )
-- recursion-elimination {Γ} {ø} {τ} {⇓} {t} no-rec-⇓
--   = t /\ no-rec-⇓
-- recursion-elimination {Γ} {ø} {τ} {⇑} {let´ v ← t in´ t₁} (no-rec-⇑ r x₂)
--   = (let´ v ← t in´ t₁) /\ (no-rec-⇑ r x₂)
-- recursion-elimination {Γ} {Δ , x ⦂ x₁} {τ} {⇑} {let´ v ← t in´ t₁} (no-rec-⇑ r x₂)
--   = (let´ v ← t in´ proj₁ (recursion-elimination r)) /\ no-rec-⇑ (proj₂ (recursion-elimination r)) x₂
-- recursion-elimination {Γ} {Δ , x ⦂ x₁} {τ} {⇑} {let´ v ← t in´ t₁} (rec-⇑ r x₂)
--   = (let´ v ← proj₁ (call-elimination x₂) in´ proj₁ (recursion-elimination r))
--      /\ no-rec-⇑ (proj₂ (recursion-elimination r)) (proj₂ (call-elimination x₂))
--
-- transformation : ∀{Γ Δ τ ρ n}{t : Γ ⊢´ τ ⊚ ρ}
--                  → t ▸rec Δ [ n ]
--                  → VecFuel n
--                  → ∃ ( λ (t' : Γ ⊢´ τ ⊚ ρ) → t' ▸rec ø [ 0 ] )
-- transformation r fs with n-is-length r
-- transformation {t = t} no-rec-⇓ [] | refl
--   = t /\ no-rec-⇓
-- transformation {Δ = ø} {n = 0} {t = t} (no-rec-⇑ r x) [] | refl
--   = t /\ (no-rec-⇑ r x)
-- transformation {Δ = Δ , v ⦂ τ'} {n = suc n} {t = t} (no-rec-⇑ r x) (f ∷ fs) | refl
--   = proj₁ (recursion-elimination (proj₂ (unroll (no-rec-⇑ r x) (f ∷ fs))))
--     /\ proj₂ (recursion-elimination (proj₂ (unroll (no-rec-⇑ r x) (f ∷ fs))))
-- transformation {t = t} (rec-⇑ r p) (f ∷ fs) | refl
--   = (proj₁ (recursion-elimination (proj₂ (unroll (rec-⇑ r p) (f ∷ fs)))))
--      /\ proj₂ (recursion-elimination (proj₂ (unroll (rec-⇑ r p) (f ∷ fs))))
