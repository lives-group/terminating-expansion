module PCF.Syntax.Properties where

open import Common.Type
open import Common.Context
open import Common.Name
open import Common.Depth using (Depth; ⇑; ⇓)
open import PCF.Syntax
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Nullary using (¬_; yes; no)
open import Data.String using (_≟_)
open import Data.Product using (∃; proj₁; proj₂) renaming (_,_ to _/\_)
open import Data.Empty using (⊥-elim)

{-
Evidence for variable calls
-}

data _⦂_not-called-in_ : ∀{Γ τ} → Name → Type → Γ ⊢´ τ ⊚ ⇓ → Set where
  no-call-zer   : ∀{Γ v τ} → v ⦂ τ not-called-in (zer {Γ})
  no-call-varn  : ∀{Γ v₁ v₂ τ τ'}{t : v₂ ⦂ τ ∈ Γ} → ¬(v₁ ≡ v₂)
                → v₁ ⦂ τ' not-called-in (var v₂ t)
  no-call-vart  : ∀{Γ v τ τ'}{t : v ⦂ τ ∈ Γ} → ¬(τ' ≡ τ)
                → v ⦂ τ' not-called-in (var v t)
  no-call-suc   : ∀{Γ v τ'}{t : Γ ⊢´ nat ⊚ ⇓}
                → v ⦂ τ' not-called-in t → v ⦂ τ' not-called-in (suc t)
  no-call-abs   : ∀{Γ v v' τ τ' τ₁}{t : Γ , v' ⦂ τ ⊢´ τ' ⊚ ⇓}
                → v ⦂ τ₁ not-called-in t → v ⦂ τ₁ not-called-in (abs v' t)
  no-call-app   : ∀{Γ v τ τ' τ₁}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓}
                → v ⦂ τ₁ not-called-in t → v ⦂ τ₁ not-called-in t'
                → v ⦂ τ₁ not-called-in (app t t')
  no-call-match : ∀{Γ v v' τ τ₁}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
                → v ⦂ τ₁ not-called-in t → v ⦂ τ₁ not-called-in t₁ → v ⦂ τ₁ not-called-in t₂
                → v ⦂ τ₁ not-called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])

data _⦂_called-in_ : ∀{Γ τ} → Name → Type → Γ ⊢´ τ ⊚ ⇓ → Set where
  call-var : ∀{Γ τ v}{t : v ⦂ τ ∈ Γ} → v ⦂ τ called-in (var v t)
  call-suc : ∀{Γ v τ}{t : Γ ⊢´ nat ⊚ ⇓}
              → v ⦂ τ called-in t → v ⦂ τ called-in (suc t)
  call-abs : ∀{Γ v v' τ τ' τ₁}{t : Γ , v' ⦂ τ ⊢´ τ' ⊚ ⇓}
              → v ⦂ τ₁ called-in t → v ⦂ τ₁ called-in (abs v' t)
  call-app1 : ∀{Γ v τ τ' τ₁}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓}
              → v ⦂ τ₁ called-in t → v ⦂ τ₁ not-called-in t' → v ⦂ τ₁ called-in (app t t')
  call-app2 : ∀{Γ v τ τ' τ₁}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓}
              → v ⦂ τ₁ not-called-in t → v ⦂ τ₁ called-in t' → v ⦂ τ₁ called-in (app t t')
  call-app12 : ∀{Γ v τ τ' τ₁}{t : Γ ⊢´ τ ⇒ τ' ⊚ ⇓}{t' : Γ ⊢´ τ ⊚ ⇓}
               → v ⦂ τ₁ called-in t → v ⦂ τ₁ called-in t' → v ⦂ τ₁ called-in (app t t')
  call-mtc1 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' called-in t → v ⦂ τ' not-called-in t₁ → v ⦂ τ' not-called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc2 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' not-called-in t → v ⦂ τ' called-in t₁ → v ⦂ τ' not-called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc3 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' not-called-in t → v ⦂ τ' not-called-in t₁ → v ⦂ τ' called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc12 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' called-in t → v ⦂ τ' called-in t₁ → v ⦂ τ' not-called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc13 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' called-in t → v ⦂ τ' not-called-in t₁ → v ⦂ τ' called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc23 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
              → v ⦂ τ' not-called-in t → v ⦂ τ' called-in t₁ → v ⦂ τ' called-in t₂
              → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])
  call-mtc123 : ∀{Γ v v' τ τ'}{t : Γ ⊢´ nat ⊚ ⇓}{t₁ : Γ ⊢´ τ ⊚ ⇓}{t₂ : Γ , v' ⦂ nat ⊢´ τ ⊚ ⇓}
                → v ⦂ τ' called-in t → v ⦂ τ' called-in t₁ → v ⦂ τ' called-in t₂
                → v ⦂ τ' called-in (match t [z⇨ t₁ suc v' ⇨ t₂ ])

{-
It is decidable to check a var calling in a term
-}
data CallTotal : ∀{Γ τ} → Name → Type → Γ ⊢´ τ ⊚ ⇓ → Set where
  is-called  : ∀{Γ v τ τ'}{t : Γ ⊢´ τ' ⊚ ⇓}
               → v ⦂ τ called-in t → CallTotal v τ t
  not-called : ∀{Γ v τ τ'}{t : Γ ⊢´ τ' ⊚ ⇓}
               → v ⦂ τ not-called-in t → CallTotal v τ t

dec-called : ∀{Γ τ'}(v : Name)(τ : Type)(t : Γ ⊢´ τ' ⊚ ⇓) → CallTotal v τ t
dec-called v τ zer = not-called no-call-zer
dec-called {τ' = τ'} v τ (var v₁ x) with v ≟ v₁ | dec-equals τ τ'
dec-called {τ' = τ'} v τ (var v₁ x) | yes refl | yes refl = is-called call-var
dec-called {τ' = τ'} v τ (var v₁ x) | yes refl | no τ≢τ₁  = not-called (no-call-vart τ≢τ₁)
dec-called {τ' = τ'} v τ (var v₁ x) | no v≢v₁  | _        = not-called (no-call-varn v≢v₁)
dec-called v τ (suc t) with dec-called v τ t
... | is-called x  = is-called (call-suc x)
... | not-called x = not-called (no-call-suc x)
dec-called v τ (abs v₁ t) with dec-called v τ t
... | is-called  x = is-called (call-abs x)
... | not-called x = not-called (no-call-abs x)
dec-called v τ (app t t₁) with dec-called v τ t | dec-called v τ t₁
dec-called v τ (app t t₁) | is-called x  | is-called x₁  = is-called (call-app12 x x₁)
dec-called v τ (app t t₁) | is-called x  | not-called x₁ = is-called (call-app1 x x₁)
dec-called v τ (app t t₁) | not-called x | is-called x₁  = is-called (call-app2 x x₁)
dec-called v τ (app t t₁) | not-called x | not-called x₁ = not-called (no-call-app x x₁)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] with dec-called v τ t | dec-called v τ t₁ | dec-called v τ t₂
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | is-called x  | is-called x₁  | is-called x₂  = is-called (call-mtc123 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | is-called x  | is-called x₁  | not-called x₂ = is-called (call-mtc12 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | is-called x  | not-called x₁ | is-called x₂  = is-called (call-mtc13 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | is-called x  | not-called x₁ | not-called x₂ = is-called (call-mtc1 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | not-called x | is-called x₁  | is-called x₂  = is-called (call-mtc23 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | not-called x | is-called x₁  | not-called x₂ = is-called (call-mtc2 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | not-called x | not-called x₁ | is-called x₂  = is-called (call-mtc3 x x₁ x₂)
dec-called v τ match t [z⇨ t₁ suc v₁ ⇨ t₂ ] | not-called x | not-called x₁ | not-called x₂ = not-called (no-call-match x x₁ x₂)


{-
Evidence for recursion
-}
data _▸rec_[_] : ∀{Γ τ ρ} → Γ ⊢´ τ ⊚ ρ → Context → ℕ → Set where
  no-rec-⇓ : ∀{Γ τ}{t : Γ ⊢´ τ ⊚ ⇓} → t ▸rec ø [ 0 ]
  no-rec-⇑ : ∀{Γ Δ τ v τ' ρ n}{t : Γ , v ⦂ τ ⊢´ τ' ⊚ ρ}{t' : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}
             → t ▸rec Δ [ n ] → v ⦂ τ not-called-in t' → (let´ v ← t' in´ t) ▸rec Δ [ n ]
  rec-⇑    : ∀{Γ Δ τ v τ' ρ n}{t : Γ , v ⦂ τ ⊢´ τ' ⊚ ρ}{t' : Γ , v ⦂ τ ⊢´ τ ⊚ ⇓}
             → t ▸rec Δ [ n ] → v ⦂ τ called-in t' → (let´ v ← t' in´ t) ▸rec (Δ , v ⦂ τ) [ suc n ]

extractType : ∀{Γ v τ τ' ρ} → Γ , v ⦂ τ ⊢´ τ' ⊚ ρ → Type
extractType {τ = τ} _ = τ

{-
It is decidable to check if a function is recursive
-}
dec-rec : ∀{Γ τ ρ} → (t : Γ ⊢´ τ ⊚ ρ) → ∃ ( λ (n : ℕ) → ∃ ( λ (Δ : Context) → t ▸rec Δ [ n ]))
dec-rec {ρ = ⇓} t = 0 /\ (ø /\ no-rec-⇓)
dec-rec (let´ v ← t in´ t₁) with dec-called v (extractType t₁) t | dec-rec t₁
... | is-called  x | n /\ Δ /\ r = suc n /\ (Δ , v ⦂ (extractType t₁) /\ rec-⇑ r x )
... | not-called x | n /\ Δ /\ r = n /\ (Δ /\ no-rec-⇑ r x )

{-
Context substitution is useful for inlining
-}
context-substitution : ∀{Γ Δ τ ρ} → Γ ⊆ Δ → Γ ⊢´ τ ⊚ ρ → Δ ⊢´ τ ⊚ ρ
context-substitution p zer = zer
context-substitution p (suc t) = suc (context-substitution p t)
context-substitution p (var v x) = var v (∈-substitution p x)
context-substitution p (abs v t) = abs v (context-substitution (keep p) t)
context-substitution p (app t t₁) = app (context-substitution p t) (context-substitution p t₁)
context-substitution p match t [z⇨ t₁ suc v ⇨ t₂ ] = match context-substitution p t
  [z⇨ context-substitution p t₁
   suc v ⇨ context-substitution (keep p) t₂ ]
context-substitution p (let´ v ← t in´ t₁) = let´ v ← context-substitution (keep p) t in´ context-substitution (keep p) t₁

{-
The next two theorems prove that
Context Substitution doesn't change
variable calls
-}
no-call-preserving : ∀{Γ Δ v τ₁ τ₂}{t : Δ ⊢´ τ₂ ⊚ ⇓}
                     (r : Δ ⊆ Γ)
                     → v ⦂ τ₁ not-called-in t
                     → v ⦂ τ₁ not-called-in (context-substitution r t)
no-call-preserving r no-call-zer = no-call-zer
no-call-preserving r (no-call-varn x) = no-call-varn x
no-call-preserving r (no-call-vart x) = no-call-vart x
no-call-preserving r (no-call-suc p) = no-call-suc (no-call-preserving r p)
no-call-preserving r (no-call-abs p) = no-call-abs (no-call-preserving (keep r) p)
no-call-preserving r (no-call-app p p₁)
  = no-call-app (no-call-preserving r p) (no-call-preserving r p₁)
no-call-preserving r (no-call-match p p₁ p₂)
  = no-call-match (no-call-preserving r p) (no-call-preserving r p₁) (no-call-preserving (keep r) p₂)

call-preserving : ∀{Γ Δ v τ₁ τ₂}{t : Δ ⊢´ τ₂ ⊚ ⇓}
                  (r : Δ ⊆ Γ)
                  → v ⦂ τ₁ called-in t
                  → v ⦂ τ₁ called-in (context-substitution r t)
call-preserving r call-var
  = call-var
call-preserving r (call-suc p)
  = call-suc (call-preserving r p)
call-preserving r (call-abs p)
  = call-abs (call-preserving (keep r) p)
call-preserving r (call-app1 p x)
  = call-app1 (call-preserving r p) (no-call-preserving r x)
call-preserving r (call-app2 x p)
  = call-app2 (no-call-preserving r x) (call-preserving r p)
call-preserving r (call-app12 p p₁)
  = call-app12 (call-preserving r p) (call-preserving r p₁)
call-preserving r (call-mtc1 p x x₁)
  = call-mtc1 (call-preserving r p) (no-call-preserving r x) (no-call-preserving (keep r) x₁)
call-preserving r (call-mtc2 x p x₁)
  = call-mtc2 (no-call-preserving r x) (call-preserving r p) (no-call-preserving (keep r) x₁)
call-preserving r (call-mtc3 x x₁ p)
  = call-mtc3 (no-call-preserving r x) (no-call-preserving r x₁) (call-preserving (keep r) p)
call-preserving r (call-mtc12 p p₁ x)
  = call-mtc12 (call-preserving r p) (call-preserving r p₁) (no-call-preserving (keep r) x)
call-preserving r (call-mtc13 p x p₁)
  = call-mtc13 (call-preserving r p) (no-call-preserving r x) (call-preserving (keep r) p₁)
call-preserving r (call-mtc23 x p p₁)
  = call-mtc23 (no-call-preserving r x) (call-preserving r p) (call-preserving (keep r) p₁)
call-preserving r (call-mtc123 p p₁ p₂)
  = call-mtc123 (call-preserving r p) (call-preserving r p₁) (call-preserving (keep r) p₂)

-- {-
-- We can safely drop something from the context if we know
-- that variable is not called at all
-- -}
-- safe-drop-name : ∀{Γ v v' τ τ'} → v' ⦂ τ' ∈ Γ , v ⦂ τ → ¬ (v' ≡ v) → v' ⦂ τ' ∈ Γ
-- safe-drop-name here         v≢v' = ⊥-elim (v≢v' refl)
-- safe-drop-name (there v∈Γv) v≢v' = v∈Γv
--
-- safe-drop-type : ∀{Γ v v' τ τ'} → v' ⦂ τ' ∈ Γ , v ⦂ τ → ¬ (τ ≡ τ') → v' ⦂ τ' ∈ Γ
-- safe-drop-type here         t≢t' = ⊥-elim (t≢t' refl)
-- safe-drop-type (there v∈Γv) t≢t' = v∈Γv
--
-- -- safe-dropex-name : ∀{Γ v₁ v₂ v₃ τ₁ τ₂ τ₃} → v₁ ⦂ τ₁ ∈ Γ , v₂ ⦂ τ₂ , v₃ ⦂ τ₃ → ¬ (v₁ ≡ v₂) → v₁ ⦂ τ₁ ∈ Γ , v₃ ⦂ τ₃
-- -- safe-dropex-name here      v₁≢v₂ = here
-- -- safe-dropex-name (there p) v₁≢v₂ = there (safe-drop-name p v₁≢v₂)
--
-- safe-∈-swap : ∀{Γ v₁ v₂ v₃ τ₁ τ₂ τ₃} → v₁ ⦂ τ₁ ∈ Γ , v₂ ⦂ τ₂ , v₃ ⦂ τ₃ → v₁ ⦂ τ₁ ∈ Γ , v₃ ⦂ τ₃ , v₂ ⦂ τ₂
-- safe-∈-swap here = there here
-- safe-∈-swap (there p) = ∈-substitution (keep (drop ⊆-refl)) p
--
-- safe-swap : ∀{Γ v₁ v₂ τ₁ τ₂ τ₃}(t : Γ , v₁ ⦂ τ₁ , v₂ ⦂ τ₂ ⊢´ τ₃ ⊚ ⇓)
--             → Γ , v₂ ⦂ τ₂ , v₁ ⦂ τ₁ ⊢´ τ₃ ⊚ ⇓
-- safe-swap zer        = zer
-- safe-swap (suc t)    = suc (safe-swap t)
-- safe-swap (var v x)  = var v (safe-∈-swap x)
-- safe-swap (abs v t)  = abs v (safe-swap {!   !} )
-- safe-swap (app t t₁) = {!   !}
-- safe-swap match t [z⇨ t₁ suc v ⇨ t₂ ] = {!   !}
--
-- -- safe-drop-extended : ∀{Γ v v' τ₁ τ₂ τ₃}(t : Γ , v ⦂ τ₁ , v' ⦂ τ₂ ⊢´ τ₃ ⊚ ⇓)
-- --                      → v ⦂ τ₁ not-called-in t
-- --                      → ∃ (λ (t' : Γ , v' ⦂ τ₂ ⊢´ τ₃ ⊚ ⇓) → v ⦂ τ₁ not-called-in t')
-- -- safe-drop-extended zer        no-call-zer
-- --   = zer /\ no-call-zer
-- -- safe-drop-extended (suc t)    (no-call-suc p)
-- --   = (suc (proj₁ (safe-drop-extended t p))) /\ (no-call-suc (proj₂ (safe-drop-extended t p)))
-- -- safe-drop-extended (var v x)  (no-call-varn x₁)  = (var v  (safe-dropex-name x λ x₂ → x₁ (sym x₂))) /\ no-call-varn x₁
-- -- safe-drop-extended (var v x)  (no-call-vart x₁)  = {!   !}
-- -- safe-drop-extended (abs v t)  (no-call-abs p)    = (abs v {!   !} ) /\ {!   !}
-- -- safe-drop-extended (app t t₁) (no-call-app p p₁) = {!   !}
-- -- safe-drop-extended match t [z⇨ t₁ suc v ⇨ t₂ ] (no-call-match p p₁ p₂)
-- --   = {!   !}
--
-- -- safe-drop : ∀{Γ τ τ' v}(t : Γ , v ⦂ τ ⊢´ τ' ⊚ ⇓) → v ⦂ τ not-called-in t → Γ ⊢´ τ' ⊚ ⇓
-- -- safe-drop zer no-call-zer                = zer
-- -- safe-drop (suc t) (no-call-suc p)        = suc (safe-drop t p)
-- -- safe-drop (var v' x) (no-call-varn x₁)   = var v' (safe-drop-name x x₁)
-- -- safe-drop (var v' x) (no-call-vart x₁)   = var v' (safe-drop-type x x₁)
-- -- safe-drop (abs v' t) (no-call-abs p)     = abs v' (proj₁ (safe-drop-extended t p))
-- -- safe-drop (app t t₁) (no-call-app p p₁)  = app (safe-drop t p) (safe-drop t₁ p₁)
-- -- safe-drop match t [z⇨ t₁ suc v' ⇨ t₂ ] (no-call-match p p₁ p₂)
-- --   = match safe-drop t p [z⇨ safe-drop t₁ p₁ suc v' ⇨ proj₁ (safe-drop-extended t₂ p₂) ]
