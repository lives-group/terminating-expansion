module Transformation where

-- Agda Stdlib 1.7
open import Data.Bool using (Bool; true; false)

open import Common.Name
open import Common.Type
open import Common.Context
open import Transformation.Fuel
open import Data.Nat using (ℕ; zero; suc)
open import PCF.Unrolling using (NamedFun; expand)
open import PCF.Examples using (ex1S)
import PCF.Syntax
import NFPCF.Syntax
import PCF.TypeSystem
import NFPCF.TypeSystem

{-- Some aliases --}
PCFTerm : Set
PCFTerm = PCF.Syntax.Term

PCFTerm' : Set
PCFTerm' = PCF.Syntax.Term'

NFPCFTerm : Set
NFPCFTerm = NFPCF.Syntax.Term

TypeCheckOnPCF : Context → PCFTerm → Type → Set
TypeCheckOnPCF = PCF.TypeSystem._⊢_⦂_

TypeCheckOnNFPCF : Context → NFPCFTerm → Type → Set
TypeCheckOnNFPCF = NFPCF.TypeSystem._⊢_⦂_
{-- End of aliases --}

translate' : PCFTerm' → Name → NFPCFTerm
translate' PCF.Syntax.zer v      = NFPCF.Syntax.zer
translate' (PCF.Syntax.suc t) v  = NFPCF.Syntax.suc (translate' t v)
translate' (PCF.Syntax.var x) "" = NFPCF.Syntax.var x
translate' (PCF.Syntax.var x) v with x equals v
...                             | true  = NFPCF.Syntax.out
...                             | false = NFPCF.Syntax.var x
translate' (PCF.Syntax.abs x t) v  = NFPCF.Syntax.abs x (translate' t v)
translate' (PCF.Syntax.app t t₁) v = NFPCF.Syntax.app (translate' t v) (translate' t₁ v)
translate' PCF.Syntax.match t [z⇨ t₁ suc x ⇨ t₂ ] v = NFPCF.Syntax.match translate' t v [z⇨ translate' t₁ v suc x ⇨ translate' t₂ v ]

-- This function assumes that no name can be empty, which is assured by a proper lexical analysis
translate : PCFTerm → NFPCFTerm
translate (PCF.Syntax.trm x)    = translate' x ""
translate (PCF.Syntax.fix x x₁) = translate' x₁ x

{--
Transformation process terminates.
Since Agda 2.4 the flag --no-termination-checker
no longer works. Instead, functions must be
marked with a pragma to skip termination checker.
Since this no function in this project has such pragma
The succesfull typechecking proves its termination.
--}
transform : PCFTerm → Fuel → NFPCFTerm
transform t f = translate (expand f t)

-- {-- If a PCF Term is typable, then transformation to NFPCF with fuel 0 keeps the same type --}
-- I think it will only work on intrinsic
-- transform0-preserves-types : ∀{Γ t τ} → TypeCheckOnPCF Γ t τ → TypeCheckOnNFPCF Γ (transform t 0) τ
-- transform0-preserves-types {Γ} {PCF.Syntax.trm .PCF.Syntax.zer} {.nat} PCF.TypeSystem.tzer = NFPCF.TypeSystem.tzer
-- transform0-preserves-types {Γ} {PCF.Syntax.trm .(PCF.Syntax.suc _)} {.nat} (PCF.TypeSystem.tsuc e) = NFPCF.TypeSystem.tsuc (transform0-preserves-types e)
-- transform0-preserves-types {Γ} {PCF.Syntax.trm .(PCF.Syntax.var _)} {τ} (PCF.TypeSystem.tvar x) = NFPCF.TypeSystem.tvar x
-- transform0-preserves-types {Γ} {PCF.Syntax.trm .(PCF.Syntax.abs _ _)} {.(_ ⇒ _)} (PCF.TypeSystem.tabs e) = NFPCF.TypeSystem.tabs (transform0-preserves-types e)
-- transform0-preserves-types {Γ} {PCF.Syntax.trm .(PCF.Syntax.app _ _)} {τ} (PCF.TypeSystem.tapp e e₁) = NFPCF.TypeSystem.tapp (transform0-preserves-types e) (transform0-preserves-types e₁)
-- transform0-preserves-types {Γ} {PCF.Syntax.trm .(PCF.Syntax.match _ [z⇨ _ suc _ ⇨ _ ])} {τ} (PCF.TypeSystem.tmch e e₁ e₂) = NFPCF.TypeSystem.tmch (transform0-preserves-types e) (transform0-preserves-types e₁) (transform0-preserves-types e₂)
-- transform0-preserves-types {Γ} {PCF.Syntax.fix x x₁} {τ} (PCF.TypeSystem.tfix e) = {!   !}
