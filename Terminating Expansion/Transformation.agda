module Transformation where

-- Agda Stdlib 1.7
open import Data.Bool using (Bool; true; false)

open import Common.Name 
open import Common.Type
open import Common.Context
open import Transformation.Fuel
open import PCF.Unrolling using (NamedFun; expand)
open import PCF.Examples using (ex1S)
import PCF.Syntax
import NFPCF.Syntax 
import PCF.TypeSystem 
import NFPCF.TypeSystem

{-- Some aliases --}
PCFTerm : Set
PCFTerm = PCF.Syntax.Term

NFPCFTerm : Set
NFPCFTerm = NFPCF.Syntax.Term

TypeCheckOnPCF : Context → PCFTerm → Type → Set
TypeCheckOnPCF = PCF.TypeSystem._⊢_⦂_

TypeCheckOnNFPCF : Context → NFPCFTerm → Type → Set
TypeCheckOnNFPCF = NFPCF.TypeSystem._⊢_⦂_
{-- End of aliases --}

translate : PCFTerm → Name → NFPCFTerm
translate PCF.Syntax.ufn v = NFPCF.Syntax.ufn
translate PCF.Syntax.zer v = NFPCF.Syntax.zer
translate (PCF.Syntax.suc t) v = NFPCF.Syntax.suc (translate t v)
translate (PCF.Syntax.var x) v with v equals x 
...                            | true  = NFPCF.Syntax.out
...                            | false = NFPCF.Syntax.var x
translate (PCF.Syntax.abs x t) v = NFPCF.Syntax.abs x (translate t v)
translate (PCF.Syntax.app t t') v = NFPCF.Syntax.app (translate t v) (translate t' v)
translate (PCF.Syntax.fix x t) v = translate t v
translate PCF.Syntax.match t [z⇨ t₁ suc x ⇨ t₂ ] v = NFPCF.Syntax.match (translate t v) 
                                                     [z⇨ (translate t₁ v) 
                                                      suc x ⇨ (translate t₂ v)]

{-- Transformation process terminates --}
transform : PCFTerm → Fuel → NFPCFTerm
transform t n with expand n t
...           | (PCF.Syntax.fix v t) = translate (PCF.Syntax.fix v t) v
...           | t' = translate t' ""

{-- TODO: Transformation preserves types --}
postulate preservation : ∀{t τ f Γ} → TypeCheckOnPCF Γ t τ → TypeCheckOnNFPCF Γ (transform t f) τ