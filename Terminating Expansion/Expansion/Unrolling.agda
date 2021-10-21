module Expansion.Unrolling where

open import Common.Name 
open import Common.Type
open import Common.Context
open import Expansion.Fuel
open import PCF.Utils using (NamedFun; expand)
open import Data.Bool using (Bool; true; false)
import PCF.Syntax
import NFPCF.Syntax 
import PCF.TypeSystem 
import NFPCF.TypeSystem

{-- some aliases --}
PCFTerm : Set
PCFTerm = PCF.Syntax.Term

NFPCFTerm : Set
NFPCFTerm = NFPCF.Syntax.Term

TypeCheckOnPCF : Context → PCFTerm → Type → Set
TypeCheckOnPCF = PCF.TypeSystem._⊢_⦂_

TypeCheckOnNFPCF : Context → NFPCFTerm → Type → Set
TypeCheckOnNFPCF = NFPCF.TypeSystem._⊢_⦂_
{-- end of aliases --}

translate : PCFTerm → Name → NFPCFTerm
translate PCF.Syntax.ufn v = NFPCF.Syntax.ufn
translate PCF.Syntax.zer v = NFPCF.Syntax.zer
translate (PCF.Syntax.suc t) v = NFPCF.Syntax.suc (translate t v)
translate (PCF.Syntax.var x) v with v equals x 
...                            | true  = NFPCF.Syntax.out
...                            | false = NFPCF.Syntax.var x
translate (PCF.Syntax.abs x t) v = NFPCF.Syntax.abs x (translate t v)
translate (PCF.Syntax.app t t') v = NFPCF.Syntax.app (translate t v) (translate t' v)
translate (PCF.Syntax.fix x t) v = NFPCF.Syntax.out -- (What should be the translation of a inner fix?)
translate PCF.Syntax.match t [z⇨ t₁ suc x ⇨ t₂ ] v = NFPCF.Syntax.match (translate t v) 
                                                     [z⇨ (translate t₁ v) 
                                                      suc x ⇨ (translate t₂ v)]

{-- Transformation process always terminate --}
transform : ∀{t : PCFTerm} → Fuel → NamedFun t → NFPCFTerm
transform {t} n (NamedFun.funName v) = translate (expand n t) v

{-- TODO: Transformation preserves types --}
postulate preservation : ∀{Γ τ t f}{n : NamedFun t}
                   → TypeCheckOnPCF Γ t τ 
                   → TypeCheckOnNFPCF Γ (transform f n) τ
-- preservation (PCF.TypeSystem.tfix e) = {! !}