module Expansion.Unrolling where

open import Common.Name 
open import Common.Type
open import Common.Context
open import Expansion.Fuel
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

postulate {-- Next steps!! --}
    expand : Fuel → PCFTerm → NFPCFTerm
    preservation : ∀{Γ τ t f}
                   → TypeCheckOnPCF Γ t τ 
                   → TypeCheckOnNFPCF Γ (expand f t) τ
    
    