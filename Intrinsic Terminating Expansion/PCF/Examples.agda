module PCF.Examples where

open import PCF.Syntax
open import Common.Type
open import Common.Context

-- Syntatic Sugar for function application

infixl 20 _∙_

_∙_ : ∀{Γ τ τ'} → Γ ⊢ τ ⇒ τ' → Γ ⊢ τ → Γ ⊢ τ'
_∙_ = app

id : ø ⊢ (nat ⇒ nat)
id = abs "x0" (var here )

{-
PCF is useless as a logical system,
but having general recursion allows
Turing completeness, which is useful
for programming.
-}
loop : ∀{τ} → ø ⊢ τ
loop = fix "x0" (var here)

sum : ø ⊢ (nat ⇒ nat ⇒ nat)
sum = fix "x0"
        (abs "x1"
          (abs "x2"
            match var (there here)
              [z⇨ var here
               suc "x3" ⇨ var (there (there (there here)))
                          ∙ var here
                          ∙ suc (var (there here))
              ]
          )
        )

1+2 : ø ⊢ nat
1+2 = fix "x0"
        (abs "x1"
          (abs "x2"
            match var (there here)
              [z⇨ var here
               suc "x3" ⇨ var (there (there (there here))) ∙ var here ∙ suc (var (there here))
              ]
          )
        )
        ∙ suc zer
        ∙ suc (suc zer)
