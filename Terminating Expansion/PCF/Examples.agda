module PCF.Examples where

open import PCF.Syntax
open import PCF.TypeSystem

infixl 18 _∙_

-- Syntatic Sugar for function application
_∙_ : Term → Term → Term
_∙_ = app

ex1S : Term
ex1S = (fix "sum" 
          (abs "x" 
            (abs "y" 
              (match (var "x") 
                [z⇨ (var "y") 
                 suc "w" ⇨ ((var "sum") ∙ (var "w") ∙ (suc (var "y"))) ]
              )
            )
          )
        )

ex1T : Type
ex1T = nat ⇒ nat ⇒ nat

_ : ø ⊢ ex1S ⦂ ex1T
_ = tfix 
      (tabs 
        (tabs 
          (tmch 
            (tvar 
              (there here)
            ) 
            (tvar here) 
            (tapp 
              (tapp 
                (tvar (there (there (there here)))) 
                (tvar here)
              ) 
              (tsuc 
                (tvar (there here))
              )
            )
          )
        )
      ) 