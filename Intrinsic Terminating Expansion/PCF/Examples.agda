module PCF.Examples where

open import Common.Type
open import Common.Context
open import Common.Name
open import PCF.Syntax
open import PCF.Syntax.Properties
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤)

-- Syntatic Sugar for function application
infixl 20 _∙_

_∙_ : ∀{Γ τ τ'} → Γ ⊢´ τ ⇒ τ' ⊚ ⇓ → Γ ⊢´ τ ⊚ ⇓ → Γ ⊢´ τ' ⊚ ⇓
_∙_ = app

id : ø ⊢´ (nat ⇒ nat) ⊚ ⇓
id = abs "x" (var "x" here)

idWithLet : ø ⊢´ (nat ⇒ nat) ⊚ ⇑
idWithLet = let´ "id" ← abs "x" (var "x" here) in´ var "id" here

{-
PCF is useless as a logical system,
but having general recursion allows
Turing completeness, which is useful
for programming.
-}
loop : ∀{τ} → ø ⊢´ τ ⊚ ⇑
loop = let´ "f" ← var "f" here in´ var "f" here

sum : ø ⊢´ (nat ⇒ nat ⇒ nat) ⊚ ⇑
sum = let´ "sum" ← (abs "x1"
                    (abs "x2"
                      match var "x1" (there here)
                        [z⇨ var "x2" here
                         suc "x3" ⇨ var "sum" (there (there (there here)))
                                    ∙ var "x3" here
                                    ∙ suc (var "x2" (there here))
                        ]
                    )
                   )
        in´ var "sum" here

1+2 : ø ⊢´ nat ⊚ ⇑
1+2 = let´ "sum" ← (abs "x1"
                    (abs "x2"
                      match var "x1" (there here)
                        [z⇨ var "x2" here
                         suc "x3" ⇨ var "sum" (there (there (there here)))
                                    ∙ var "x3" here
                                    ∙ suc (var "x2" (there here))
                        ]
                    )
                   )
        in´ (var "sum" here
            ∙ suc zer
            ∙ suc (suc zer))

{-
If I want to prove a theorem that only applies to
expressions with let, that is straightforward
-}
exampleTheorem : ∀{Γ τ} → Γ ⊢´ τ ⊚ ⇑ → Set
exampleTheorem (let´ v ← t in´ t₁) = ⊤

{-
We can create nested let's but with some
constraints. The Type System won't let you assign
a let to a let-variable.

So we can't have expressions like:

let x ← let y ← z in y in x

but we can do this:
-}
nested : ø ⊢´ nat ⊚ ⇑
nested = let´ "x" ← abs "z" (var "z" here)
         in´
           (let´ "y" ← suc zer
            in´ (var "x" (there here)
                 ∙ var "y" here)
            )

{-
We can also have "mutually recursive functions",
in some sense. Notice, however, that they actually
are a simple, conventional recursion. So, there is no way to
write a recursive function that doesn't "look like" one.
-}
mutualLoop : ø ⊢´ nat ⇒ nat ⊚ ⇑
mutualLoop = let´ "loop1" ← abs "f"
                              (abs "x"
                                (app
                                  (var "f" (there here))
                                  (var "x" here)
                                )
                              )
              in´
                (let´ "loop2" ← app
                                  (var "loop1"
                                    (there here)
                                  )
                                  (var "loop2" here)
                 in´ var "loop2" here
                )

mutualLoop' : ø ⊢´ nat ⇒ nat ⊚ ⇑
mutualLoop' = let´ "loop1" ← abs "f"
                              (abs "x"
                                (app
                                  (var "f" (there here))
                                  (var "x" here)
                                )
                              )
              in´
                (let´ "loop2" ← abs "f"
                                  (abs "x"
                                    (app
                                      (var "f" (there here))
                                      (var "x" here)
                                    )
                                  )
                 in´ (let´ "loop3" ← app (var "loop2" (there here) )
                                         (app (var "loop1" (there (there here)) )
                                              (var "loop3" here )
                                         )
                      in´
                        var "loop3" here
                     )
                )

{-
I can prove that loop3 is the only recursive function above
-}

ev1 : ¬ ("loop2" equals "f")
ev1 ()

ev2 : ¬ ("loop2" equals "x")
ev2 ()

ev3 : ¬ ("loop1" equals "f")
ev3 ()

ev4 : ¬ ("loop1" equals "x")
ev4 ()

only-loop3-rec : mutualLoop' ▸rec (ø , "loop3" ⦂ nat ⇒ nat)
only-loop3-rec = no-rec-⇑
                     (no-rec-⇑
                          (rec-⇑ no-rec-⇓
                           (call-app2 (call-app2 call-var)))
                      (no-call-abs (no-call-abs (no-call-app (no-call-var ev1 ) (no-call-var ev2)))))
                 (no-call-abs (no-call-abs (no-call-app (no-call-var ev3) (no-call-var ev4))))

{-
But I can prove sum is recursive indeed
-}
sum-is-recursive : sum ▸rec (ø , "sum" ⦂ nat ⇒ nat ⇒ nat)
sum-is-recursive = rec-⇑ no-rec-⇓ (call-abs (call-abs (call-mtc3 (call-app1 (call-app1 call-var)))))

{-
With context substitution we can use already defined
expressions to avoid rewriting them
-}
two : ø ⊢´ nat ⊚ ⇓
two = suc (suc zer)

f-on-context : ø , "f" ⦂ nat ⇒ nat ⊢´ nat ⊚ ⇓
f-on-context = var "f" here ∙ context-substitution (drop empty) two
