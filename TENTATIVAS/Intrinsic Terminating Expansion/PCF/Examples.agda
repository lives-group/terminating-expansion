module PCF.Examples where

open import Common.Type
open import Common.Context
open import Common.Name
open import Common.Depth using (Depth; ⇑; ⇓)
open import PCF.Syntax
open import PCF.Syntax.Properties
open import PCF.Syntax.Unrolling
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ)

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
only-loop3-rec : mutualLoop' ▸rec (ø , "loop3" ⦂ nat ⇒ nat) [ 1 ]
only-loop3-rec = no-rec-⇑
                     (no-rec-⇑
                          (rec-⇑ no-rec-⇓
                           (call-app2 (no-call-varn loop3≢loop2)
                                      (call-app2
                                         (no-call-varn loop3≢loop1)
                                           call-var)))
                      (no-call-abs (no-call-abs (no-call-app
                         (no-call-varn loop2≢f)
                           (no-call-varn loop2≢x)))))
                 (no-call-abs (no-call-abs (no-call-app
                                              (no-call-varn loop1≢f)
                                              (no-call-varn loop1≢x))))
  where
    loop2≢f : ¬ ("loop2" ≡ "f")
    loop2≢f ()

    loop2≢x : ¬ ("loop2" ≡ "x")
    loop2≢x ()

    loop1≢f : ¬ ("loop1" ≡ "f")
    loop1≢f ()

    loop1≢x : ¬ ("loop1" ≡ "x")
    loop1≢x ()

    loop3≢loop2 : ¬ ("loop3" ≡ "loop2")
    loop3≢loop2 ()

    loop3≢loop1 : ¬ ("loop3" ≡ "loop1")
    loop3≢loop1 ()

{-
and I can prove sum is indeed recursive (and the only one)
-}
sum-is-recursive : sum ▸rec (ø , "sum" ⦂ nat ⇒ nat ⇒ nat) [ 1 ]
sum-is-recursive = rec-⇑ no-rec-⇓ (call-abs (call-abs (call-mtc3
                        (no-call-varn sum≢x1 )
                        (no-call-varn sum≢x2 )
                        (call-app1 (call-app1
                                      call-var
                                      (no-call-varn sum≢x3))
                                   (no-call-suc
                                      (no-call-varn sum≢x2))))))
  where
    sum≢x1 : ¬ ("sum" ≡ "x1")
    sum≢x1 ()

    sum≢x2 : ¬ ("sum" ≡ "x2")
    sum≢x2 ()

    sum≢x3 : ¬ ("sum" ≡ "x3")
    sum≢x3 ()

{-
As long as the type is different,
variables with same name won't cause confusion.
For example, at first glance the function
"x" below seems recursive, but I can prove
it actually isn't.
-}
ex-term : ø , "x" ⦂ nat , "sum" ⦂ nat ⇒ nat ⇒ nat ⊢´ nat ⇒ nat ⊚ ⇑
ex-term = let´ "x" ← (var "sum" (there here))
                     ∙ (var "x" (there (there here)))
          in´ (var "x" here )

dif-type : ex-term ▸rec ø [ 0 ]
dif-type = no-rec-⇑ no-rec-⇓ (no-call-app (no-call-varn x≢sum) (no-call-vart n≢nn))
  where
    x≢sum : ¬ ("x" ≡ "sum")
    x≢sum ()
    n≢nn  : ¬ (nat ⇒ nat ≡ nat)
    n≢nn ()

{-
With context substitution we can use already defined
expressions to avoid rewriting them
-}
two : ø ⊢´ nat ⊚ ⇓
two = suc (suc zer)

f-on-context : ø , "f" ⦂ nat ⇒ nat ⊢´ nat ⊚ ⇓
f-on-context = var "f" here ∙ context-substitution (drop empty) two

{-
Inline a function into another is essential to
the recursion expansion.
-}
inl-f1 : ø ⊢´ nat ⇒ nat ⇒ nat ⊚ ⇓
inl-f1 = abs "x" (abs "y" (var "y" here))

inl-f2 : ø , "f1" ⦂ nat ⇒ nat ⇒ nat ⊢´ nat ⊚ ⇓
inl-f2 = var "f1" here
          ∙ zer
          ∙ (var "f1" here
             ∙ zer
             ∙ zer)

f1-called-in-f2 : "f1" ⦂ nat ⇒ nat ⇒ nat called-in inl-f2
f1-called-in-f2 = call-app12
                    (call-app1
                      call-var
                      no-call-zer
                    )
                    (call-app1
                      (call-app1
                        call-var
                        no-call-zer
                      )
                      no-call-zer
                    )

right-answer-inline : ø , "f1" ⦂ nat ⇒ nat ⇒ nat ⊢´ nat ⊚ ⇓
right-answer-inline = abs "x" (abs "y" (var "y" here))
               ∙ zer
               ∙ (abs "x" (abs "y" (var "y" here))
                  ∙ zer
                  ∙ zer)

_ : inline f1-called-in-f2 inl-f1 (drop empty) ≡ right-answer-inline
_ = refl

{-
We can expand terms if we can prove
they call the var we are saying they
represent.
-}
exp-example : ø , "sum" ⦂ nat ⇒ nat ⇒ nat ⊢´ nat ⇒ nat ⇒ nat ⊚ ⇓
exp-example = (abs "x1"
                (abs "x2"
                  match var "x1" (there here)
                    [z⇨ var "x2" here
                     suc "x3" ⇨ var "sum" (there (there (there here)))
                                ∙ var "x3" here
                                ∙ suc (var "x2" (there here))
                    ]
                )
              )

sum-called-in-exp-example : "sum" ⦂ nat ⇒ nat ⇒ nat called-in exp-example
sum-called-in-exp-example = call-abs
                             (call-abs
                               (call-mtc3
                                 (no-call-varn sum≢x1)
                                 (no-call-varn sum≢x2)
                                 (call-app1
                                   (call-app1
                                     call-var
                                     (no-call-varn sum≢x3)
                                   ) (no-call-suc
                                       (no-call-varn sum≢x2)
                                     )
                                 )
                               )
                              )
  where
    sum≢x1 : ¬ ("sum" ≡ "x1")
    sum≢x1 ()

    sum≢x2 : ¬ ("sum" ≡ "x2")
    sum≢x2 ()

    sum≢x3 : ¬ ("sum" ≡ "x3")
    sum≢x3 ()

right-answer-expand-once : ø , "sum" ⦂ nat ⇒ nat ⇒ nat ⊢´ nat ⇒ nat ⇒ nat ⊚ ⇓
right-answer-expand-once = abs "x1"
                            (abs "x2"
                             match var "x1" (there here) [z⇨ var "x2" here suc "x3" ⇨
                             app
                             (app
                              (abs "x1"
                               (abs "x2"
                                match var "x1" (there here) [z⇨ var "x2" here suc "x3" ⇨
                                app
                                (app
                                 (var "sum" (there (there (there (there (there (there here)))))))
                                 (var "x3" here))
                                (suc (var "x2" (there here)))
                                ]))
                              (var "x3" here))
                             (suc (var "x2" (there here)))
                             ])

_ : extract (expand-once sum-called-in-exp-example) ≡ right-answer-expand-once
_ = refl

_ : extractExpansion (expand sum-called-in-exp-example (gas 1)) ≡ right-answer-expand-once
_ = refl

vf : VecFuel 1
vf = gas 1 ∷ []

right-answer-unroll : ø ⊢´ nat ⇒ nat ⇒ nat ⊚ ⇑
right-answer-unroll = let´ "sum" ← right-answer-expand-once
                        in´ var "sum" here

_ : unroll sum-is-recursive vf ≡ right-answer-unroll
_ = refl
