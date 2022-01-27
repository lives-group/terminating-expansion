{-# OPTIONS --safe #-}

module Examples.Translation where

open import Common.Fuel
open import Common.Context
open import Common.Type
open import Transform.Translation
open import Examples.R
open import R.Syntax
open import L.Syntax
open import L.Semantics

open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

l-term : ∅ , ℕ´ ⇒ ℕ´ ⇒ ℕ´ ⊪ ℕ´
l-term = app
          (app
           (abs
            (abs
             (match (var (there here)) (var here)
              (app
               (app
                (abs
                 (abs
                  (match (var (there here)) (var here)
                   (app
                    (app
                     (abs
                      (abs
                       (match (var (there here)) (var here)
                        (app
                         (app
                          (abs
                           (abs
                            (match (var (there here)) (var here)
                             (app (app error (var here)) (suc´ (var (there here)))))))
                          (var here))
                         (suc´ (var (there here)))))))
                     (var here))
                    (suc´ (var (there here)))))))
                (var here))
               (suc´ (var (there here)))))))
           (suc´ zero´))
          (suc´ (suc´ zero´))

tr-term : ∅ , ℕ´ ⇒ ℕ´ ⇒ ℕ´ ⊪ ℕ´
tr-term = proj₂ (transform (gas 3) 1+2)

_ : tr-term ≡ l-term
_ = refl

l-term1 : ∅ ⊪ ℕ´
l-term1 = app (abs tr-term) (abs (abs zero´))

_ : proj₁ (output (⊪-eval (gas 100) l-term1)) ≡ suc´ (suc´ (suc´ zero´))
_ = refl
