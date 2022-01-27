{-# OPTIONS --safe #-}

module Examples.Translation where

open import Common.Fuel
open import Common.Context
open import Common.Type
open import Transform.Translation
open import Examples.R
open import R.Syntax
open import L.Syntax

open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

L-term : ∅ , ℕ´ ⇒ ℕ´ ⇒ ℕ´ ⊪ ℕ´
L-term = app
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

_ : proj₂ (transform (gas 3) 1+2) ≡ L-term
_ = refl
