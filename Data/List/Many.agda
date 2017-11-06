module Data.List.Many {a p} {A : Set a} where

open import Data.List hiding (length)
open import Data.List.All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Function
open import Level

Many : (P : A → Set p) → List A → Set (a ⊔ p)
Many P = All (Maybe ∘ P)

length : {P : A → Set p} {xs : _} → Many P xs → ℕ
length [] = 0
length (nothing ∷ xs) = length xs
length (just _  ∷ xs) = length xs + 1
