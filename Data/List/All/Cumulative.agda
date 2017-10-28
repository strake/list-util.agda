module Data.List.All.Cumulative {a p} {A : Set a} where

open import Data.List hiding (all)
open import Function
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary using (Decidable)

infixr 5 _∷_
data All (P : List A → A → Set p) : List A → Set (a ⊔ p) where
    [] : All P []
    _∷_ : ∀ {x xs} (px : P xs x) (pxs : All P xs) → All P (x ∷ xs)

head : ∀ {P : List A → A → Set p} {x xs} → All P (x ∷ xs) → P xs x
head (px ∷ _) = px

tail : ∀ {P : List A → A → Set p} {x xs} → All P (x ∷ xs) → All P xs
tail (_ ∷ pxs) = pxs

all : ∀ {P : List A → A → Set p} → (∀ xs x → Dec (P xs x)) → (xs : List A) → Dec (All P xs)
all p [] = yes []
all p (x ∷ xs) with p xs x
... | yes px = Dec.map′ (_∷_ px) tail (all p xs)
... | no ¬px = no (¬px ∘ head)
