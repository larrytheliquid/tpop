module View where
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality

data ShiftRView {A : Set} : List A → Set where
  [] : ShiftRView []
  shifted : (x : A) → (xs : List A) → ShiftRView (xs ++ [ x ])

example : ShiftRView (1 ∷ 2 ∷ 3 ∷ [])
example = shifted 3 (1 ∷ 2 ∷ [])

view : {A : Set} → (xs : List A) → ShiftRView xs
view [] = []
view (x ∷ xs) with view xs
view (x ∷ ._) | [] = shifted x []
view (x ∷ ._) | shifted y ys = shifted y (x ∷ ys)

example₂ : ShiftRView (1 ∷ 2 ∷ 3 ∷ [])
example₂ = view (1 ∷ 2 ∷ 3 ∷ [])

shiftR : {A : Set} → List A → List A
shiftR xs with view xs
shiftR ._ | [] = []
shiftR ._ | shifted y ys = y ∷ ys

example₃ : shiftR (1 ∷ 2 ∷ 3 ∷ []) ≡ (3 ∷ 1 ∷ 2 ∷ [])
example₃ = refl
