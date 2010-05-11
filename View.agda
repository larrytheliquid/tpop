module View where
open import Data.List

data ReverseView {A : Set} : List A → Set where
  [] : ReverseView []
  _∷_ : (x : A) → (xs : List A) → ReverseView (xs ++ [ x ])

view : {A : Set} → (xs : List A) → ReverseView xs
view [] = []
view (x ∷ xs) with view xs
view (x ∷ .[]) | [] = x ∷ []
view (x ∷ .(ys ++ [ y ])) | y ∷ ys = y ∷ (x ∷ ys)

shiftR : {A : Set} → List A → List A
shiftR xs with view xs
shiftR ._ | [] = []
shiftR ._ | y ∷ ys = y ∷ ys
