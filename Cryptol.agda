module Cryptol where
open import Data.Nat
open import Data.Vec hiding ([_])
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

data Bit : Set where
  I O : Bit

Word : Pred ℕ
Word n = Vec Bit n

Word-Universal : Universal Word
Word-Universal zero = []
Word-Universal (suc n) with Word-Universal n
Word-Universal (suc ._) | [] = I ∷ []
Word-Universal (suc ._) | x ∷ xs = I ∷ x ∷ xs

-- swab′ without assurance that same vector was split

split : {A : Set} (n m : ℕ) → Vec A (m * n) → Vec (Vec A n) m
split n zero [] = []
split n (suc k) xs = take n xs ∷ split n k (drop n xs)

swab′ : Word 32 → Word 32
swab′ xs with split 8 4 xs
... | a ∷ b ∷ c ∷ d ∷ [] = concat (b ∷ a ∷ c ∷ d ∷ [])

-- swab with assurance that same vector was split

data SplitView {A : Set} : {n : ℕ} → (m : ℕ) → Vec A (m * n) → Set where
  [_] : ∀ {n m} → (xss : Vec (Vec A n) m) → SplitView m (concat xss)

postulate
  splitConcatLemma : ∀ {A n} m → (xs : Vec A (m * n)) →
    concat (split n m xs) ≡ xs

view : {A : Set} (n m : ℕ) (xs : Vec A (m * n)) → SplitView m xs
view n m xs with [ split n m xs ]
... | v rewrite splitConcatLemma m xs = v

SplitView-Universal : {A : Set}{n m : ℕ} → Universal (SplitView {A} {n} m)
SplitView-Universal {_} {n} {m} xs = view n m xs

swab : Word 32 → Word 32
swab xs with view 8 4 xs
swab .(concat (a ∷ b ∷ c ∷ d ∷ [])) | [ a ∷ b ∷ c ∷ d ∷ [] ] = concat (b ∷ a ∷ c ∷ d ∷ [])
