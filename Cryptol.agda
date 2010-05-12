module Cryptol where
open import Data.Nat
open import Data.Vec
open import Relation.Unary

data Bit : Set where
  I O : Bit

Word : Pred ℕ
Word n = Vec Bit n

Word-Universal : Universal Word
Word-Universal zero = []
Word-Universal (suc n) with Word-Universal n
Word-Universal (suc ._) | [] = [ I ]
Word-Universal (suc ._) | x ∷ xs = I ∷ x ∷ xs

