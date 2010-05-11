module Cryptol where
open import Data.Nat
open import Data.Vec

data Bit : Set where
  I O : Bit

Word : ℕ → Set
Word n = Vec Bit n

