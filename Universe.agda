module Universe where
open import Cryptol
open import Data.Bool
open import Data.Char
open import Data.String
open import Data.Nat
open import Data.Maybe
open import Data.Product
open import Data.Vec hiding (_++_)

data U : Set where
  BIT BOOL CHAR NAT : U
  VEC : U → ℕ → U

el : U → Set
el BIT = Bit
el BOOL = Bool
el CHAR = Char
el NAT = ℕ
el (VEC u n) = Vec (el u) n

postulate charToString : Char → String

parens : String → String
parens s = "(" ++ s ++ ")"

show : {u : U} → el u → String
show {BIT} I = "I"
show {BIT} O = "O"
show {BOOL} true = "true"
show {BOOL} false = "false"
show {CHAR} c = charToString c
show {NAT} zero = "zero"
show {NAT} (suc n) = "suc " ++ parens (show n)
show {VEC _ zero} [] = "[]"
show {VEC _ (suc _)} (x ∷ xs) = show x ++ " ∷ " ++ parens (show xs)

postulate
  read : (u : U) → String → Maybe (el u × String)
