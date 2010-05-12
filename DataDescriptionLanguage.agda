module DataDescriptionLanguage where
open import Data.Bool
open import Data.Char
open import Data.String
open import Data.Nat
open import Data.Vec hiding (_++_)

data U : Set where
  BOOL CHAR NAT : U
  VEC : U → ℕ → U

el : U → Set
el BOOL = Bool
el CHAR = Char
el NAT = ℕ
el (VEC u n) = Vec (el u) n

postulate charToString : Char → String

parens : String → String
parens s = "(" ++ s ++ ")"

show : {u : U} → el u → String
show {BOOL} true = "true"
show {BOOL} false = "false"
show {CHAR} c = charToString c
show {NAT} zero = "zero"
show {NAT} (suc n) = "suc " ++ parens (show n)
show {VEC u zero} [] = "[]"
show {VEC u (suc n)} (x ∷ xs) = show x ++ " ∷ " ++ parens (show xs)
