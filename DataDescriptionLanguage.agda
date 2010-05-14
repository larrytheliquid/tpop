module DataDescriptionLanguage where
open import Cryptol
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Char
open import Data.String hiding (_==_)
open import Data.Nat
open import Data.Vec hiding (_++_; _>>=_)
open import Data.Sum
open import Data.Product

data U : Set where
  BIT CHAR NAT : U
  VEC : U → ℕ → U

el : U → Set
el BIT = Bit
el CHAR = Char
el NAT = ℕ
el (VEC u n) = Vec (el u) n

postulate charToString : Char → String

parens : String → String
parens s = "(" ++ s ++ ")"

show : {u : U} → el u → String
show {BIT} I = "I"
show {BIT} O = "O"
show {CHAR} c = charToString c
show {NAT} zero = "zero"
show {NAT} (suc n) = "suc " ++ parens (show n)
show {VEC _ zero} [] = "[]"
show {VEC _ (suc _)} (x ∷ xs) = show x ++ " ∷ " ++ parens (show xs)

mutual
  data Format : Set where
    Bad End : Format
    Base : U → Format
    Plus Skip : Format → Format → Format
    Read : (f : Format) → (⟦ f ⟧ → Format) → Format

  ⟦_⟧ : Format → Set
  ⟦ Bad ⟧ = ⊥
  ⟦ End ⟧ = ⊤
  ⟦ Base u ⟧ = el u
  ⟦ Plus f₁ f₂ ⟧ = ⟦ f₁ ⟧ ⊎ ⟦ f₂ ⟧
  ⟦ Skip _ f ⟧ = ⟦ f ⟧
  ⟦ Read f₁ f₂ ⟧ = Σ ⟦ f₁ ⟧ λ x → ⟦ f₂ x ⟧

char : Char → Format
char c = Read (Base CHAR)
              (λ c′ → if c == c′ then End else Bad)

satisfy : (f : Format) → (⟦ f ⟧ → Bool) → Format
satisfy f pred = Read f right where
  right : ⟦ f ⟧ → Format
  right x = if pred x then End else Bad

infixl 1 _>>=_ _>>_

_>>_ : Format → Format → Format
f₁ >> f₂ = Skip f₁ f₂

_>>=_ : (f : Format) → (⟦ f ⟧ → Format) → Format
x >>= f = Read x f

pbm : Format
pbm =
  char 'P' >>
  char '4' >>
  char ' ' >>
  Base NAT >>= λ w →
  char ' ' >>
  Base NAT >>= λ h →
  char '\n' >>
  Base (VEC (VEC BIT w) h) >>= λ _ →
  End
