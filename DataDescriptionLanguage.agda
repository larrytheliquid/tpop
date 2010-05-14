module DataDescriptionLanguage where
open import Cryptol
open import Universe
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Char
open import Data.Maybe
open import Data.List
open import Data.Sum
open import Data.Product

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
