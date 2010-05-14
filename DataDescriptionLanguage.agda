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

parse : (f : Format) → List Bit → Maybe (⟦ f ⟧ × List Bit)
parse Bad _ = nothing
parse End bs = just (tt , bs)
parse (Base u) bs with read u
... | nothing = nothing
... | just v = just (v , bs)
parse (Plus f₁ f₂) bs with parse f₁ bs
... | just (x , cs) = just (inj₁ x , cs)
... | nothing with parse f₂ bs
... | just (y , ds) = just (inj₂ y , ds)
... | nothing = nothing
parse (Skip f₁ f₂) bs with parse f₁ bs
... | nothing = nothing
... | just (_ , cs) = parse f₂ cs
parse (Read f₁ f₂) bs with parse f₁ bs
... | nothing = nothing
... | just (x , cs) with parse (f₂ x) cs
... | nothing = nothing
... | just (y , ds) = just ((x , y) , ds)

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
