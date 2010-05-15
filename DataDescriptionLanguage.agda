module DataDescriptionLanguage where
open import Cryptol
open import Universe
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Char
open import Data.Nat
open import Data.Vec hiding (_>>=_)
open import Data.String hiding (_==_)
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

infixl 1 _>>=_ _>>_

_>>_ : Format → Format → Format
f₁ >> f₂ = Skip f₁ f₂

_>>=_ : (f : Format) → (⟦ f ⟧ → Format) → Format
x >>= f = Read x f

parse : (f : Format) → String → Maybe (⟦ f ⟧ × String)
parse Bad _ = nothing
parse End s = just (tt , s)
parse (Base u) s = read u s
parse (Plus f₁ f₂) s with parse f₁ s
... | just (x , s') = just (inj₁ x , s')
... | nothing with parse f₂ s
... | just (y , s'') = just (inj₂ y , s'')
... | nothing = nothing
parse (Skip f₁ f₂) s with parse f₁ s
... | nothing = nothing
... | just (_ , s') = parse f₂ s'
parse (Read f₁ f₂) s with parse f₁ s
... | nothing = nothing
... | just (x , s') with parse (f₂ x) s'
... | nothing = nothing
... | just (y , s'') = just ((x , y) , s'')

data _≡_ {S : Set₁} (A : S) : S → Set₁ where
    refl : A ≡ A

char : Char → Format
char c = Read (Base CHAR)
              (λ c′ → if c == c′ then End else Bad)

testChar : ⟦ char 'A' ⟧ ≡ 
  Σ Char (λ x → ⟦ if 'A' == x then End else Bad ⟧)
testChar = refl


satisfy : (f : Format) → (⟦ f ⟧ → Bool) → Format
satisfy f pred = Read f right where
  right : ⟦ f ⟧ → Format
  right x = if pred x then End else Bad

vec : Format
vec =
  Base NAT >>= λ n →
  Base (VEC BIT n)

testVec : ⟦ vec ⟧ ≡ Σ ℕ (Vec Bit)
testVec = refl

exampleVec : ⟦ vec ⟧
exampleVec = 2 , (I ∷ O ∷ [])

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

testPbm : ⟦ pbm ⟧ ≡ 
  Σ ℕ (λ w → Σ ℕ (λ h → Σ (Vec (Vec Bit w) h) (λ _ → ⊤)))
testPbm = refl
