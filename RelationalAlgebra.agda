module RelationalAlgebra where
open import Universe
open import Data.Unit
open import Data.Bool
open import Data.String hiding (_==_)
open import Data.Product
open import Data.List
open import IO

Attribute = String × U
Schema = List Attribute

Cars : Schema
Cars = ( "Model" , VEC CHAR 20 )
     ∷ ( "Time"  , VEC CHAR 6 )
     ∷ [ "Wet"   , BOOL ]

infixr 5 _∷_

data Row : Schema → Set where
  [] : Row []
  _∷_ : ∀ {name u s} → el u → Row s → Row ((name , u) ∷ s)

Table : Schema → Set
Table s = List (Row s)

zonda : Row Cars
zonda = toVec "Pagani Zonda C12 F  "
      ∷ toVec "1:18.4"
      ∷ false ∷ []

postulate
  occurs : String → Schema → Bool
  lookup : String → Schema → U

data Expr : Schema → U → Set where
  _==_ < : ∀ {u s} → Expr s u → Expr s u → Expr s BOOL
  _!_ : (s : Schema) → (nm : String) → {_ : T (occurs nm s)} →
        Expr s (lookup nm s)

ServerName = String
TableName = String

postulate
  Handle : Schema → Set
  connect : ServerName → TableName → (s : Schema) → IO (Handle s)
  disjoin : Schema → Schema → Bool
  sub : Schema → Schema → Bool

data RA : Schema → Set where
  Read : ∀ {s} → Handle s → RA s
  Union Diff : ∀ {s} → RA s → RA s → RA s
  Product : ∀ {s s'} → {_ : T (disjoin s s')} → RA s → RA s' → RA s
  Project : ∀ {s} → (s' : Schema) → {_ : T (sub s s')} → RA s → RA s'
  Select : ∀ {s} → Expr s BOOL → RA s → RA s

Models : Schema
Models = [ "Model" , VEC CHAR 20 ]

models : Handle Cars → RA Models
models h = Project Models (Read h)

-- wet : Handle Cars → RA Models
-- wet h = Project Models (Select (Cars ! "Wet") (Read h))

postulate
  toSQL : ∀ {s} → RA s → String
  query : {s : Schema} → RA s → IO (List (Row s))
