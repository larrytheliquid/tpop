module RelationalAlgebra where
open import Universe
open import Data.Bool
open import Data.String
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

ServerName = String
TableName = String

postulate
  Handle : Schema → Set
  connect : ServerName → TableName → (s : Schema) → IO (Handle s)
