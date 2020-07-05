module IndexType

import Data.Fin
import Data.Hash
import Encodable

%default total

public export
IndexType : Encodable -> Type
IndexType Bit           = ()
IndexType (a && b)      = Either (IndexType a) (IndexType b)
IndexType (EncVect n a) = (Fin n, IndexType a)
IndexType (NewEnc _ a)  = IndexType a

export
[HashableIndexType] {a : Encodable} -> Hashable (IndexType a) where
  hash {a = Bit}         ()        = hash ()
  hash {a = _ && _}      (Left i)  = hash (the Int 0, hash @{HashableIndexType} i)
  hash {a = _ && _}      (Right i) = hash (the Int 1, hash @{HashableIndexType} i)
  hash {a = EncVect _ _} (n, i)    = hash (finToInteger n, hash @{HashableIndexType} i)
  hash {a = NewEnc _ _}  i         = hash @{HashableIndexType} i

