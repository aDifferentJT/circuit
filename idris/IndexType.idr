module IndexType

import Data.Fin
import Data.Hash
import Encodable

%default total

public export
IndexType : Encodable -> Type
IndexType Bit           = ()
IndexType (a & b)       = Either (IndexType a) (IndexType b)
IndexType (EncVect n a) = (Fin n, IndexType a)
IndexType (NewEnc _ a)  = IndexType a

export
[HashableIndexType] Hashable (IndexType a) where
  saltedHash64 {a=Bit}         ()        = saltedHash64 ()
  saltedHash64 {a=_ & _}       (Left i)  = saltedHash64 (the Int 0, hash @{HashableIndexType} i)
  saltedHash64 {a=_ & _}       (Right i) = saltedHash64 (the Int 1, hash @{HashableIndexType} i)
  saltedHash64 {a=EncVect _ _} (n, i)    = saltedHash64 (finToInteger n, hash @{HashableIndexType} i)
  saltedHash64 {a=NewEnc _ _}  i         = saltedHash64 i

