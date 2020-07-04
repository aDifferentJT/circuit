module WithBitTypes

import Data.Hash
import public Data.Vect
import Encodable
import IndexType
import Utils

%default total

public export
data NewType : String -> Type -> Type where
  MkNewType : a -> NewType i a

export
Functor (NewType i) where
  map f (MkNewType x) = MkNewType $ f x


public export
WithBitType : Type -> Encodable -> Type
WithBitType t Bit           = t
WithBitType t (a & b)       = (WithBitType t a, WithBitType t b)
WithBitType t (EncVect n a) = Vect n (WithBitType t a)
WithBitType t (NewEnc i a)  = NewType i (WithBitType t a)

export
mapBits : (t1 -> t2) -> WithBitType t1 a -> WithBitType t2 a
mapBits {a = Bit}         f b = f b
mapBits {a = _ & _}       f (x, y) = (mapBits f x, mapBits f y)
mapBits {a = EncVect _ _} f xs = map (mapBits f) xs
mapBits {a = NewEnc _ a}  f x = map (mapBits f) x

export
[HashableWithBitType] Hashable t => Hashable (WithBitType t a) where
  saltedHash64 {a = Bit}         x             = saltedHash64 x
  saltedHash64 {a = _ & _}       (x, y)        = saltedHash64 (hash @{HashableWithBitType} x, hash @{HashableWithBitType} y)
  saltedHash64 {a = EncVect _ _} xs            = saltedHash64 $ map (hash @{HashableWithBitType}) xs
  saltedHash64 {a = NewEnc _ _}  (MkNewType x) = saltedHash64 @{HashableWithBitType} x

export
replicate : t -> WithBitType t a
replicate {a = Bit} x = x
replicate {a = _ & _} x = (replicate x, replicate x)
replicate {a = EncVect _ _} x = Utils.replicate $ replicate x
replicate {a = NewEnc _ _} x = MkNewType $ replicate x

export
bitAt : IndexType a -> WithBitType t a -> t
bitAt {a=Bit}         ()         x             = x
bitAt {a=_ & _}       (Left is)  (x, _)        = bitAt is x
bitAt {a=_ & _}       (Right is) (_, x)        = bitAt is x
bitAt {a=EncVect _ _} (i, is)    x             = bitAt is $ index i x
bitAt {a=NewEnc _ _}  is         (MkNewType x) = bitAt is x

export
mapBitAt : {a : Encodable} -> (t -> t) -> IndexType a -> WithBitType t a -> WithBitType t a
mapBitAt {a = Bit} f () b = f b
mapBitAt {a = _ & _} f (Left is)  (x, y) = (mapBitAt f is x, y)
mapBitAt {a = _ & _} f (Right is) (x, y) = (x, mapBitAt f is y)
mapBitAt {a = EncVect Z _} _ (_, _) [] = []
mapBitAt {a = EncVect (S _) _} f (FZ,   is) (x :: xs) = mapBitAt f is x :: xs
mapBitAt {a = EncVect (S n) a} f (FS i, is) (x :: xs) = x :: mapBitAt f {a = assert_smaller (EncVect (S n) a) (EncVect n a)} (i, is) xs
mapBitAt {a = NewEnc _ _} f is x = map (mapBitAt f is) x

export
IndexTypes : WithBitType (IndexType a) a
IndexTypes {a = Bit} = ()
IndexTypes {a = a & b} =
  ( mapBits (\i => the (IndexType (a & b)) (Left i)) IndexTypes
  , mapBits (\i => the (IndexType (a & b)) (Right i)) IndexTypes
  )
IndexTypes {a = EncVect _ _} = map (\i => mapBits (\is => (i, is)) IndexTypes) range
IndexTypes {a = NewEnc _ _} = MkNewType IndexTypes

