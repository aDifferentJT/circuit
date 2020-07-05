module WithBitType

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
WithBitType t (a && b)      = (WithBitType t a, WithBitType t b)
WithBitType t (EncVect n a) = Vect n (WithBitType t a)
WithBitType t (NewEnc i a)  = NewType i (WithBitType t a)

export
mapBits : {a : Encodable} -> (t1 -> t2) -> WithBitType t1 a -> WithBitType t2 a
mapBits {a = Bit}         f b = f b
mapBits {a = _ && _}      f (x, y) = (mapBits f x, mapBits f y)
mapBits {a = EncVect _ _} f xs = map (mapBits f) xs
mapBits {a = NewEnc _ a}  f x = map (mapBits f) x

export
[HashableWithBitType] {a : Encodable} -> Hashable t => Hashable (WithBitType t a) where
  hash {a = Bit}         x = hash x
  hash {a = _ && _}      (x, y) = combineHashes (hash @{HashableWithBitType} x) (hash @{HashableWithBitType} y)
  hash {a = EncVect _ _} x = hash @{HashableVect HashableWithBitType} x
  hash {a = NewEnc _ _} (MkNewType x) = hash @{HashableWithBitType} x

export
replicate : {a : Encodable} -> t -> WithBitType t a
replicate {a = Bit} x = x
replicate {a = _ && _} x = (WithBitType.replicate x, WithBitType.replicate x)
replicate {a = EncVect _ _} x = Utils.replicate $ WithBitType.replicate x
replicate {a = NewEnc _ _} x = MkNewType $ WithBitType.replicate x

export
bitAt : {a : Encodable} -> IndexType a -> WithBitType t a -> t
bitAt {a=Bit}         ()        x             = x
bitAt {a=_ && _}      (Left i)  (x, _)        = bitAt i x
bitAt {a=_ && _}      (Right i) (_, x)        = bitAt i x
bitAt {a=EncVect _ _} (k, i)    x             = bitAt i $ index k x
bitAt {a=NewEnc _ _}  i         (MkNewType x) = bitAt i x

export
mapBitAt : {a : Encodable} -> (t -> t) -> IndexType a -> WithBitType t a -> WithBitType t a
mapBitAt {a = Bit} f () b = f b
mapBitAt {a = _ && _} f (Left is)  (x, y) = (mapBitAt f is x, y)
mapBitAt {a = _ && _} f (Right is) (x, y) = (x, mapBitAt f is y)
mapBitAt {a = EncVect Z _} _ (k, _) [] = absurd k
mapBitAt {a = EncVect (S n) a} f i (x :: xs) =
  case i of
       (FZ, i') => mapBitAt f i' x :: xs
       (FS k, i') => x :: mapBitAt f {a = assert_smaller (EncVect (S n) a) (EncVect n a)} (k, i') xs
mapBitAt {a = NewEnc _ _} f is x = map (mapBitAt f is) x

export
IndexTypes : {a : Encodable} -> WithBitType (IndexType a) a
IndexTypes {a = Bit} = ()
IndexTypes {a = a && b} =
  ( mapBits (\i => the (IndexType (a && b)) (Left i)) IndexTypes
  , mapBits (\i => the (IndexType (a && b)) (Right i)) IndexTypes
  )
IndexTypes {a = EncVect _ _} = map (\i => mapBits (\is => (i, is)) IndexTypes) range
IndexTypes {a = NewEnc _ _} = MkNewType IndexTypes

