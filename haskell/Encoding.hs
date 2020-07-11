{-# LANGUAGE MagicHash #-}

module Encoding
  ( Encoding(..)
  )where

import Data.Hashable
import Data.Set
import Encodable
--import EqOrdUtils
import IndexType

data Encoding :: (EncodableKind -> *) -> EncodableKind -> * where
  BitEncoding :: f a -> Encoding f a
  UnitEnc :: Encoding f UnitEnc
  PairEnc :: Encoding f a -> Encoding f b -> Encoding f (a && b)
  NilEnc :: Encoding f (EncVect Z a)
  ConsEnc :: Encoding f a -> Encoding f (EncVect n a) -> Encoding f (EncVect (S n) a)
  NewEncoding :: KnownSymbol ident => Encoding f a -> Encoding f (NewEnc ident a)

data BitType :: * -> EncodableKind -> * where
  BitType :: t -> BitType t BitT

removeBitType :: EncodableType a -> BitType (f BitT) a -> f a
removeBitType BitV x = x

instance Show t => Show (Encoding (BitType t) a) where
  show (BitEncoding (BitType x)) = show x
  show UnitEnc = "()"
  show (PairEnc x y) = "(" ++ show x ++ " && " ++ show y ++ ")"
  show NilEnc = "[]"
  show (ConsEnc x NilEnc) = "[" ++ show x ++ "]"
  show (ConsEnc x xs) = "[" ++ show x ++ ", " ++ (tail $ show xs)
  show (NewEncoding x) = symbolVal (proxy#) ++ " " ++ show x

mapBits :: (t1 -> t2) -> Encoding (BitType t1) a -> Encoding (BitType t2) a
mapBits f (BitEncoding (BitType x)) = BitEncoding $ BitType $ f x
mapBits _ UnitEnc = UnitEnc
mapBits f (PairEnc x y) =
  (  mapBits f x
  && mapBits f y
  )
mapBits f NilEnc = NilEnc
mapBits f (ConsEnc x xs) = ConsEnc (mapBits f x) (mapBits f xs)
mapBits f (NewEncoding x) = NewEncoding $ mapBits f x

export
mapEncodings :: {a :: Encodable} -> ({b :: Encodable} -> PartialIndex a b -> f b -> g b) -> Encoding f a -> Encoding g a
mapEncodings h (BitEncoding x) = BitEncoding $ h EmptyIndex x
mapEncodings h UnitEnc = UnitEnc
mapEncodings h (PairEnc x y) = PairEnc (mapEncodings (h . LeftIndex) x) (mapEncodings (h . RightIndex) y)
mapEncodings h NilEnc = NilEnc
mapEncodings h (ConsEnc x xs) = ConsEnc (mapEncodings (h . HeadIndex) x) (mapEncodings (h . TailIndex) xs)
mapEncodings h (NewEncoding x) = NewEncoding $ mapEncodings (h . NewEncIndex) x

instance Hashable t => Hashable (Encoding (BitType t) a) where
  hashWithSalt (BitEncoding (BitType x)) = hashWithSalt x
  hashWithSalt UnitEnc = hashWithSalt ()
  hashWithSalt (PairEnc x y) = hashWithSalt (x, y)
  hashWithSalt NilEnc = hashWithSalt ()
  hashWithSalt (ConsEnc x xs) = hashWithSalt (x, xs)
  hashWithSalt (NewEncoding x) = hashWithSalt (0, x)

export
replicate :: EncodableType a -> f BitT -> Encoding f a
replicate BitV x = BitEncoding x
replicate UnitEncV _ = UnitEnc
replicate (PairEncV _ _) x = replicate x && replicate x
replicate (EncVectV _) _ = NilEnc
replicate (EncVectV _) x = ConsEnc (replicate x) (replicate x)
replicate (NewEnc _) x = NewEncoding $ replicate x

export
index :: PartialIndex a b -> Encoding (BitType t) a -> Encoding (BitType t) b
index EmptyIndex x = x
index (LeftIndex i)  (PairEnc x _) = index i x
index (RightIndex i) (PairEnc _ x) = index i x
index (HeadIndex i) (ConsEnc x _)  = index i x
index (TailIndex i) (ConsEnc _ xs) = index i xs
index (NewEncIndex i) (NewEncoding x) = index i x

export
mapBitAt :: (t -> t) -> PartialIndex a Bit -> Encoding (BitType t) a -> Encoding (BitType t) a
mapBitAt g EmptyIndex (BitEncoding x) = BitEncoding $ g x
mapBitAt g (LeftIndex i)  (PairEnc x y) = PairEnc (mapBitAt g i x) y
mapBitAt g (RightIndex i) (PairEnc x y) = PairEnc x (mapBitAt g i y)
mapBitAt g (HeadIndex i) (ConsEnc x xs) = ConsEnc (mapBitAt g i x) xs
mapBitAt g (TailIndex i) (ConsEnc x xs) = ConsEnc x (mapBitAt g i xs)
mapBitAt g (NewEncIndex i) (NewEncoding x) = NewEncoding $ mapBitAt g i x

indexTypes :: EncodableType a -> Encoding (BitType (IndexType a)) a
indexTypes BitV = BitEncoding EmptyIndex
indexTypes UnitEncV = UnitEnc
indexTypes (PairEnc a b) = PairEnc (mapBits LeftIndex $ IndexTypes a) (mapBits RightIndex $ IndexTypes b)
indexTypes (EncVectV _) = NilEnc
indexTypes (EncVectV a) = ConsEnc (mapBits HeadIndex $ IndexTypes a) (mapBits TailIndex $ IndexTypes $ EncVectV a)
indexTypes (NewEnc a) = NewEncoding $ mapBits NewEncIndex $ IndexTypes a

export
indexVect :: Fin n -> Encoding (BitType t) (EncVect n a) -> Encoding (BitType t) a
indexVect FZ (x :::: _) = x
indexVect (FS k) (_ :::: xs) = indexVect k xs

export
encodingToSet :: {a :: Encodable} -> ((x :: Encodable) -> Ord (f x)) => Encoding f a -> Set (b :: Encodable ** f b)
encodingToSet (BitEncoding x) = fromList [(a ** x)]
encodingToSet UnitEnc = empty
encodingToSet (PairEnc x y) = union (encodingToSet x) (encodingToSet y)
encodingToSet NilEnc = empty
encodingToSet (ConsEnc x xs) = union (encodingToSet x) (encodingToSet xs)
encodingToSet (NewEncoding x) = encodingToSet x

