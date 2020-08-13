module Encoding

import Bit
import Data.Fin
import Data.Hash
import Data.SortedSet
import Encodable
import IndexType
import Utils

%default total

public export
data Encoding : (Encodable -> Type) -> Encodable -> Type where
  BitEncoding : f a -> Encoding f a
  UnitEnc : Encoding f UnitEnc
  (&&) : Encoding f a -> Encoding f b -> Encoding f (a && b)
  Nil : Encoding f (EncVect Z a)
  (::) : Encoding f a -> Encoding f (EncVect n a) -> Encoding f (EncVect (S n) a)
  NewEncoding : Encoding f a -> Encoding f (NewEnc i a)

public export
BitType : Type -> Encodable -> Type
BitType t Bit = t
BitType _ _ = Void

export
removeBitType : {a : Encodable} -> (f : Encodable -> Type) -> BitType (f Bit) a -> f a
removeBitType {a = Bit} _ x = x

{-
export
[ShowEncoding] Show t => Show (Encoding (BitType t) a) where
  show {a = Bit} (BitEncoding x) = show x
  show UnitEnc = "()"
  show {t} (x && y) = "(" ++ show @{ShowEncoding {t}} x ++ " && " ++ show @{ShowEncoding {t}} y ++ ")"
  show [] = "[]"
  show {t} [x] = "[" ++ show @{ShowEncoding {t}} x ++ "]"
  show {t} (x :: xs) = "[" ++ show @{ShowEncoding {t}} x ++ ", " ++ (assert_total $ strTail $ show @{ShowEncoding {t}} xs)
  show {t} {a = NewEnc ident a} (NewEncoding x) = ident ++ " " ++ show @{ShowEncoding {t}} x
  -}

export
map : (t1 -> t2) -> Encoding (BitType t1) a -> Encoding (BitType t2) a
map {a = Bit} f (BitEncoding x) = BitEncoding $ f x
map _ UnitEnc = UnitEnc
map f (x && y) = map f x && map f y
map f [] = []
map f (x :: xs) = map f x :: map f xs
map f (NewEncoding x) = NewEncoding $ map f x

export
mapEncodings : {a : Encodable} -> ({b : Encodable} -> PartialIndex a b -> f b -> g b) -> Encoding f a -> Encoding g a
mapEncodings h (BitEncoding x) = BitEncoding $ h EmptyIndex x
mapEncodings h UnitEnc = UnitEnc
mapEncodings h (x && y) = (mapEncodings (h . LeftIndex) x && mapEncodings (h . RightIndex) y)
mapEncodings h [] = []
mapEncodings h (x :: xs) = mapEncodings (h . HeadIndex) x :: mapEncodings (h . TailIndex) xs
mapEncodings h (NewEncoding x) = NewEncoding $ mapEncodings (h . NewEncIndex) x

export
traverse : Applicative f => {a : Encodable} -> (t1 -> f t2) -> Encoding (BitType t1) a -> f (Encoding (BitType t2) a)
traverse {a = Bit} f (BitEncoding x) = BitEncoding <$> f x
traverse f UnitEnc = pure UnitEnc
traverse f (x && y) = liftA2 (&&) (traverse f x) (traverse f y)
traverse f [] = pure []
traverse f (x :: xs) = liftA2 (::) (traverse f x) (traverse f xs)
traverse f (NewEncoding x) = NewEncoding <$> traverse f x

export
zipWith : {a : Encodable} -> (t1 -> t2 -> t3) -> Encoding (BitType t1) a -> Encoding (BitType t2) a -> Encoding (BitType t3) a
zipWith {a = Bit} f (BitEncoding x) (BitEncoding y) = BitEncoding $ f x y
zipWith f UnitEnc UnitEnc = UnitEnc
zipWith f (x1 && x2) (y1 && y2) = zipWith f x1 y1 && zipWith f x2 y2
zipWith f [] [] = []
zipWith f (x :: xs) (y :: ys) = zipWith f x y :: zipWith f xs ys
zipWith f (NewEncoding x) (NewEncoding y) = NewEncoding $ zipWith f x y

export
[HashableEncoding] Hashable t => Hashable (Encoding (BitType t) a) where
  saltedHash64 {a = Bit} (BitEncoding x) = saltedHash64 x
  saltedHash64 UnitEnc = saltedHash64 ()
  saltedHash64 {t} (x && y) = saltedHash64 (hash @{HashableEncoding {t}} x, hash @{HashableEncoding {t}} y)
  saltedHash64 [] = saltedHash64 ()
  saltedHash64 {t} (x :: xs) = saltedHash64 (hash @{HashableEncoding {t}} x, assert_total $ hash @{HashableEncoding {t}} xs)
  saltedHash64 {t} (NewEncoding x) = saltedHash64 (0, hash @{HashableEncoding {t}} x)

export
fromInteger : (x : Integer) -> {auto prf : IsBit x} -> Encoding (BitType Bit) Bit
fromInteger x = BitEncoding $ fromInteger x

export
replicate : {a : Encodable} -> (f Bit) -> Encoding f a
replicate {a = Bit} x = BitEncoding x
replicate {a = UnitEnc} _ = UnitEnc
replicate {a = _ && _} x = replicate x && replicate x
replicate {a = EncVect Z _} _ = []
replicate {a = EncVect (S n) a} x = replicate x :: replicate {a = assert_smaller (EncVect (S n) a) $ EncVect n a} x
replicate {a = NewEnc _ _} x = NewEncoding $ replicate x

export
index : PartialIndex a b -> Encoding (BitType t) a -> Encoding (BitType t) b
index EmptyIndex x = x
index (LeftIndex i)  (x && _) = index i x
index (RightIndex i) (_ && x) = index i x
index (HeadIndex i) (x :: _)  = index i x
index (TailIndex i) (_ :: xs) = index i xs
index (NewEncIndex i) (NewEncoding x) = index i x

export
mapBitAt : (t -> t) -> PartialIndex a Bit -> Encoding (BitType t) a -> Encoding (BitType t) a
mapBitAt g EmptyIndex (BitEncoding x) = BitEncoding $ g x
mapBitAt g (LeftIndex i)  (x && y) = (mapBitAt g i x && y)
mapBitAt g (RightIndex i) (x && y) = (x && mapBitAt g i y)
mapBitAt g (HeadIndex i) (x :: xs) = mapBitAt g i x :: xs
mapBitAt {a = EncVect (S n) a} g (TailIndex i) (x :: xs) = x :: mapBitAt {a = assert_smaller (EncVect (S n) a) $ EncVect n a} g i xs
mapBitAt g (NewEncIndex i) (NewEncoding x) = NewEncoding $ mapBitAt g i x

export
IndexTypes : {a : Encodable} -> Encoding (BitType (IndexType a)) a
IndexTypes {a = Bit} = BitEncoding EmptyIndex
IndexTypes {a = UnitEnc} = UnitEnc
IndexTypes {a = a1 && a2} =
     map LeftIndex  IndexTypes
  && map RightIndex IndexTypes
IndexTypes {a = EncVect Z _} = []
IndexTypes {a = EncVect (S n) a} =
     map HeadIndex IndexTypes
  :: map TailIndex (IndexTypes {a = assert_smaller (EncVect (S n) a) $ EncVect n a})
IndexTypes {a = NewEnc _ a} = NewEncoding $ map NewEncIndex IndexTypes

export
indexVect : Fin n -> Encoding (BitType t) (EncVect n a) -> Encoding (BitType t) a
indexVect FZ (x :: _) = x
indexVect (FS k) (_ :: xs) = indexVect k xs

export
encodingToList : {a : Encodable} -> Encoding (BitType t) a -> List t
encodingToList {a = Bit} (BitEncoding x) = [x]
encodingToList UnitEnc = []
encodingToList (x && y) = encodingToList x ++ encodingToList y
encodingToList [] = []
encodingToList (x :: xs) = encodingToList x ++ encodingToList xs
encodingToList (NewEncoding x) = encodingToList x

export
encodingToSet : Ord t => {a : Encodable} -> Encoding (BitType t) a -> SortedSet t
encodingToSet {a = Bit} (BitEncoding x) = fromList [x]
encodingToSet UnitEnc = empty
encodingToSet (x && y) = union (encodingToSet x) (encodingToSet y)
encodingToSet [] = empty
encodingToSet (x :: xs) = union (encodingToSet x) (encodingToSet xs)
encodingToSet (NewEncoding x) = encodingToSet x

