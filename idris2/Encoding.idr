module Encoding

import Bit
import Data.Fin
import Data.Hash
import Data.LVect
import Data.SortedSet
import Data.Strings
import Encodable
import IndexType
import LinearUtils
import Utils

%default total

public export
data Encoding : (Encodable -> Type) -> Encodable -> Type where
  BitEncoding : (1 _ : f a) -> Encoding f a
  UnitEnc : Encoding f UnitEnc
  (&&) : (1 _ : Encoding f a) -> (1 _ : Encoding f b) -> Encoding f (a && b)
  Nil : Encoding f (EncVect Z a)
  (::) : (1 _ : Encoding f a) -> (1 _ : Encoding f (EncVect n a)) -> Encoding f (EncVect (S n) a)
  NewEncoding : {ident : String} -> (1 _ : Encoding f a) -> Encoding f (NewEnc ident a)

public export
data BitType : Type -> Encodable -> Type where
  MkBitType : (1 _ : t) -> BitType t Bit

export
removeBitType : (0 f : Encodable -> Type) -> (1 _ : BitType (f Bit) a) -> f a
removeBitType _ (MkBitType x) = x

export
length : Encoding (BitType _) (EncVect m _) -> (n : Nat ** m = n)
length [] = (Z ** Refl)
length (_ :: xs) with (length xs)
  length (_ :: xs) | (n ** Refl) = (S n ** Refl)

export
[ShowEncoding] Show t => Show (Encoding (BitType t) a) where
  show (BitEncoding (MkBitType x)) = show x
  show UnitEnc = "()"
  show (x && y) = "(" ++ show @{ShowEncoding} x ++ " && " ++ show @{ShowEncoding} y ++ ")"
  show [] = "[]"
  show [x] = "[" ++ show @{ShowEncoding} x ++ "]"
  show (x :: xs) = "[" ++ show @{ShowEncoding} x ++ ", " ++ (assert_total $ strTail $ show @{ShowEncoding} xs)
  show (NewEncoding {ident} x) = ident ++ " " ++ show @{ShowEncoding} x

export
map : (t1 -> t2) -> Encoding (BitType t1) a -> Encoding (BitType t2) a
map f (BitEncoding (MkBitType x)) = BitEncoding $ MkBitType $ f x
map _ UnitEnc = UnitEnc
map f (x && y) = map f x && map f y
map f [] = []
map f (x :: xs) = map f x :: map f xs
map f (NewEncoding x) = NewEncoding $ map f x

mapWithIndex' : (IndexType b -> IndexType a) -> (IndexType a -> t1 -> t2) -> Encoding (BitType t1) b -> Encoding (BitType t2) b
mapWithIndex' g f (BitEncoding (MkBitType x)) = BitEncoding $ MkBitType $ f (g EmptyIndex) x
mapWithIndex' _ _ UnitEnc = UnitEnc
mapWithIndex' g f (x && y) = mapWithIndex' (g . LeftIndex) f x && mapWithIndex' (g . RightIndex) f y
mapWithIndex' g f [] = []
mapWithIndex' g f (x :: xs) = mapWithIndex' (g . HeadIndex) f x :: mapWithIndex' (g . TailIndex) f xs
mapWithIndex' g f (NewEncoding x) = NewEncoding $ mapWithIndex' (g . NewEncIndex) f x

export
mapWithIndex : (IndexType a -> t1 -> t2) -> Encoding (BitType t1) a -> Encoding (BitType t2) a
mapWithIndex = mapWithIndex' id

export
mapEncodings : {a : Encodable} -> ({b : Encodable} -> PartialIndex a b -> f b -> g b) -> Encoding f a -> Encoding g a
mapEncodings h (BitEncoding x) = BitEncoding $ h EmptyIndex x
mapEncodings h UnitEnc = UnitEnc
mapEncodings h (x && y) = (mapEncodings (h . LeftIndex) x && mapEncodings (h . RightIndex) y)
mapEncodings h [] = []
mapEncodings h (x :: xs) = mapEncodings (h . HeadIndex) x :: mapEncodings (h . TailIndex) xs
mapEncodings h (NewEncoding x) = NewEncoding $ mapEncodings (h . NewEncIndex) x

export
traverse : Applicative f => (t1 -> f t2) -> Encoding (BitType t1) a -> f (Encoding (BitType t2) a)
traverse f (BitEncoding (MkBitType x)) = relax (BitEncoding . MkBitType) <$> f x
traverse f UnitEnc = pure UnitEnc
traverse f (x && y) = liftA2 (relax2 $ relax (&&)) (traverse f x) (traverse f y)
traverse f [] = pure []
traverse f (x :: xs) = liftA2 (relax2 $ relax (::)) (traverse f x) (traverse f xs)
traverse f (NewEncoding x) = relax NewEncoding <$> traverse f x

export
zipWith : (t1 -> t2 -> t3) -> Encoding (BitType t1) a -> Encoding (BitType t2) a -> Encoding (BitType t3) a
zipWith f (BitEncoding (MkBitType x)) (BitEncoding (MkBitType y)) = BitEncoding $ MkBitType $ f x y
zipWith f UnitEnc UnitEnc = UnitEnc
zipWith f (x1 && x2) (y1 && y2) = zipWith f x1 y1 && zipWith f x2 y2
zipWith f [] [] = []
zipWith f (x :: xs) (y :: ys) = zipWith f x y :: zipWith f xs ys
zipWith f (NewEncoding x) (NewEncoding y) = NewEncoding $ zipWith f x y

export
[HashableEncoding] Hashable t => Hashable (Encoding (BitType t) a) where
  hash (BitEncoding (MkBitType x)) = hash x
  hash UnitEnc = hash ()
  hash (x && y) = addSalt (hash @{HashableEncoding} x) (hash @{HashableEncoding} y)
  hash [] = hash ()
  hash (x :: xs) = addSalt (hash @{HashableEncoding} x) (assert_total $ hash @{HashableEncoding} xs)
  hash (NewEncoding x) = addSalt 0 $ hash @{HashableEncoding} x

export
fromInteger : (x : Integer) -> {auto prf : IsBit x} -> Encoding (BitType Bit) Bit
fromInteger x = BitEncoding $ MkBitType $ fromInteger x

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
mapBitAt g EmptyIndex (BitEncoding (MkBitType x)) = BitEncoding $ MkBitType $ g x
mapBitAt g (LeftIndex i)  (x && y) = (mapBitAt g i x && y)
mapBitAt g (RightIndex i) (x && y) = (x && mapBitAt g i y)
mapBitAt g (HeadIndex i) (x :: xs) = mapBitAt g i x :: xs
mapBitAt {a = EncVect (S n) a} g (TailIndex i) (x :: xs) = x :: mapBitAt {a = assert_smaller (EncVect (S n) a) $ EncVect n a} g i xs
mapBitAt g (NewEncIndex i) (NewEncoding x) = NewEncoding $ mapBitAt g i x

export
Dup t => Dup (BitType t a) where
  dup (MkBitType x) = MkBitType *** MkBitType $ dup x

  release (MkBitType x) = MkBitType <$> release x

export
{dupBit : (0 b : Encodable) -> Dup (t b)} -> Dup (Encoding t a) where
  dup (BitEncoding x) = BitEncoding *** BitEncoding $ dup @{dupBit a} x
  dup UnitEnc = UnitEnc # UnitEnc
  dup (x && y) = ((&&) **** (&&)) (dup x) (dup y)
  dup [] = [] # []
  dup (x :: xs) = ((::) **** (::)) (dup x) (dup xs)
  dup (NewEncoding x) = NewEncoding *** NewEncoding $ dup x

  release (BitEncoding x) = BitEncoding <$> release x
  release UnitEnc = MkUnrestricted UnitEnc
  release (x && y) = liftA2 (&&) (release x) (release y)
  release [] = MkUnrestricted []
  release (x :: xs) = liftA2 (::) (release x) (release xs)
  release (NewEncoding x) = NewEncoding <$> release x

export
IndexTypes : {a : Encodable} -> Encoding (BitType (IndexType a)) a
IndexTypes {a = Bit} = BitEncoding $ MkBitType EmptyIndex
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
encodingToList : Encoding (BitType t) a -> List t
encodingToList (BitEncoding (MkBitType x)) = [x]
encodingToList UnitEnc = []
encodingToList (x && y) = encodingToList x ++ encodingToList y
encodingToList [] = []
encodingToList (x :: xs) = encodingToList x ++ encodingToList xs
encodingToList (NewEncoding x) = encodingToList x

export
encodingToSet : Ord t => {auto pf : (b : Encodable) -> t = f b} -> Encoding f a -> SortedSet t
encodingToSet (BitEncoding x) = fromList [rewrite pf a in x]
encodingToSet UnitEnc = empty
encodingToSet (x && y) = union (encodingToSet x) (encodingToSet y)
encodingToSet [] = empty
encodingToSet (x :: xs) = union (encodingToSet x) (encodingToSet xs)
encodingToSet (NewEncoding x) = encodingToSet x

export
encodingBitTypeToSet : Ord t => Encoding (BitType t) a -> SortedSet t
encodingBitTypeToSet (BitEncoding (MkBitType x)) = fromList [x]
encodingBitTypeToSet UnitEnc = empty
encodingBitTypeToSet (x && y) = union (encodingBitTypeToSet x) (encodingBitTypeToSet y)
encodingBitTypeToSet [] = empty
encodingBitTypeToSet (x :: xs) = union (encodingBitTypeToSet x) (encodingBitTypeToSet xs)
encodingBitTypeToSet (NewEncoding x) = encodingBitTypeToSet x

