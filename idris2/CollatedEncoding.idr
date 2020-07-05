module CollatedEncoding

import Data.SortedSet
import Data.Vect
import Encodable
import EqOrdUtils
import PartialIndex

%default total

public export
data CollatedEncoding : (Encodable -> Type) -> Encodable -> Type where
  CollatedBit : f a -> CollatedEncoding f a
  (&&) : CollatedEncoding f a -> CollatedEncoding f b -> CollatedEncoding f (a && b)
  CollatedVect : Vect n (CollatedEncoding f a) -> CollatedEncoding f (EncVect n a)
  CollatedNewEnc : (CollatedEncoding f a) -> CollatedEncoding f (NewEnc i a)

export
mapCollatedEncoding : {a : Encodable} -> ((b : Encodable) -> PartialIndex a b -> f b -> g b) -> CollatedEncoding f a -> CollatedEncoding g a
mapCollatedEncoding h (CollatedBit x) = CollatedBit $ h a EmptyIndex x
mapCollatedEncoding {a = a1 && a2} h (x && y) = mapCollatedEncoding hX x && mapCollatedEncoding hY y
  where
    hX : (b : Encodable) -> PartialIndex a1 b -> f b -> g b
    hX b i = h b $ LeftIndex i
    hY : (b : Encodable) -> PartialIndex a2 b -> f b -> g b
    hY b i = h b $ RightIndex i
mapCollatedEncoding {a = EncVect n a} h (CollatedVect xs) = CollatedVect $ map (\(i, x) => mapCollatedEncoding (h' i) x) $ zip range xs
  where
    h' : Fin n -> (b : Encodable) -> PartialIndex a b -> f b -> g b
    h' k b i = h b $ VectIndex k i
mapCollatedEncoding {a = NewEnc ident a} h (CollatedNewEnc x) = CollatedNewEnc $ mapCollatedEncoding h' x
  where
    h' : (b : Encodable) -> PartialIndex a b -> f b -> g b
    h' b i = h b $ NewEncIndex i

export
partialEncodingToSet : {a : Encodable} -> ((x : Encodable) -> Ord (f x)) => CollatedEncoding f a -> SortedSet (b : Encodable ** f b)
partialEncodingToSet (CollatedBit x) = fromList @{OrdDPair} [(a ** x)]
partialEncodingToSet (x && y) = union (partialEncodingToSet x) (partialEncodingToSet y)
partialEncodingToSet (CollatedVect xs) = foldl (\s => union s . partialEncodingToSet) (empty @{OrdDPair}) xs
partialEncodingToSet (CollatedNewEnc x) = partialEncodingToSet x

