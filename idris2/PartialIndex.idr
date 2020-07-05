module PartialIndex

import AuxProofs
import Data.DPair.Extra
import Data.List
import Data.SortedSet
import Data.Vect
import Decidable.Equality
import Encodable
import EqOrdUtils
import IndexType
import Utils
import WithBitType

%default total

public export
data PartialIndex : Encodable -> Encodable -> Type where
  EmptyIndex : PartialIndex a a
  LeftIndex : PartialIndex a b -> PartialIndex (a && _) b
  RightIndex : PartialIndex a b -> PartialIndex (_ && a) b
  VectIndex : Fin n -> PartialIndex a b -> PartialIndex (EncVect n a) b
  NewEncIndex : PartialIndex a b -> PartialIndex (NewEnc _ a) b

export
partialIndex : PartialIndex a b -> WithBitType t a -> WithBitType t b
partialIndex EmptyIndex x = x
partialIndex (LeftIndex i) (x, _) = partialIndex i x
partialIndex (RightIndex i) (_, x) = partialIndex i x
partialIndex (VectIndex k i) x = partialIndex i $ index k x
partialIndex (NewEncIndex i) (MkNewType x) = partialIndex i x

export
Eq (PartialIndex a b) where
  EmptyIndex == EmptyIndex = True
  (LeftIndex i1) == (LeftIndex i2) = i1 == i2
  (RightIndex i1) == (RightIndex i2) = i1 == i2
  (VectIndex k1 i1) == (VectIndex k2 i2) = k1 == k2 && i1 == i2
  (NewEncIndex i1) == (NewEncIndex i2) = i1 == i2
  _ == _ = False

export
Ord (PartialIndex a b) where
  compare EmptyIndex EmptyIndex = EQ
  compare (LeftIndex i1) (LeftIndex i2) = compare i1 i2
  compare (RightIndex i1) (RightIndex i2) = compare i1 i2
  compare (VectIndex k1 i1) (VectIndex k2 i2) = thenCompare (compare k1 k2) (compare i1 i2)
  compare (NewEncIndex i1) (NewEncIndex i2) = compare i1 i2

  compare EmptyIndex (LeftIndex _)   = LT
  compare EmptyIndex (RightIndex _)  = LT
  compare EmptyIndex (VectIndex _ _) = LT
  compare EmptyIndex (NewEncIndex _) = LT
  compare (LeftIndex _)   EmptyIndex = GT
  compare (RightIndex _)  EmptyIndex = GT
  compare (VectIndex _ _) EmptyIndex = GT
  compare (NewEncIndex _) EmptyIndex = GT
  
  compare (LeftIndex _) (RightIndex _) = LT
  compare (RightIndex _) (LeftIndex _) = GT

ltePartialIndex : PartialIndex a b -> LTE b a
ltePartialIndex EmptyIndex = LTERefl
ltePartialIndex (LeftIndex i) = LTFst $ ltePartialIndex i
ltePartialIndex (RightIndex i) = LTSnd $ ltePartialIndex i
ltePartialIndex (VectIndex _ i) = LTVect $ ltePartialIndex i
ltePartialIndex (NewEncIndex i) = LTNewEnc $ ltePartialIndex i

export
partialFromIndex : {a : Encodable} -> IndexType a -> PartialIndex a Bit
partialFromIndex {a = Bit}         ()        = EmptyIndex
partialFromIndex {a = a && _}      (Left  i) = LeftIndex   $ partialFromIndex i
partialFromIndex {a = _ && a}      (Right i) = RightIndex  $ partialFromIndex i
partialFromIndex {a = EncVect _ a} (k, i)    = VectIndex k $ partialFromIndex i
partialFromIndex {a = NewEnc _ a}  i         = NewEncIndex $ partialFromIndex i

export
indexFromPartial : PartialIndex a Bit -> IndexType a
indexFromPartial EmptyIndex = ()
indexFromPartial (LeftIndex i) = Left $ indexFromPartial i
indexFromPartial (RightIndex i) = Right $ indexFromPartial i
indexFromPartial (VectIndex k i) = (k, indexFromPartial i)
indexFromPartial (NewEncIndex i) = indexFromPartial i

compose : PartialIndex a b -> PartialIndex b c -> PartialIndex a c
compose EmptyIndex i = i
compose (LeftIndex i1) i2 = LeftIndex $ compose i1 i2
compose (RightIndex i1) i2 = RightIndex $ compose i1 i2
compose (VectIndex k i1) i2 = VectIndex k $ compose i1 i2
compose (NewEncIndex i1) i2 = NewEncIndex (compose i1 i2)

mutual
  export
  Uninhabited (PartialIndex a (a && _)) where
    uninhabited i = absurd $ ltePartialIndex i
  
  export
  Uninhabited (PartialIndex a (_ && a)) where
    uninhabited i = absurd $ ltePartialIndex i
  
  export
  Uninhabited (PartialIndex a (EncVect _ a)) where
    uninhabited i = absurd $ ltePartialIndex i
  
  export
  Uninhabited (PartialIndex a (NewEnc _ a)) where
    uninhabited i = absurd $ ltePartialIndex i

leftmostIndex : {a : Encodable} -> Nat -> (b : Encodable ** PartialIndex a b)
leftmostIndex {a} Z = (a ** EmptyIndex)
leftmostIndex {a = Bit} (S _) = (Bit ** EmptyIndex)
leftmostIndex {a = _ && _} (S n) = second LeftIndex $ leftmostIndex n
leftmostIndex {a = EncVect Z a} (S _) = (EncVect Z a ** EmptyIndex)
leftmostIndex {a = EncVect (S _) _} (S n) = second (VectIndex 0) $ leftmostIndex n
leftmostIndex {a = NewEnc _ b} (S n) = second NewEncIndex $ leftmostIndex $ S n

rightmostIndex : {a : Encodable} -> Nat -> (b : Encodable ** PartialIndex a b)
rightmostIndex {a} Z = (a ** EmptyIndex)
rightmostIndex {a = Bit} (S _) = (Bit ** EmptyIndex)
rightmostIndex {a = _ && _} (S n) = second RightIndex $ rightmostIndex n
rightmostIndex {a = EncVect Z a} (S _) = (EncVect Z a ** EmptyIndex)
rightmostIndex {a = EncVect (S _) _} (S n) = second (VectIndex last) $ rightmostIndex n
rightmostIndex {a = NewEnc _ a} (S n) = second NewEncIndex $ rightmostIndex $ S n

moveUp' : {a : Encodable} -> PartialIndex a b -> Maybe (c : Encodable ** PartialIndex a c)
moveUp' EmptyIndex = Nothing
moveUp' {a = a1 && a2} (LeftIndex i) =
  maybe (Just (a1 && a2 ** EmptyIndex)) (Just . second LeftIndex) $ moveUp' i
moveUp' {a = a1 && a2 && a3} (RightIndex i) =
  case moveUp' i of
       Nothing => Just (a1 && a2 && a3 ** EmptyIndex)
       Just (c ** i') => if (a2 && a3) == c
                            then Just (a1 && a2 && a3 ** EmptyIndex)
                            else Just (c ** RightIndex i')
moveUp' {a = a1 && a2} (RightIndex i) =
  maybe (Just (a1 && a2 ** EmptyIndex)) (Just . second RightIndex) $ moveUp' i
moveUp' {a = EncVect n a} (VectIndex k i) =
  maybe (Just (EncVect n a ** EmptyIndex)) (Just . second (VectIndex k)) $ moveUp' i
moveUp' {a = NewEnc ident a} (NewEncIndex i) =
  case moveUp' i of
       Nothing => Just (NewEnc ident a ** EmptyIndex)
       Just (c ** i') => if a == c
                            then Just (NewEnc ident a ** EmptyIndex)
                            else Just (c ** NewEncIndex i')

export
moveUp : {a : Encodable} -> {b : Encodable} -> PartialIndex a b -> (c : Encodable ** PartialIndex a c)
moveUp i = fromMaybe (b ** i) $ moveUp' i

export
moveDown : {b : Encodable} -> PartialIndex a b -> (c : Encodable ** PartialIndex a c)
moveDown i = second (compose i) $ leftmostIndex 1

moveLeft' : {a : Encodable} -> PartialIndex a b -> Either Nat (c : Encodable ** PartialIndex a c)
moveLeft' EmptyIndex = Left Z
moveLeft' (LeftIndex i) =
  either (Left . S) (Right . second LeftIndex) $ moveLeft' i
moveLeft' (RightIndex (LeftIndex i)) =
  either (Right . second LeftIndex . rightmostIndex) (Right . second (RightIndex . LeftIndex)) $ moveLeft' i
moveLeft' (RightIndex (RightIndex i)) =
  either (Right . second (RightIndex . LeftIndex) . rightmostIndex) (Right . second (RightIndex . RightIndex)) $ moveLeft' i
moveLeft' (RightIndex i) =
  either (Right . second LeftIndex . rightmostIndex) (Right . second RightIndex) $ moveLeft' i
moveLeft' (VectIndex FZ i) =
  either (Left . S) (Right . second (VectIndex FZ)) $ moveLeft' i
moveLeft' (VectIndex (FS k) i) =
  either (Right . second (VectIndex $ weaken k) . rightmostIndex) (Right . second (VectIndex $ FS k)) $ moveLeft' i
moveLeft' (NewEncIndex i) =
  either Left (Right . second NewEncIndex) $ moveLeft' i

export
moveLeft : {a : Encodable} -> {b : Encodable} -> PartialIndex a b -> (c : Encodable ** PartialIndex a c)
moveLeft i = either (\_ => (b ** i)) id $ moveLeft' i

moveRight' : {a : Encodable} -> PartialIndex a b -> Either Nat (c : Encodable ** PartialIndex a c)
moveRight' EmptyIndex = Left Z
moveRight' {a = a1 && a && _} (LeftIndex i) =
  either (Right . second RightIndex . leftmostIndex . S) (Right . second LeftIndex) $ moveRight' i
moveRight' {a = a1 && a} (LeftIndex i) =
  either (Right . second RightIndex . leftmostIndex) (Right . second LeftIndex) $ moveRight' i
moveRight' (RightIndex i) =
  either (Left . S) (Right . second RightIndex) $ moveRight' i
moveRight' {a = EncVect (S _) a} (VectIndex k i) =
  case strengthen k of
       Left _ => either (Left . S) (Right . second (VectIndex k)) $ moveRight' i
       Right k' => either (Right . second (VectIndex $ FS k') . rightmostIndex) (Right . second (VectIndex k)) $ moveRight' i
moveRight' (NewEncIndex i) =
  either Left (Right . second NewEncIndex) $ moveRight' i

export
moveRight : {a : Encodable} -> {b : Encodable} -> PartialIndex a b -> (c : Encodable ** PartialIndex a c)
moveRight i = either (\_ => (b ** i)) id $ moveRight' i

export
collatePair : PartialIndex a b -> PartialIndex a c -> Maybe (PartialIndex a (b && c))
collatePair EmptyIndex _ = Nothing
collatePair _ EmptyIndex = Nothing
collatePair (LeftIndex i1) (LeftIndex i2) = LeftIndex <$> collatePair i1 i2
collatePair (LeftIndex EmptyIndex) (RightIndex EmptyIndex) = Just EmptyIndex
collatePair (LeftIndex _) (RightIndex _) = Nothing
collatePair (RightIndex _) (LeftIndex _) = Nothing
collatePair (RightIndex i1) (RightIndex i2) = RightIndex <$> collatePair i1 i2
collatePair (VectIndex k1 i1) (VectIndex k2 i2) with (decEq k1 k2)
  collatePair (VectIndex k i1) (VectIndex k i2) | Yes Refl = VectIndex k <$> collatePair i1 i2
  collatePair (VectIndex k1 i1) (VectIndex k2 i2) | No _ = Nothing
collatePair (NewEncIndex i1) (NewEncIndex i2) = NewEncIndex <$> collatePair i1 i2

extractLeft : PartialIndex (a && _) b -> Maybe (PartialIndex a b)
extractLeft EmptyIndex = Nothing
extractLeft (LeftIndex i) = Just i
extractLeft (RightIndex _) = Nothing

extractRight : PartialIndex (_ && a) b -> Maybe (PartialIndex a b)
extractRight EmptyIndex = Nothing
extractRight (LeftIndex _) = Nothing
extractRight (RightIndex i) = Just i

extractVect : PartialIndex (EncVect n a) b -> Maybe (Fin n, PartialIndex a b)
extractVect EmptyIndex = Nothing
extractVect (VectIndex k i) = Just (k, i)

extractNewEnc : PartialIndex (NewEnc _ a) b -> Maybe (PartialIndex a b)
extractNewEnc EmptyIndex = Nothing
extractNewEnc (NewEncIndex i) = Just i

export
collateVect : {n : Nat} -> {a : Encodable} -> Vect n (PartialIndex a b) -> Maybe (PartialIndex a (EncVect n b))
collateVect [] = Nothing
collateVect (EmptyIndex :: _) = Nothing
collateVect is@(LeftIndex _ :: _) = LeftIndex <$> (traverse extractLeft is >>= collateVect)
collateVect is@(RightIndex _ :: _) = RightIndex <$> (traverse extractRight is >>= collateVect)
collateVect {n = S n} {a = EncVect m a} is@(VectIndex _ i :: _) =
  case (i, decEq m (S n)) of
       (EmptyIndex, Yes Refl) => if traverse (map fst . extractVect) is == Just range
                                    then Just EmptyIndex
                                    else case nub <$> toList <$> traverse (map fst . extractVect) is of
                                              Just [k] => VectIndex k <$> (traverse (map snd . extractVect) is >>= (\xs => assert_total $ collateVect xs))
                                              _ => Nothing
       _ => case nub <$> toList <$> traverse (map fst . extractVect) is of
                 Just [k] => VectIndex k <$> (traverse (map snd . extractVect) is >>= (\xs => assert_total $ collateVect xs))
                 _ => Nothing
collateVect is@(NewEncIndex _ :: _) = NewEncIndex <$> (traverse extractNewEnc is >>= collateVect)

export
collateNewEnc : {ident : String} -> {a : Encodable} -> PartialIndex a b -> Maybe (PartialIndex a (NewEnc ident b))
collateNewEnc EmptyIndex = Nothing
collateNewEnc (LeftIndex i) = LeftIndex <$> collateNewEnc i
collateNewEnc (RightIndex i) = RightIndex <$> collateNewEnc i
collateNewEnc (VectIndex k i) = VectIndex k <$> collateNewEnc i
collateNewEnc {a = NewEnc ident' _} (NewEncIndex EmptyIndex) with (decEq ident ident')
  collateNewEnc {a = NewEnc ident _} (NewEncIndex EmptyIndex) | Yes Refl = Just EmptyIndex
  collateNewEnc (NewEncIndex EmptyIndex) | No _ = Nothing
collateNewEnc (NewEncIndex i) = NewEncIndex <$> collateNewEnc i

