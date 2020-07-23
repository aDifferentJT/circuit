module IndexType

import AuxProofs
import Data.DPair.Extra
import Data.Hash
import Data.List
import Data.SortedSet
import Data.Strings
import Data.Vect
import Debug.Trace
import Decidable.Equality
import Encodable
import EqOrdUtils
import Utils

%default total

public export
data PartialIndex : Encodable -> Encodable -> Type where
  EmptyIndex : PartialIndex a a
  LeftIndex : PartialIndex a b -> PartialIndex (a && _) b
  RightIndex : PartialIndex a b -> PartialIndex (_ && a) b
  HeadIndex : PartialIndex a b -> PartialIndex (EncVect (S n) a) b
  TailIndex : PartialIndex (EncVect n a) b -> PartialIndex (EncVect (S n) a) b
  NewEncIndex : PartialIndex a b -> PartialIndex (NewEnc _ a) b

export
Eq (PartialIndex a b) where
  EmptyIndex       == EmptyIndex       = True
  (LeftIndex i1)   == (LeftIndex i2)   = i1 == i2
  (RightIndex i1)  == (RightIndex i2)  = i1 == i2
  (HeadIndex i1)   == (HeadIndex i2)   = i1 == i2
  (TailIndex i1)   == (TailIndex i2)   = i1 == i2
  (NewEncIndex i1) == (NewEncIndex i2) = i1 == i2
  _ == _ = False

export
Ord (PartialIndex a b) where
  compare EmptyIndex EmptyIndex = EQ
  compare (LeftIndex i1)   (LeftIndex i2)   = compare i1 i2
  compare (RightIndex i1)  (RightIndex i2)  = compare i1 i2
  compare (HeadIndex i1)   (HeadIndex i2)   = compare i1 i2
  compare (TailIndex i1)   (TailIndex i2)   = compare i1 i2
  compare (NewEncIndex i1) (NewEncIndex i2) = compare i1 i2

  compare EmptyIndex (LeftIndex _)   = LT
  compare EmptyIndex (RightIndex _)  = LT
  compare EmptyIndex (HeadIndex _)   = LT
  compare EmptyIndex (TailIndex _)   = LT
  compare EmptyIndex (NewEncIndex _) = LT
  compare (LeftIndex _)   EmptyIndex = GT
  compare (RightIndex _)  EmptyIndex = GT
  compare (HeadIndex _)   EmptyIndex = GT
  compare (TailIndex _)   EmptyIndex = GT
  compare (NewEncIndex _) EmptyIndex = GT
  
  compare (LeftIndex _) (RightIndex _) = LT
  compare (RightIndex _) (LeftIndex _) = GT

  compare (HeadIndex _) (TailIndex _) = LT
  compare (TailIndex _) (HeadIndex _) = GT

show' : {a : Encodable} -> PartialIndex a b -> List String
show' EmptyIndex = []
show' (LeftIndex   i) = "Left" :: show' i
show' (RightIndex  i) = "Right" :: show' i
show' (HeadIndex   i) = "Head" :: show' i
show' (TailIndex   i) = "Tail" :: show' i
show' {a = NewEnc ident _} (NewEncIndex i) = ident :: show' i

export
{a : Encodable} -> Show (PartialIndex a b) where
  show = unwords . show'

export
showIdent : {a : Encodable} -> PartialIndex a b -> String
showIdent = concat . intersperse "_" . show'

export
Hashable (PartialIndex a b) where
  hash EmptyIndex = hash ()
  hash (LeftIndex i)   = addSalt 0 $ hash i
  hash (RightIndex i)  = addSalt 1 $ hash i
  hash (HeadIndex i)   = addSalt 2 $ hash i
  hash (TailIndex i)   = assert_total $ addSalt 3 $ hash i
  hash (NewEncIndex i) = addSalt 4 $ hash i

compose : PartialIndex a b -> PartialIndex b c -> PartialIndex a c
compose EmptyIndex i = i
compose (LeftIndex   i1) i2 = LeftIndex   $ compose i1 i2
compose (RightIndex  i1) i2 = RightIndex  $ compose i1 i2
compose (HeadIndex   i1) i2 = HeadIndex   $ compose i1 i2
compose (TailIndex   i1) i2 = TailIndex   $ compose i1 i2
compose (NewEncIndex i1) i2 = NewEncIndex $ compose i1 i2

mutual
  export
  Uninhabited (PartialIndex a (a && _)) where
    uninhabited EmptyIndex impossible
    uninhabited (LeftIndex   i) = absurd $ compose i $ LeftIndex EmptyIndex
    uninhabited (RightIndex  i) = absurd $ compose i $ LeftIndex EmptyIndex
    uninhabited (HeadIndex   i) = absurd $ compose i $ LeftIndex EmptyIndex
    uninhabited (TailIndex   i) = absurd $ compose i $ LeftIndex EmptyIndex
    uninhabited (NewEncIndex i) = absurd $ compose i $ LeftIndex EmptyIndex
  
  export
  Uninhabited (PartialIndex a (_ && a)) where
    uninhabited EmptyIndex impossible
    uninhabited (LeftIndex   i) = absurd $ compose i $ RightIndex EmptyIndex
    uninhabited (RightIndex  i) = absurd $ compose i $ RightIndex EmptyIndex
    uninhabited (HeadIndex   i) = absurd $ compose i $ RightIndex EmptyIndex
    uninhabited (TailIndex   i) = absurd $ compose i $ RightIndex EmptyIndex
    uninhabited (NewEncIndex i) = absurd $ compose i $ RightIndex EmptyIndex
  
  export
  Uninhabited (PartialIndex a (EncVect (S _) a)) where
    uninhabited EmptyIndex impossible
    uninhabited (LeftIndex   i) = absurd $ compose i $ HeadIndex EmptyIndex
    uninhabited (RightIndex  i) = absurd $ compose i $ HeadIndex EmptyIndex
    uninhabited (HeadIndex   i) = absurd $ compose i $ HeadIndex EmptyIndex
    uninhabited (TailIndex   i) = absurd $ compose i $ HeadIndex EmptyIndex
    uninhabited (NewEncIndex i) = absurd $ compose i $ HeadIndex EmptyIndex
  
  export
  Uninhabited (PartialIndex (EncVect n a) (EncVect (S n) a)) where
    uninhabited EmptyIndex impossible
    uninhabited (HeadIndex i) = absurd $ compose i $ TailIndex EmptyIndex
    uninhabited (TailIndex i) = absurd $ compose i $ TailIndex EmptyIndex
  
  export
  Uninhabited (PartialIndex a (NewEnc _ a)) where
    uninhabited EmptyIndex impossible
    uninhabited (LeftIndex   i) = absurd $ compose i $ NewEncIndex EmptyIndex
    uninhabited (RightIndex  i) = absurd $ compose i $ NewEncIndex EmptyIndex
    uninhabited (HeadIndex   i) = absurd $ compose i $ NewEncIndex EmptyIndex
    uninhabited (TailIndex   i) = absurd $ compose i $ NewEncIndex EmptyIndex
    uninhabited (NewEncIndex i) = absurd $ compose i $ NewEncIndex EmptyIndex

leftmostIndex : {a : Encodable} -> Nat -> (b : Encodable ** PartialIndex a b)
leftmostIndex {a} Z = (a ** EmptyIndex)
leftmostIndex {a = Bit} (S _) = trace "Forced Up" (Bit ** EmptyIndex)
leftmostIndex {a = UnitEnc} (S _) = trace "Forced Up" (UnitEnc ** EmptyIndex)
leftmostIndex {a = _ && _} (S n) = second LeftIndex $ leftmostIndex n
leftmostIndex {a = EncVect Z a} (S _) = (EncVect Z a ** EmptyIndex)
leftmostIndex {a = EncVect (S _) _} (S n) = second HeadIndex $ leftmostIndex n
leftmostIndex {a = NewEnc _ b} (S n) = second NewEncIndex $ leftmostIndex $ S n

rightmostIndex : {a : Encodable} -> Nat -> (b : Encodable ** PartialIndex a b)
rightmostIndex {a} Z = (a ** EmptyIndex)
rightmostIndex {a = Bit} (S _) = trace "Forced Up" (Bit ** EmptyIndex)
rightmostIndex {a = UnitEnc} (S _) = trace "Forced Up" (UnitEnc ** EmptyIndex)
rightmostIndex {a = _ && UnitEnc} (S n) = second LeftIndex $ rightmostIndex n
rightmostIndex {a = _ && _} (S n) = second RightIndex $ rightmostIndex n
rightmostIndex {a = EncVect 0 a} (S _) = (EncVect Z a ** EmptyIndex)
rightmostIndex {a = EncVect 1 a} (S n) = second HeadIndex $ rightmostIndex n
rightmostIndex {a = EncVect (S m) a} (S n) = second TailIndex $ rightmostIndex {a = assert_smaller (EncVect (S m) a) $ EncVect m a} $ S n
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
moveUp' {a = EncVect (S n) a} (HeadIndex i) =
  maybe (Just (EncVect (S n) a ** EmptyIndex)) (Just . second HeadIndex) $ moveUp' i
moveUp' {a = EncVect 1 a} (TailIndex i) =
  maybe (Just (EncVect 1 a ** EmptyIndex)) (Just . second TailIndex) $ moveUp' i
moveUp' {a = EncVect (S (S n)) a} (TailIndex i) =
  case moveUp' i of
       Nothing => Just (EncVect (S (S n)) a ** EmptyIndex)
       Just (c ** i') => if EncVect (S n) a == c
                            then Just (EncVect (S (S n)) a ** EmptyIndex)
                            else Just (c ** TailIndex i')
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
moveLeft' {a = _ && a2} (LeftIndex i) =
    either (map (second RightIndex) . onFail a2) (Right . second LeftIndex) $ moveLeft' i
  where
    onFail : (d : Encodable) -> Nat -> Either Nat (c : Encodable ** PartialIndex d c)
    onFail UnitEnc = Left
    onFail _       = Left . S
moveLeft' (RightIndex (LeftIndex i)) =
  either (Right . second LeftIndex . rightmostIndex) (Right . second (RightIndex . LeftIndex)) $ moveLeft' i
moveLeft' (RightIndex (RightIndex i)) =
  either (Right . second (RightIndex . LeftIndex) . rightmostIndex) (Right . second (RightIndex . RightIndex)) $ moveLeft' i
moveLeft' (RightIndex i) =
  either (Right . second LeftIndex . rightmostIndex) (Right . second RightIndex) $ moveLeft' i
moveLeft' (HeadIndex i) =
  either (Left . S) (Right . second HeadIndex) $ moveLeft' i
moveLeft' (TailIndex (HeadIndex i)) =
  either (Right . second HeadIndex . rightmostIndex) (Right . second (TailIndex . HeadIndex)) $ moveLeft' i
moveLeft' (TailIndex i) =
  either (Right . second HeadIndex . rightmostIndex) (Right . second TailIndex) $ moveLeft' i
moveLeft' (NewEncIndex i) =
  either Left (Right . second NewEncIndex) $ moveLeft' i

export
moveLeft : {a : Encodable} -> {b : Encodable} -> PartialIndex a b -> (c : Encodable ** PartialIndex a c)
moveLeft i = either (\_ => (b ** i)) id $ moveLeft' i

moveRight' : {a : Encodable} -> PartialIndex a b -> Either Nat (c : Encodable ** PartialIndex a c)
moveRight' EmptyIndex = Left Z
moveRight' {a = _ && a2} (LeftIndex i) =
    either (map (second RightIndex) . onFail a2) (Right . second LeftIndex) $ moveRight' i
  where
    onFail : (d : Encodable) -> Nat -> Either Nat (c : Encodable ** PartialIndex d c)
    onFail UnitEnc  = Left
    onFail (_ && _) = Right . leftmostIndex . S
    onFail _        = Right . leftmostIndex
moveRight' (RightIndex i) =
  either (Left . S) (Right . second RightIndex) $ moveRight' i
moveRight' {a = EncVect 1 _} (HeadIndex i) =
  either (Left . S) (Right . second HeadIndex) $ moveRight' i
moveRight' {a = EncVect (S (S _)) _} (HeadIndex i) =
  either (Right . second TailIndex . leftmostIndex . S) (Right . second HeadIndex) $ moveRight' i
moveRight' {a = EncVect _ a'} (TailIndex i) =
  second TailIndex <$> moveRight' i
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
collatePair (HeadIndex i1) (HeadIndex i2) = HeadIndex <$> collatePair i1 i2
collatePair (TailIndex i1) (TailIndex i2) = TailIndex <$> collatePair i1 i2
collatePair (HeadIndex _) (TailIndex _) = Nothing
collatePair (TailIndex _) (HeadIndex _) = Nothing
collatePair (NewEncIndex i1) (NewEncIndex i2) = NewEncIndex <$> collatePair i1 i2

export
collateVect : PartialIndex a b -> PartialIndex a (EncVect n b) -> Maybe (PartialIndex a (EncVect (S n) b))
collateVect EmptyIndex _ = Nothing
collateVect _ EmptyIndex = Nothing
collateVect (LeftIndex i1) (LeftIndex i2) = LeftIndex <$> collateVect i1 i2
collateVect (LeftIndex _) (RightIndex _) = Nothing
collateVect (RightIndex _) (LeftIndex _) = Nothing
collateVect (RightIndex i1) (RightIndex i2) = RightIndex <$> collateVect i1 i2
collateVect (HeadIndex i1) (HeadIndex i2) = HeadIndex <$> collateVect i1 i2
collateVect (HeadIndex EmptyIndex) (TailIndex EmptyIndex) = Just EmptyIndex
collateVect (HeadIndex _) (TailIndex _) = Nothing
collateVect (TailIndex _) (HeadIndex _) = Nothing
collateVect (TailIndex i1) (TailIndex i2) = TailIndex <$> collateVect i1 i2
collateVect (NewEncIndex i1) (NewEncIndex i2) = NewEncIndex <$> collateVect i1 i2

export
collateNewEnc : {ident : String} -> {a : Encodable} -> PartialIndex a b -> Maybe (PartialIndex a (NewEnc ident b))
collateNewEnc EmptyIndex = Nothing
collateNewEnc (LeftIndex  i) = LeftIndex  <$> collateNewEnc i
collateNewEnc (RightIndex i) = RightIndex <$> collateNewEnc i
collateNewEnc (HeadIndex  i) = HeadIndex  <$> collateNewEnc i
collateNewEnc (TailIndex  i) = TailIndex  <$> collateNewEnc i
collateNewEnc {a = NewEnc ident' _} (NewEncIndex EmptyIndex) with (decEq ident ident')
  collateNewEnc {a = NewEnc ident _} (NewEncIndex EmptyIndex) | Yes Refl = Just EmptyIndex
  collateNewEnc (NewEncIndex EmptyIndex) | No _ = Nothing
collateNewEnc (NewEncIndex i) = NewEncIndex <$> collateNewEnc i

public export
IndexType : Encodable -> Type
IndexType a = PartialIndex a Bit

