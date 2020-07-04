module PartialIndex

import AuxProofs
import Data.DPair.Extra
import Data.SortedSet
import Encodable
import EqOrdUtils
import IndexType
import Utils
import WithBitType

%default total

public export
PartialIndex : Encodable -> Encodable -> Type
PartialIndex a b with (decEq a b)
  PartialIndex _ _ | Yes Refl = ()
  PartialIndex Bit _ | No _ = Void
  PartialIndex (a1 & a2) b | No _ = Either (PartialIndex a1 b) (PartialIndex a2 b)
  PartialIndex (EncVect n a) b | No _ = (Fin n, PartialIndex a b)
  PartialIndex (NewEnc i a) b | No _ = PartialIndex a b

export
partialIndex
  :  {a : Encodable}
  -> {b : Encodable}
  -> PartialIndex a b
  -> WithBitType t a
  -> WithBitType t b
partialIndex {a} {b} i x with (decEq a b)
  partialIndex () x | Yes Refl = x
  partialIndex {a = Bit} _ _ | No _ impossible
  partialIndex {a = a & _} {b} (Left i)  (x, _) | No _ = partialIndex {a} {b} i x
  partialIndex {a = _ & a} {b} (Right i) (_, x) | No _ = partialIndex {a} {b} i x
  partialIndex {a = EncVect _ a} {b} (i, is) x | No _ = partialIndex {a} {b} is $ index i x
  partialIndex {a = NewEnc _ a} {b} i (MkNewType x) | No _ = partialIndex {a} {b} i x

export
OrdPartialIndex : (a : Encodable) -> (b : Encodable) -> Ord (PartialIndex a b)
OrdPartialIndex a b with (decEq a b)
  OrdPartialIndex a a | Yes Refl = %implementation
  OrdPartialIndex Bit _ | No _ = OrdVoid
  OrdPartialIndex (a1 & a2) b | No  _ = OrdEither @{OrdPartialIndex a1 b} @{OrdPartialIndex a2 b}
  OrdPartialIndex (EncVect n a) b | No  _ = OrdPair @{%implementation} @{OrdPartialIndex a b}
  OrdPartialIndex (NewEnc i a) b | No  _ = OrdPartialIndex a b

export
EqPartialIndex : (a : Encodable) -> (b : Encodable) -> Eq (PartialIndex a b)
EqPartialIndex a b with (OrdPartialIndex a b)
  | _ = autoDer

export
rewritePartialIndex : (a = a') -> (b = b') -> PartialIndex a b = PartialIndex a' b'
rewritePartialIndex Refl Refl = Refl

ltePartialIndex : PartialIndex a b -> LTE b a
ltePartialIndex {a} {b} i with (decEq a b)
  ltePartialIndex () | Yes Refl = LTERefl
  ltePartialIndex {a = _ & _} (Left i)  | No _ = LTFst $ ltePartialIndex i
  ltePartialIndex {a = _ & _} (Right i) | No _ = LTSnd $ ltePartialIndex i
  ltePartialIndex {a = EncVect _ _} (_, i) | No _ = LTVect $ ltePartialIndex i
  ltePartialIndex {a = NewEnc _ _} i | No _ = LTNewEnc $ ltePartialIndex i

export implicit
emptyIndex : {a : Encodable} -> PartialIndex a a
emptyIndex {a} with (decEq a a)
  | Yes Refl = ()
  | No f = absurd $ f Refl

export
partialFromIndex : IndexType a -> PartialIndex a Bit
partialFromIndex {a} i with (decEq a Bit)
  partialFromIndex {a = Bit} () | Yes Refl = ()
  partialFromIndex {a = _ & _} () | Yes Refl impossible
  partialFromIndex {a = EncVect _ _} () | Yes Refl impossible
  partialFromIndex {a = NewEnc _ _} () | Yes Refl impossible
  partialFromIndex {a = Bit} _ | No f = absurd $ f Refl
  partialFromIndex {a = a & _} (Left i) | No _ = Left  $ partialFromIndex {a} i
  partialFromIndex {a = _ & a} (Right i) | No _ = Right $ partialFromIndex {a} i
  partialFromIndex {a = EncVect _ a} (i, is) | No _ = (i, partialFromIndex {a} is)
  partialFromIndex {a = NewEnc _ a} i | No _ = partialFromIndex {a} i

export
indexFromPartial : PartialIndex a Bit -> IndexType a
indexFromPartial {a} i with (decEq a Bit)
  indexFromPartial {a = Bit} () | Yes Refl = ()
  indexFromPartial {a = _ & _} () | Yes Refl impossible
  indexFromPartial {a = EncVect _ _} () | Yes Refl impossible
  indexFromPartial {a = NewEnc _ _} () | Yes Refl impossible
  indexFromPartial {a = Bit} _ | No f = absurd $ f Refl
  indexFromPartial {a = a & _} (Left i) | No _ = Left  $ indexFromPartial {a} i
  indexFromPartial {a = _ & a} (Right i) | No _ = Right $ indexFromPartial {a} i
  indexFromPartial {a = EncVect _ a} (i, is) | No _ = (i, indexFromPartial {a} is)
  indexFromPartial {a = NewEnc _ a} i | No _ = indexFromPartial {a} i

composeIndices : PartialIndex a b -> PartialIndex b c -> PartialIndex a c
composeIndices {a} {b} {c} iAB iBC with (decEq a b)
  composeIndices () iBC | Yes Refl = iBC
  composeIndices {a = Bit} _ _ | No _ impossible
  composeIndices {a} {b} {c} iAB iBC | No _ with (decEq a c)
    composeIndices _ _ | No _ | Yes Refl = ()
    composeIndices {a = a & _} {b} {c} (Left iAB) iBC | No _ | No _ = Left $ composeIndices {a} {b} {c} iAB iBC
    composeIndices {a = _ & a} {b} {c} (Right iAB) iBC | No _ | No _ = Right $ composeIndices {a} {b} {c} iAB iBC
    composeIndices {a = EncVect _ a} {b} {c} (iAB, isAB) iBC | No _ | No _ = (iAB, composeIndices {a} {b} {c} isAB iBC)
    composeIndices {a = NewEnc _ a} {b} {c} iAB iBC | No _ | No _ = composeIndices {a} {b} {c} iAB iBC

export
[IndexNotLeft] Uninhabited (PartialIndex a (a & b)) where
  uninhabited {a} {b} = absurd {t = LTE (a & b) a} . ltePartialIndex

export
[IndexNotRight] Uninhabited (PartialIndex b (a & b)) where
  uninhabited {a} {b} = absurd {t = LTE (a & b) b} . ltePartialIndex

export
[IndexNotVect] Uninhabited (PartialIndex a (EncVect n a)) where
  uninhabited {n} {a} = absurd {t = LTE (EncVect n a) a} . ltePartialIndex

export
[IndexNotNewEnc] Uninhabited (PartialIndex a (NewEnc ident a)) where
  uninhabited {ident} {a} = absurd {t = LTE (NewEnc ident a) a} . ltePartialIndex

export
leftIndex : {a1 : Encodable} -> {a2 : Encodable} -> {b : Encodable} -> PartialIndex a1 b -> PartialIndex (a1 & a2) b
leftIndex {a1} {a2} {b} i with (decEq (a1 & a2) b)
  leftIndex {a1} {a2} {b = a1 & a2} i | Yes Refl = absurd @{IndexNotLeft} i
  leftIndex i | No _ = Left i

export
rightIndex : {a1 : Encodable} -> {a2 : Encodable} -> {b : Encodable} -> PartialIndex a2 b -> PartialIndex (a1 & a2) b
rightIndex {a1} {a2} {b} i with (decEq (a1 & a2) b)
  rightIndex {a1} {a2} {b = a1 & a2} i | Yes Refl = absurd @{IndexNotRight} i
  rightIndex i | No _ = Right i

export
vectElemIndex : {n : Nat} -> {a : Encodable} -> {b : Encodable} -> Fin n -> PartialIndex a b -> PartialIndex (EncVect n a) b
vectElemIndex {n} {a} {b} k i with (decEq (EncVect n a) b)
  vectElemIndex {n} {a} {b = EncVect n a} _ i | Yes Refl = absurd @{IndexNotVect} i
  vectElemIndex k i | No _ = (k, i)

export
newEncIndex : {ident : String} -> {a : Encodable} -> {b : Encodable} -> PartialIndex a b -> PartialIndex (NewEnc ident a) b
newEncIndex {ident} {a} {b} i with (decEq (NewEnc ident a) b)
  newEncIndex {ident} {a} {b = NewEnc ident a} i | Yes Refl = absurd @{IndexNotNewEnc} i
  newEncIndex i | No _ = i

indexSelfLeft : PartialIndex (a1 & a2) a1 -> Either () (PartialIndex a2 a1)
indexSelfLeft {a1} {a2} i with (decEq (a1 & a2) a1)
  indexSelfLeft _ | Yes Refl impossible
  indexSelfLeft (Left i) | No _ = Left ()
  indexSelfLeft (Right i) | No _ = Right i

leftmostIndex : Nat -> (b : Encodable ** PartialIndex a b)
leftmostIndex {a} Z = (a ** emptyIndex)
leftmostIndex {a = Bit} (S _) = (Bit ** emptyIndex)
leftmostIndex {a = _ & _} (S n) = second leftIndex $ leftmostIndex n
leftmostIndex {a = EncVect Z a} (S _) = (EncVect Z a ** emptyIndex)
leftmostIndex {a = EncVect (S _) _} (S n) = second (vectElemIndex 0) $ leftmostIndex n
leftmostIndex {a = NewEnc _ b} (S n) = second newEncIndex $ leftmostIndex $ S n

rightmostIndex : Nat -> (b : Encodable ** PartialIndex a b)
rightmostIndex {a} Z = (a ** emptyIndex)
rightmostIndex {a = Bit} (S _) = (Bit ** emptyIndex)
rightmostIndex {a = _ & _} (S n) = second rightIndex $ rightmostIndex n
rightmostIndex {a = EncVect Z a} (S _) = (EncVect Z a ** emptyIndex)
rightmostIndex {a = EncVect (S _) _} (S n) = second (vectElemIndex last) $ rightmostIndex n
rightmostIndex {a = NewEnc _ a} (S n) = second newEncIndex $ rightmostIndex $ S n

export
moveUp' : PartialIndex a b -> Maybe (c : Encodable ** PartialIndex a c)
moveUp' {a = Bit} {b} i with (decEq Bit b)
  moveUp' {a = Bit} {b = Bit} () | Yes Refl = Nothing
  moveUp' _ | No _ impossible
moveUp' {a = a1 & a2} {b} i with (decEq (a1 & a2) b)
  moveUp' {a = a1 & a2} {b = a1 & a2} () | Yes Refl = Nothing
  moveUp' {b = Bit} () | Yes Refl impossible
  moveUp' {b = EncVect _ _} () | Yes Refl impossible
  moveUp' {b = NewEnc _ _} () | Yes Refl impossible
  moveUp' {a = a1 & a2} {b} (Left i) | No _ with (moveUp' {a = a1} {b} i)
    | Nothing = Just (a1 & a2 ** emptyIndex)
    | Just (c ** i') = Just (c ** leftIndex i')
  moveUp' {a = a1 & a2 & a3} {b} (Right i) | No _ with (moveUp' {a = a2 & a3} {b} i)
    | Nothing = Just (a1 & a2 & a3 ** emptyIndex)
    | Just (c ** i') =
      if a2 & a3 == c
         then Just (a1 & a2 & a3 ** emptyIndex)
         else Just (c ** rightIndex i')
  moveUp' {a = a1 & a2} {b} (Right i) | No _ with (moveUp' {a = a2} {b} i)
    | Nothing = Just (a1 & a2 ** emptyIndex)
    | Just (c ** i') = Just (c ** rightIndex i')
moveUp' {a = EncVect n a} {b} i with (decEq (EncVect n a) b)
  moveUp' {a = EncVect n a} {b = EncVect n a} () | Yes Refl = Nothing
  moveUp' {b = Bit} () | Yes Refl impossible
  moveUp' {b = _ & _} () | Yes Refl impossible
  moveUp' {b = NewEnc _ _} () | Yes Refl impossible
  moveUp' {a = EncVect n a} {b} (k, i) | No _ =
    maybe (Just (EncVect n a ** emptyIndex)) (Just . second (vectElemIndex k)) $ moveUp' {a} {b} i
moveUp' {a = NewEnc ident a} {b} i with (decEq (NewEnc ident a) b)
  moveUp' {a = NewEnc ident a} {b = NewEnc ident a} () | Yes Refl = Nothing
  moveUp' {b = Bit} () | Yes Refl impossible
  moveUp' {b = _ & _} () | Yes Refl impossible
  moveUp' {b = EncVect _ _} () | Yes Refl impossible
  moveUp' {a = NewEnc ident a} {b} i | No _ with (moveUp' {a} {b} i)
    | Nothing = Just (NewEnc ident a ** emptyIndex)
    | Just (c ** i') =
      if a == c
         then Just (NewEnc ident a ** emptyIndex)
         else Just (c ** newEncIndex i')

export
moveUp : PartialIndex a b -> (c : Encodable ** PartialIndex a c)
moveUp {b} i = fromMaybe (b ** i) $ moveUp' i

export
moveDown : PartialIndex a b -> (c : Encodable ** PartialIndex a c)
moveDown i = second (composeIndices i) $ leftmostIndex 1

moveLeft' : PartialIndex a b -> Either Nat (c : Encodable ** PartialIndex a c)
moveLeft' {a = Bit} _ = Left Z
moveLeft' {a = a1 & a2} {b} i with (decEq (a1 & a2) b)
  moveLeft' () | Yes Refl = Left Z
  moveLeft' {a = a1 & a2} {b} (Left i) | No _ = either (Left . S) (Right . second leftIndex) $ moveLeft' i
  moveLeft' {a = a1 & a2 & a3} {b} (Right i) | No _ with (decEq (a2 & a3) b)
    moveLeft' {a = a & _} _ | No _ | Yes _ =
      Right (a ** leftIndex emptyIndex)
    moveLeft' (Right (Left i)) | No _ | No _ =
      either (Right . second leftIndex . rightmostIndex) (Right . second (rightIndex . leftIndex)) $ moveLeft' i
    moveLeft' {a = _ & a & _} (Right (Right i)) | No _ | No _ =
      either (Right . second (rightIndex . leftIndex) . rightmostIndex {a}) (Right . second (rightIndex . rightIndex)) $ moveLeft' i
  moveLeft' {a = a1 & a2} {b} (Right i) | No _ =
    if a2 == b
       then Right (a1 ** leftIndex emptyIndex)
       else either (Right . second leftIndex . rightmostIndex) (Right . second rightIndex) $ moveLeft' i
moveLeft' {a = EncVect n a} {b} i with (decEq (EncVect n a) b)
  moveLeft' () | Yes Refl = Left Z
  moveLeft' {a = EncVect Z _} (_, _) | No _ impossible
  moveLeft' {a = EncVect (S _) a} {b} (FZ, i) | No _ = either (Left . S) (Right . second (vectElemIndex FZ)) $ moveLeft' i
  moveLeft' {a = EncVect (S _) a} {b} (FS k, i) | No _ =
    if a == b
       then Right (a ** vectElemIndex (weaken k) emptyIndex)
       else either (Right . second (vectElemIndex $ weaken k) . rightmostIndex) (Right . second (vectElemIndex $ FS k)) $ moveLeft' i
moveLeft' {a = NewEnc ident a} {b} i with (decEq (NewEnc ident a) b)
  moveLeft' () | Yes Refl = Left Z
  | No _ = either Left (Right . second newEncIndex) $ moveLeft' i

export
moveLeft : PartialIndex a b -> (c : Encodable ** PartialIndex a c)
moveLeft {b} i = either (\_ => (b ** i)) id $ moveLeft' i

moveRight' : PartialIndex a b -> Either Nat (c : Encodable ** PartialIndex a c)
moveRight' {a = Bit} _ = Left Z
moveRight' {a = a1 & a2} {b} i with (decEq (a1 & a2) b)
  moveRight' () | Yes Refl = Left Z
  moveRight' {a = a1 & a2} {b} (Left i) | No _ with (a1 == b)
    moveRight' {a = _ & a & _} (Left _) | No _ | True = Right (a ** rightIndex $ leftIndex $ emptyIndex)
    moveRight' {a = _ & a}     (Left _) | No _ | True = Right (a ** rightIndex $ emptyIndex)
    | False with (moveRight' i)
      moveRight' {a = _ & a & _} (Left _) | No _ | False | Left k = Right $ second rightIndex $ leftmostIndex $ S k
      moveRight' {a = _ & a}     (Left _) | No _ | False | Left k = Right $ second rightIndex $ leftmostIndex k
      | Right i' = Right $ second leftIndex i'
  moveRight' {a = a1 & a2} {b} (Right i) | No _ = (\(c ** i') => (c ** rightIndex i')) <$> moveRight' i
moveRight' {a = EncVect n a} {b} i with (decEq (EncVect n a) b)
  moveRight' () | Yes Refl = Left Z
  moveRight' {a = EncVect Z _} (_, _) | No _ impossible
  moveRight' {a = EncVect (S _) a} {b} (k, i) | No _ with (strengthen k)
    | Left _ = either (Left . S) (Right . second (vectElemIndex k)) $ moveRight' i
    | Right k' =
      if a == b
         then Right (a ** vectElemIndex (FS k') emptyIndex)
         else either (Right . second (vectElemIndex $ FS k') . rightmostIndex) (Right . second (vectElemIndex $ k)) $ moveRight' i
moveRight' {a = NewEnc ident a} {b} i with (decEq (NewEnc ident a) b)
  moveRight' () | Yes Refl = Left Z
  | No _ = either Left (Right . second newEncIndex) $ moveRight' i

export
moveRight : PartialIndex a b -> (c : Encodable ** PartialIndex a c)
moveRight {b} i = either (\_ => (b ** i)) id $ moveRight' i

export
collatePair
  :  (a : Encodable)
  -> (b : Encodable)
  -> (c : Encodable)
  -> PartialIndex a b
  -> PartialIndex a c
  -> Maybe (PartialIndex a (b & c))
collatePair a b c iX iY  with (decEq a b)
  collatePair _ _ _ _ _ | Yes Refl = Nothing
  collatePair (a1 & a2) b c (Left iX) iY | No _ with (decEq (a1 & a2) c)
    collatePair _ _ _ _ _ | No _ | Yes Refl = Nothing
    collatePair (a1 & a2) b c (Left iX) (Left iY) | No _ | No _ with (decEq (a1 & a2) (b & c))
      collatePair (a1 & a2) a1 a2 (Left _) (Left _) | No _ | No _ | Yes Refl = Nothing
      collatePair (a & _) b c (Left iX) (Left iY) | No _ | No _ | No _ = Left <$> collatePair a b c iX iY
    collatePair (a1 & a2) b c (Left iX) (Right iY) | No _ | No _ with (decEq a1 b)
      collatePair (a1 & a2) a1 c (Left ()) (Right iY) | No _ | No _ | Yes Refl with (decEq a2 c)
        collatePair (a1 & a2) a1 a2 (Left ()) (Right ()) | No _ | No _ | Yes Refl | Yes Refl = Just emptyIndex
        collatePair (_ & _) _ _ (Left _) (Right _) | No _ | No _ | Yes Refl | No _ = Nothing
      collatePair (_ & _) _ _ (Left _) (Right _) | No _ | No _ | No _ = Nothing
  collatePair (a1 & a2) b c (Right iX) iY | No _ with (decEq (a1 & a2) c)
    collatePair _ _ _ _ _ | No _ | Yes Refl = Nothing
    collatePair (a1 & a2) b c (Right iX) (Left iY) | No _ | No _ = Nothing
    collatePair (a1 & a2) b c (Right iX) (Right iY) | No _ | No _ with (decEq (a1 & a2) (b & c))
      collatePair (_ & _) _ _ (Right _) (Right _) | No _ | No _ | Yes Refl = Nothing
      collatePair (_ & a) b c (Right iX) (Right iY) | No _ | No _ | No _ = Right <$> collatePair a b c iX iY
  collatePair (EncVect n a) b c (iX, isX) iY | No _ with (decEq (EncVect n a) c)
    collatePair _ _ _ _ _ | No _ | Yes Refl = Nothing
    collatePair (EncVect n a) b c (iX, isX) (iY, isY) | No _ | No _ with (decEq (EncVect n a) (b & c))
      collatePair _ _ _ _ _ | No _ | No _ | Yes Refl impossible
      collatePair (EncVect _ a) b c (iX, isX) (iY, isY) | No _ | No _ | No _ with (decEq iX iY)
        collatePair (EncVect _ a) b c (iX, isX) (iX, isY) | No _ | No _ | No _ | Yes Refl = MkPair iX <$> collatePair a b c isX isY
        collatePair _ _ _ _ _ | No _ | No _ | No _ | No _ = Nothing
  collatePair (NewEnc ident a) b c iX iY | No _ with (decEq (NewEnc ident a) c)
    collatePair _ _ _ _ _ | No _ | Yes Refl = Nothing
    collatePair (NewEnc ident a) b c iX iY | No _ | No _ with (decEq (NewEnc ident a) (b & c))
      | Yes Refl impossible
      | No _ = collatePair a b c iX iY

extractEither : Vect (S n) (Either a b) -> Maybe (Either (Vect (S n) a) (Vect (S n) b))
extractEither [Left x] = Just $ Left [x]
extractEither [Right x] = Just $ Right [x]
extractEither {n = S _} (x :: xs) with (extractEither xs)
  extractEither (Left y :: _) | Just (Left ys) = Just $ Left $ y :: ys
  extractEither (Right y :: _) | Just (Right ys) = Just $ Right $ y :: ys
  | _ = Nothing

export
collateVect
  :  (a : Encodable)
  -> (n : Nat)
  -> (b : Encodable)
  -> Vect n (PartialIndex a b)
  -> Maybe (PartialIndex a (EncVect n b))
collateVect a n b is with (decEq a b)
  collateVect _ _ _ _ | Yes Refl = Nothing
  collateVect Bit Z _ [] | No _ = Nothing
  collateVect Bit (S _) _ (_ :: _) | No _ impossible
  collateVect (a1 & a2) n b is | No _ with (decEq (a1 & a2) (EncVect n b))
    collateVect _ _ _ _ | No _ | Yes Refl impossible
    collateVect (a1 & a2) Z b [] | No _ | No _ = Nothing
    collateVect (a1 & a2) (S n) b is | No _ | No _ with (extractEither is)
      collateVect _ _ _ _ | No _ | No _ | Nothing = Nothing
      collateVect (a & _) (S n) b _ | No _ | No _ | Just (Left is') = Left <$> collateVect a (S n) b is'
      collateVect (_ & a) (S n) b _ | No _ | No _ | Just (Right is') = Right <$> collateVect a (S n) b is'
  collateVect (EncVect m a) n b is | No _ with (decEq (EncVect m a) (EncVect n b))
    collateVect (EncVect n a) n a is | No _ | Yes Refl = if map fst is == range then Just () else Nothing
    collateVect (EncVect m a) n b is | No _ | No _ with (SortedSet.toList $ SortedSet.fromList $ toList $ map fst is)
      | [i] = MkPair i <$> collateVect a n b (map snd is)
      | _ = Nothing
  collateVect (NewEnc ident a) n b is | No _ with (decEq (NewEnc ident a) (EncVect n b))
    | Yes Refl impossible
    | No _ = collateVect a n b is

export
collateNewEnc
  :  (a : Encodable)
  -> (ident : String)
  -> (b : Encodable)
  -> PartialIndex a b
  -> Maybe (PartialIndex a (NewEnc ident b))
collateNewEnc a ident b i with (decEq a b)
  collateNewEnc _ _ _ _ | Yes Refl = Nothing
  collateNewEnc (a1 & a2) ident b i | No _ with (decEq (a1 & a2) (NewEnc ident b))
    collateNewEnc _ _ _ _ | No _ | Yes Refl impossible
    collateNewEnc (a & _) ident b (Left i) | No _ | No _ = Left <$> collateNewEnc a ident b i
    collateNewEnc (_ & a) ident b (Right i) | No _ | No _ = Right <$> collateNewEnc a ident b i
  collateNewEnc (EncVect n a) ident b i | No _ with (decEq (EncVect n a) (NewEnc ident b))
    collateNewEnc _ _ _ _ | No _ | Yes Refl impossible
    collateNewEnc (EncVect _ a) ident b (i, is) | No _ | No _ = MkPair i <$> collateNewEnc a ident b is
  collateNewEnc (NewEnc ident' a) ident b i | No _ with (decEq (NewEnc ident' a) (NewEnc ident b))
    collateNewEnc (NewEnc ident a) ident a i | No _ | Yes Refl = Just ()
    collateNewEnc (NewEnc _ a) ident b i | No _ | No _ = collateNewEnc a ident b i

