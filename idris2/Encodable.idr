module Encodable

import Decidable.Equality
import Utils

%default total

infixr 9 &&

public export
data Encodable : Type where
  Bit     : Encodable
  (&&)    : Encodable -> Encodable -> Encodable
  EncVect : Nat -> Encodable -> Encodable
  NewEnc  : String -> Encodable -> Encodable

export
encPairInjective : {0 a' : Encodable} -> {0 b' : Encodable} -> ((a && b) = (a' && b')) -> (a = a', b = b')
encPairInjective Refl = (Refl, Refl)

export
encVectInjective : (EncVect n a = EncVect n' a') -> (n = n', a = a')
encVectInjective Refl = (Refl, Refl)

export
newEncInjective : (NewEnc ident a = NewEnc ident' b) -> (ident = ident', a = b)
newEncInjective Refl = (Refl, Refl)

export
DecEq Encodable where
  decEq Bit Bit = Yes Refl
  decEq (a1 && a2) (b1 && b2) = case (decEq a1 b1, decEq a2 b2) of
    (Yes Refl, Yes Refl) => Yes Refl
    (Yes Refl, No  p   ) => No $ p . snd . encPairInjective
    (No  p,    Yes Refl) => No $ p . fst . encPairInjective
    (No  p,    No  _   ) => No $ p . fst . encPairInjective
  decEq (EncVect m a) (EncVect n b) = case (decEq m n, decEq a b) of
    (Yes Refl, Yes Refl) => Yes Refl
    (Yes Refl, No  p   ) => No $ p . snd . encVectInjective
    (No  p,    Yes Refl) => No $ p . fst . encVectInjective
    (No  p,    No  _   ) => No $ p . fst . encVectInjective
  decEq (NewEnc ident a) (NewEnc ident' b) = case (decEq ident ident', decEq a b) of
    (Yes Refl, Yes Refl) => Yes Refl
    (Yes Refl, No  p   ) => No $ p . snd . newEncInjective
    (No  p,    Yes Refl) => No $ p . fst . newEncInjective
    (No  p,    No  _   ) => No $ p . fst . newEncInjective
  decEq Bit (b1 && b2) =
    let
      f : Not (Bit = b1 && b2)
      f Refl impossible
    in
        No f
  decEq Bit (EncVect n b) =
    let
      f : Not (Bit = EncVect n b)
      f Refl impossible
    in
        No f
  decEq Bit (NewEnc ident b) =
    let
      f : Not (Bit = NewEnc ident b)
      f Refl impossible
    in
        No f
  decEq (a1 && a2) Bit =
    let
      f : Not (a1 && a2 = Bit)
      f Refl impossible
    in
        No f
  decEq (a1 && a2) (EncVect n b) =
    let
      f : Not (a1 && a2 = EncVect n b)
      f Refl impossible
    in
        No f
  decEq (a1 && a2) (NewEnc ident b) =
    let
      f : Not (a1 && a2 = NewEnc ident b)
      f Refl impossible
    in
        No f
  decEq (EncVect n a) Bit =
    let
      f : Not (EncVect n a = Bit)
      f Refl impossible
    in
        No f
  decEq (EncVect n a) (b1 && b2) =
    let
      f : Not (EncVect n a = b1 && b2)
      f Refl impossible
    in
        No f
  decEq (EncVect n a) (NewEnc ident b) =
    let
      f : Not (EncVect n a = NewEnc ident b)
      f Refl impossible
    in
        No f
  decEq (NewEnc ident a) Bit =
    let
      f : Not (NewEnc ident a = Bit)
      f Refl impossible
    in
        No f
  decEq (NewEnc ident a) (b1 && b2) =
    let
      f : Not (NewEnc ident a = b1 && b2)
      f Refl impossible
    in
        No f
  decEq (NewEnc ident a) (EncVect n b) =
    let
      f : Not (NewEnc ident a = EncVect n b)
      f Refl impossible
    in
        No f

export
Eq Encodable where
  a == b = case decEq a b of
    Yes _ => True
    No _ => False

export
Ord Encodable where
  compare Bit            Bit            = EQ
  compare Bit            (_ && _)       = LT
  compare Bit            (EncVect _ _)  = LT
  compare Bit            (NewEnc _ _)   = LT
  compare (_ && _)       Bit            = GT
  compare (a && b)       (a' && b')     = thenCompare (compare a a') (compare b b')
  compare (_ && _)       (EncVect _ _)  = LT
  compare (_ && _)       (NewEnc _ _)   = LT
  compare (EncVect _ _)  Bit            = GT
  compare (EncVect _ _)  (_ && _)       = GT
  compare (EncVect m a)  (EncVect n b)  = thenCompare (compare m n) (compare a b)
  compare (EncVect _ _)  (NewEnc _ _)   = LT
  compare (NewEnc _ _)   Bit            = GT
  compare (NewEnc _ _)   (_ && _)       = GT
  compare (NewEnc _ _)   (EncVect _ _)  = GT
  compare (NewEnc i a)   (NewEnc i' b)  = thenCompare (compare i i') (compare a b)


public export
data LTE : Encodable -> Encodable -> Type where
  LTERefl : Encodable.LTE a a
  LTFst : LTE a b1 -> LTE a (b1 && b2)
  LTSnd : LTE a b2 -> LTE a (b1 && b2)
  LTVect : LTE a b -> LTE a (EncVect n b)
  LTNewEnc : LTE a b -> LTE a (NewEnc i b)

export
lteTrans : Encodable.LTE a b -> Encodable.LTE b c -> Encodable.LTE a c
lteTrans p1 LTERefl = p1
lteTrans p1 (LTFst p2) = LTFst $ lteTrans p1 p2
lteTrans p1 (LTSnd p2) = LTSnd $ lteTrans p1 p2
lteTrans p1 (LTVect p2) = LTVect $ lteTrans p1 p2
lteTrans p1 (LTNewEnc p2) = LTNewEnc $ lteTrans p1 p2

lteFst : LTE (a && _) b -> LTE a b
lteFst = lteTrans $ LTFst LTERefl

lteSnd : LTE (_ && a) b -> LTE a b
lteSnd = lteTrans $ LTSnd LTERefl

lteVect : LTE (EncVect _ a) b -> LTE a b
lteVect = lteTrans $ LTVect LTERefl

lteNewEnc : LTE (NewEnc _ a) b -> LTE a b
lteNewEnc = lteTrans $ LTNewEnc LTERefl

mutual
  export
  Uninhabited (LTE (a && _) a) where
    uninhabited LTERefl impossible
    uninhabited {a = _ && _} (LTFst p) = absurd $ lteFst p
    uninhabited {a = a && b} (LTSnd p) = absurd $ lteFst p
    uninhabited {a = EncVect n a} (LTVect p) = absurd $ lteFst p
    uninhabited {a = NewEnc _ _} (LTNewEnc p) = absurd $ lteFst p

  export
  Uninhabited (LTE (_ && a) a) where
    uninhabited LTERefl impossible
    uninhabited {a = _ && _} (LTFst p) = absurd $ lteSnd p
    uninhabited {a = a && b} (LTSnd p) = absurd $ lteSnd p
    uninhabited {a = EncVect n a} (LTVect p) = absurd $ lteSnd p
    uninhabited {a = NewEnc _ _} (LTNewEnc p) = absurd $ lteSnd p

  export
  Uninhabited (LTE (EncVect _ a) a) where
    uninhabited LTERefl impossible
    uninhabited {a = _ && _} (LTFst p) = absurd $ lteVect p
    uninhabited {a = a && b} (LTSnd p) = absurd $ lteVect p
    uninhabited {a = EncVect n a} (LTVect p) = absurd $ lteVect p
    uninhabited {a = NewEnc _ _} (LTNewEnc p) = absurd $ lteVect p

  export
  Uninhabited (LTE (NewEnc _ a) a) where
    uninhabited LTERefl impossible
    uninhabited {a = _ && _} (LTFst p) = absurd $ lteNewEnc p
    uninhabited {a = a && b} (LTSnd p) = absurd $ lteNewEnc p
    uninhabited {a = EncVect n a} (LTVect p) = absurd $ lteNewEnc p
    uninhabited {a = NewEnc _ _} (LTNewEnc p) = absurd $ lteNewEnc p

selfNotLeft : {a : Encodable} -> {b : Encodable} -> LTE (a && _) b -> Not (a = b)
selfNotLeft {a} {b = a} lte Refl = absurd lte

selfNotRight : {a : Encodable} -> {b : Encodable} -> LTE (_ && a) b -> Not (a = b)
selfNotRight {a} {b = a} lte Refl = absurd lte

selfNotVect : {a : Encodable} -> {b : Encodable} -> LTE (EncVect _ a) b -> Not (a = b)
selfNotVect {a} {b = a} lte Refl = absurd lte

selfNotNewEnc : {a : Encodable} -> {b : Encodable} -> LTE (NewEnc _ a) b -> Not (a = b)
selfNotNewEnc {a} {b = a} lte Refl = absurd lte

export
lteAntiSymmetric : {a : Encodable} -> {b : Encodable} -> LTE a b -> LTE b a -> a = b
lteAntiSymmetric LTERefl _ = Refl
lteAntiSymmetric _ LTERefl = Refl

lteAntiSymmetric (LTFst p1) (LTFst p2) = absurd $ selfNotLeft p1 $ lteAntiSymmetric (lteFst p1) (lteFst p2)
lteAntiSymmetric (LTFst p1) (LTSnd p2) = absurd $ selfNotRight p1 $ lteAntiSymmetric (lteSnd p1) (lteFst p2)
lteAntiSymmetric (LTFst p1) (LTVect p2) = absurd $ selfNotVect p1 $ lteAntiSymmetric (lteVect p1) (lteFst p2)
lteAntiSymmetric (LTFst p1) (LTNewEnc p2) = absurd $ selfNotNewEnc p1 $ lteAntiSymmetric (lteNewEnc p1) (lteFst p2)

lteAntiSymmetric (LTSnd p1) (LTFst p2) = absurd $ selfNotLeft p1 $ lteAntiSymmetric (lteFst p1) (lteSnd p2)
lteAntiSymmetric (LTSnd p1) (LTSnd p2) = absurd $ selfNotRight p1 $ lteAntiSymmetric (lteSnd p1) (lteSnd p2)
lteAntiSymmetric (LTSnd p1) (LTVect p2) = absurd $ selfNotVect p1 $ lteAntiSymmetric (lteVect p1) (lteSnd p2)
lteAntiSymmetric (LTSnd p1) (LTNewEnc p2) = absurd $ selfNotNewEnc p1 $ lteAntiSymmetric (lteNewEnc p1) (lteSnd p2)

lteAntiSymmetric (LTVect p1) (LTFst p2) = absurd $ selfNotLeft p1 $ lteAntiSymmetric (lteFst p1) (lteVect p2)
lteAntiSymmetric (LTVect p1) (LTSnd p2) = absurd $ selfNotRight p1 $ lteAntiSymmetric (lteSnd p1) (lteVect p2)
lteAntiSymmetric (LTVect p1) (LTVect p2) = absurd $ selfNotVect p1 $ lteAntiSymmetric (lteVect p1) (lteVect p2)
lteAntiSymmetric (LTVect p1) (LTNewEnc p2) = absurd $ selfNotNewEnc p1 $ lteAntiSymmetric (lteNewEnc p1) (lteVect p2)

lteAntiSymmetric (LTNewEnc p1) (LTFst p2) = absurd $ selfNotLeft p1 $ lteAntiSymmetric (lteFst p1) (lteNewEnc p2)
lteAntiSymmetric (LTNewEnc p1) (LTSnd p2) = absurd $ selfNotRight p1 $ lteAntiSymmetric (lteSnd p1) (lteNewEnc p2)
lteAntiSymmetric (LTNewEnc p1) (LTVect p2) = absurd $ selfNotVect p1 $ lteAntiSymmetric (lteVect p1) (lteNewEnc p2)
lteAntiSymmetric (LTNewEnc p1) (LTNewEnc p2) = absurd $ selfNotNewEnc p1 $ lteAntiSymmetric (lteNewEnc p1) (lteNewEnc p2)

