module Encodable

import Decidable.Equality
import Utils

%default total

infixr 9 &&

public export
data Encodable : Type where
  Bit     : Encodable
  UnitEnc    : Encodable
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
  decEq UnitEnc UnitEnc = Yes Refl
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
  decEq Bit UnitEnc =
    let
      f : Not (Bit = UnitEnc)
      f Refl impossible
    in
        No f
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
  decEq UnitEnc Bit =
    let
      f : Not (UnitEnc = Bit)
      f Refl impossible
    in
        No f
  decEq UnitEnc (b1 && b2) =
    let
      f : Not (UnitEnc = b1 && b2)
      f Refl impossible
    in
        No f
  decEq UnitEnc (EncVect n b) =
    let
      f : Not (UnitEnc = EncVect n b)
      f Refl impossible
    in
        No f
  decEq UnitEnc (NewEnc ident b) =
    let
      f : Not (UnitEnc = NewEnc ident b)
      f Refl impossible
    in
        No f
  decEq (a1 && a2) Bit =
    let
      f : Not (a1 && a2 = Bit)
      f Refl impossible
    in
        No f
  decEq (a1 && a2) UnitEnc =
    let
      f : Not (a1 && a2 = UnitEnc)
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
  decEq (EncVect n a) UnitEnc =
    let
      f : Not (EncVect n a = UnitEnc)
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
  decEq (NewEnc ident a) UnitEnc =
    let
      f : Not (NewEnc ident a = UnitEnc)
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
  compare Bit            UnitEnc        = LT
  compare Bit            (_ && _)       = LT
  compare Bit            (EncVect _ _)  = LT
  compare Bit            (NewEnc _ _)   = LT
  compare UnitEnc        Bit            = GT
  compare UnitEnc        UnitEnc        = EQ
  compare UnitEnc        (_ && _)       = LT
  compare UnitEnc        (EncVect _ _)  = LT
  compare UnitEnc        (NewEnc _ _)   = LT
  compare (_ && _)       Bit            = GT
  compare (_ && _)       UnitEnc        = GT
  compare (a && b)       (a' && b')     = thenCompare (compare a a') (compare b b')
  compare (_ && _)       (EncVect _ _)  = LT
  compare (_ && _)       (NewEnc _ _)   = LT
  compare (EncVect _ _)  Bit            = GT
  compare (EncVect _ _)  UnitEnc        = GT
  compare (EncVect _ _)  (_ && _)       = GT
  compare (EncVect m a)  (EncVect n b)  = thenCompare (compare m n) (compare a b)
  compare (EncVect _ _)  (NewEnc _ _)   = LT
  compare (NewEnc _ _)   Bit            = GT
  compare (NewEnc _ _)   UnitEnc        = GT
  compare (NewEnc _ _)   (_ && _)       = GT
  compare (NewEnc _ _)   (EncVect _ _)  = GT
  compare (NewEnc i a)   (NewEnc i' b)  = thenCompare (compare i i') (compare a b)

