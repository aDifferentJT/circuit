module Encodable

import Decidable.Equality
import Utils

%default total

public export
data Encodable : Type where
  Bit     : Encodable
  UnitEnc : Encodable
  (&&)    : Encodable -> Encodable -> Encodable
  EncVect : Nat -> Encodable -> Encodable
  NewEnc  : String -> Encodable -> Encodable

export
encPairInjective : {a' : Encodable} -> {b' : Encodable} -> ((a && b) = (a' && b')) -> (a = a', b = b')
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
  decEq Bit UnitEnc = No $ \Refl impossible
  decEq Bit (b1 && b2) = No $ \Refl impossible
  decEq Bit (EncVect n b) = No $ \Refl impossible
  decEq Bit (NewEnc ident b) = No $ \Refl impossible
  decEq UnitEnc Bit = No $ \Refl impossible
  decEq UnitEnc (b1 && b2) = No $ \Refl impossible
  decEq UnitEnc (EncVect n b) = No $ \Refl impossible
  decEq UnitEnc (NewEnc ident b) = No $ \Refl impossible
  decEq (a1 && a2) Bit = No $ \Refl impossible
  decEq (a1 && a2) UnitEnc = No $ \Refl impossible
  decEq (a1 && a2) (EncVect n b) = No $ \Refl impossible
  decEq (a1 && a2) (NewEnc ident b) = No $ \Refl impossible
  decEq (EncVect n a) Bit = No $ \Refl impossible
  decEq (EncVect n a) UnitEnc = No $ \Refl impossible
  decEq (EncVect n a) (b1 && b2) = No $ \Refl impossible
  decEq (EncVect n a) (NewEnc ident b) = No $ \Refl impossible
  decEq (NewEnc ident a) Bit = No $ \Refl impossible
  decEq (NewEnc ident a) UnitEnc = No $ \Refl impossible
  decEq (NewEnc ident a) (b1 && b2) = No $ \Refl impossible
  decEq (NewEnc ident a) (EncVect n b) = No $ \Refl impossible

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

