module C_Circuit

import Circuit
import Data.Nat
import Data.Vect
import NatProofs
import VectProofs

%default total

public export
countBits : Encodable -> Nat
countBits Bit           = 1
countBits (a && b)       = countBits a + countBits b
countBits (EncVect n a) = n * countBits a
countBits (NewEnc _ a)  = countBits a

public export
countIndices : Encodable -> Nat
countIndices Bit           = Z
countIndices (x && y)       = S (maxNat (countIndices x) (countIndices y))
countIndices (EncVect k x) = S (countIndices x)
countIndices (NewEnc _ x)  = countIndices x

public export
manyArgs : Vect n Type -> Type -> Type
manyArgs []        b = b
manyArgs (a :: as) b = a -> manyArgs as b

constN : {as : Vect n Type} -> b -> manyArgs as b
constN {as = []}     x = x
constN {as = _ :: _} x = const (constN x)

composeN : {as : Vect n Type} -> (b -> c) -> manyArgs as b -> manyArgs as c
composeN {as = []}      f g = f g
composeN {as = a :: as} f g = composeN f . g

mergeArgs : {as : Vect m Type} -> {bs : Vect n Type} -> manyArgs as c -> manyArgs bs d -> manyArgs (as ++ bs) (c, d)
mergeArgs {as = []}     f g = composeN (MkPair f) g
mergeArgs {as = _ :: _} f g = \x => mergeArgs (f x) g

public export
FromCType : Encodable -> Type
FromCType a = manyArgs (replicate (countBits a) Int) (PrimType a)

export
fromCPoly : (a : Encodable) -> FromCType a
fromCPoly Bit               = \b => case b of
                                         0 => B0
                                         _ => B1
fromCPoly (a && b)           = rewrite sym $ concatReplicate (countBits a) (countBits b) Int in
                                      mergeArgs (fromCPoly a) (fromCPoly b)
fromCPoly (EncVect Z a)     = []
fromCPoly (EncVect (S n) a) = composeN {as = replicate (countBits a + countBits (EncVect n a)) Int} (uncurry Data.Vect.(::)) $
                              rewrite sym $ concatReplicate (countBits a) (countBits (EncVect n a)) Int in
                                      mergeArgs (fromCPoly a) (fromCPoly (assert_smaller (EncVect (S n) a) (EncVect n a)))
fromCPoly (NewEnc _ a)      = composeN MkNewType $ fromCPoly a

public export
ToCType : {default 0 extra : Nat} -> Encodable -> Type
ToCType {extra} a = PrimType a -> manyArgs (replicate (countIndices a + extra) Int) Int

export
toCPoly : {default 0 extra : Nat} -> (a : Encodable) -> ToCType {extra} a
toCPoly {extra} Bit B0 = constN (the Int 0)
toCPoly {extra} Bit B1 = constN (the Int 1)
toCPoly {extra} (a && b) (x, y) = f
  where
    f : manyArgs (replicate (countIndices (a && b) + extra) Int) Int
    f 0 =
      let
        smaller : LTE (countIndices a) (maxNat (countIndices a) (countIndices b))
        smaller = xSmallerThanMaxNatXY (countIndices a) (countIndices b)
      in
      let
        padding : Nat
        padding = maxNat (countIndices a) (countIndices b) `minus` countIndices a
      in
      rewrite sym $ plusMinusCancel (maxNat (countIndices a) (countIndices b)) (countIndices a) {smaller} in
              rewrite sym $ plusAssociative (countIndices a) padding extra in
                      toCPoly {extra=padding + extra} a x
    f 1 =
      let
        smaller : LTE (countIndices b) (maxNat (countIndices a) (countIndices b))
        smaller = ySmallerThanMaxNatXY (countIndices a) (countIndices b)
      in
      let
        padding : Nat
        padding = maxNat (countIndices a) (countIndices b) `minus` countIndices b
      in
      rewrite sym $ plusMinusCancel (maxNat (countIndices a) (countIndices b)) (countIndices b) {smaller} in
              rewrite sym $ plusAssociative (countIndices b) padding extra in
                      toCPoly {extra=padding + extra} b y
    f _ = constN (the Int (-1))
toCPoly {extra} (EncVect n a) xs =
  \i =>
       maybe (constN (the Int (-1))) (toCPoly {extra} a . flip index xs) $
       integerToFin (cast i) n
toCPoly {extra} (NewEnc _ a)  (MkNewType x) = toCPoly {extra} a x

