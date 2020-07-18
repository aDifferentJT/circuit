module C_Circuit

import Circuit
import Data.Nat
import Data.Vect
import NatProofs
import VectProofs

%default total

public export
countBits : Encodable -> Nat
countBits Bit = 1
countBits UnitEnc = 0
countBits (a && b) = countBits a + countBits b
countBits (EncVect n a) = n * countBits a
countBits (NewEnc _ a) = countBits a

public export
countIndices : Encodable -> Nat
countIndices Bit = Z
countIndices UnitEnc = Z
countIndices (x && y) = S (maxNat (countIndices x) (countIndices y))
countIndices (EncVect k x) = S (countIndices x)
countIndices (NewEnc _ x) = countIndices x

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

mergeArgs : {as : Vect m Type} -> {bs : Vect n Type} -> {0 x : c} -> {0 y : c} -> {0 z : c} -> (0 cToType : c -> Type) -> (cToType x -> cToType y -> cToType z) -> manyArgs as (cToType x) -> manyArgs bs (cToType y) -> manyArgs (as ++ bs) (cToType z)
mergeArgs {as = []}     _ f g h = composeN (f g) h
mergeArgs {as = _ :: _} cToType f g h = \x => mergeArgs cToType f (g x) h

public export
FromCType : Encodable -> Type
FromCType a = manyArgs (replicate (countBits a) Int) (Encoding (BitType Bit) a)

export
fromCPoly : (a : Encodable) -> FromCType a
fromCPoly Bit = \b => case b of
                           0 => BitEncoding B0
                           _ => BitEncoding B1
fromCPoly UnitEnc = UnitEnc
fromCPoly (a && b) = rewrite sym $ concatReplicate (countBits a) (countBits b) Int in
                             mergeArgs (Encoding $ BitType Bit) Encoding.(&&) (fromCPoly a) (fromCPoly b)
fromCPoly (EncVect Z a) = []
fromCPoly (EncVect (S n) a) = rewrite sym $ concatReplicate (countBits a) (countBits (EncVect n a)) Int in
                                      mergeArgs (Encoding $ BitType Bit) Encoding.(::) (fromCPoly a) (fromCPoly $ assert_smaller (EncVect (S n) a) $ EncVect n a)
fromCPoly (NewEnc _ a)      = composeN NewEncoding $ fromCPoly a

public export
ToCType : {default 0 extra : Nat} -> Encodable -> Type
ToCType {extra} a = Encoding (BitType Bit) a -> manyArgs (replicate (countIndices a + extra) Int) Int

export
toCPoly : {default 0 extra : Nat} -> (a : Encodable) -> ToCType {extra} a
toCPoly Bit (BitEncoding b) = constN $ the Int $ case b of
                                                      B0 => 0
                                                      B1 => 1
toCPoly UnitEnc UnitEnc = constN $ the Int 0
toCPoly (a && b) (x && y) = f
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
toCPoly (EncVect n a) xs =
  \i =>
       maybe (constN (the Int (-1))) (toCPoly {extra} a . flip indexVect xs) $
       integerToFin (cast i) n
toCPoly (NewEnc _ a) (NewEncoding x) = toCPoly {extra} a x

