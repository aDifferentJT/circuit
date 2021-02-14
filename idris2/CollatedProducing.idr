module CollatedProducing

import Circuit
import Data.Hash
import Data.List
import Data.Vect
import Decidable.Equality
import Encodable
import Encoding
import IndexType
import LinearUtils
import Utils

%default total

public export
CollatedProducing : (Encodable -> Encodable -> Type) -> Encodable -> Encodable -> Type
CollatedProducing prim input = Encoding $ ProducingBit prim input

collatePair : CollatedProducing prim input a1 -> CollatedProducing prim input a2 -> CollatedProducing prim input (a1 && a2)
collatePair (BitEncoding (InputBit i1)) (BitEncoding (InputBit i2)) = maybe (BitEncoding (InputBit i1) && BitEncoding (InputBit i2)) (relax BitEncoding . InputBit) $ collatePair i1 i2
collatePair (BitEncoding (BitProducedFrom {a = c1} {b = b1} prim1 i1)) (BitEncoding (BitProducedFrom {a = c2} {b = b2} prim2 i2)) =
  case (decEq c1 c2, decEq b1 b2) of
       (Yes Refl, Yes Refl) =>
                              if hash prim1 == hash prim2
                                 then maybe (BitEncoding (BitProducedFrom prim1 i1) && BitEncoding (BitProducedFrom prim2 i2)) (relax BitEncoding . BitProducedFrom prim1) $ collatePair i1 i2
                                 else BitEncoding (BitProducedFrom prim1 i1) && BitEncoding (BitProducedFrom prim2 i2)
       _ => BitEncoding (BitProducedFrom prim1 i1) && BitEncoding (BitProducedFrom prim2 i2)
collatePair x y = x && y

collateVect : CollatedProducing prim input a -> CollatedProducing prim input (EncVect n a) -> CollatedProducing prim input (EncVect (S n) a)
collateVect (BitEncoding (InputBit i1)) (BitEncoding (InputBit i2)) = maybe (BitEncoding (InputBit i1) :: BitEncoding (InputBit i2)) (relax BitEncoding . InputBit) $ collateVect i1 i2
collateVect (BitEncoding (BitProducedFrom {a = c1} {b = b1} prim1 i1)) (BitEncoding (BitProducedFrom {a = c2} {b = b2} prim2 i2)) =
  case (decEq c1 c2, decEq b1 b2) of
       (Yes Refl, Yes Refl) =>
                              if hash prim1 == hash prim2
                                 then maybe (BitEncoding (BitProducedFrom prim1 i1) :: BitEncoding (BitProducedFrom prim2 i2)) (relax BitEncoding . BitProducedFrom prim1) $ collateVect i1 i2
                                 else BitEncoding (BitProducedFrom prim1 i1) :: BitEncoding (BitProducedFrom prim2 i2)
       _ => BitEncoding (BitProducedFrom prim1 i1) :: BitEncoding (BitProducedFrom prim2 i2)
collateVect x xs = x :: xs

collateNewEnc : {ident : String} -> CollatedProducing prim input a -> CollatedProducing prim input (NewEnc ident a)
collateNewEnc (BitEncoding (InputBit i)) =
  maybe (NewEncoding $ BitEncoding $ InputBit i) (relax BitEncoding . InputBit) $ collateNewEnc i
collateNewEnc (BitEncoding (BitProducedFrom {b} prim i)) =
  maybe (NewEncoding $ BitEncoding $ BitProducedFrom prim i) (relax BitEncoding . BitProducedFrom prim) $ collateNewEnc i
collateNewEnc x = NewEncoding x

export
collate : Producing prim input a -> CollatedProducing prim input a
collate (BitEncoding x) = BitEncoding $ removeBitType (ProducingBit prim input) x
collate UnitEnc = UnitEnc
collate (x && y) = collatePair (collate x) (collate y)
collate [] = []
collate (x :: xs) = collateVect (collate x) (collate xs)
collate (NewEncoding x) = collateNewEnc $ collate x

