module CollatedProducing

import Circuit
import Data.Hash
import Data.Vect
import Encodable
import IndexType
import PartialIndex
import Utils
import WithBitType

%default total

public export
data CollatedProducing : Encodable -> Encodable -> Type where
  Input : PartialIndex input a -> CollatedProducing input a
  ProducedFrom : Primitive input a b -> PartialIndex b c -> CollatedProducing input c
  (&&) : CollatedProducing input a -> CollatedProducing input b -> CollatedProducing input (a & b)
  ProdVect : Vect n (CollatedProducing input a) -> CollatedProducing input (EncVect n a)
  ProdNewEnc : CollatedProducing input a -> CollatedProducing input (NewEnc i a)

collatePair : CollatedProducing input a1 -> CollatedProducing input a2 -> CollatedProducing input (a1 & a2)
collatePair {a1} {a2} (Input iX) (Input iY) = maybe (Input iX && Input iY) Input $ collatePair input a1 a2 iX iY
collatePair {a1} {a2} (ProducedFrom {a = cX} {b = bX} primX iX) (ProducedFrom {a = cY} {b = bY} primY iY) with (decEq cX cY, decEq bX bY)
  collatePair {a1} {a2} (ProducedFrom {b} primX iX) (ProducedFrom {b} primY iY) | (Yes Refl, Yes Refl) =
    if hash primX == hash primY
       then maybe (ProducedFrom primX iX && ProducedFrom primY iY) (ProducedFrom primX) $ collatePair b a1 a2 iX iY
       else ProducedFrom primX iX && ProducedFrom primY iY
  | _ = ProducedFrom primX iX && ProducedFrom primY iY
collatePair x y = x && y

extractTermini : Vect (S n) (CollatedProducing input a) -> Maybe (Either (Vect (S n) (PartialIndex input a)) (Vect (S n) (b : Encodable ** c : Encodable ** (Primitive input b c, PartialIndex c a))))
extractTermini [Input i] = Just $ Left [i]
extractTermini [ProducedFrom {a} {b} prim i] = Just $ Right [(a ** b ** (prim, i))]
extractTermini [_] = Nothing
extractTermini {n = S _} (x :: xs) with (extractTermini xs)
  extractTermini (Input i :: _) | Just (Left is) = Just $ Left $ i :: is
  extractTermini (ProducedFrom {a} {b} prim i :: _) | Just (Right ys) = Just $ Right $ (a ** b ** (prim, i)) :: ys
  | _ = Nothing

collateVect : Vect n (CollatedProducing input a) -> CollatedProducing input (EncVect n a)
collateVect {n = Z} [] = ProdVect []
collateVect {n = S n} {input} {a} xs with (extractTermini xs)
  | Nothing = ProdVect xs
  | Just (Left is) = maybe (ProdVect xs) Input $ collateVect input (S n) a is
  | Just (Right ys) with (decEqVectDPair ys)
    | Nothing = ProdVect xs
    | Just (b ** ys') with (decEqVectDPair ys')
      | Nothing = ProdVect xs
      | Just (c ** ys'') with (removeDuplicatesWith hash $ toList $ map fst ys'')
        | [prim] = maybe (ProdVect xs) (ProducedFrom prim) $ collateVect c (S n) a $ map snd ys''
        | _ = ProdVect xs

collateNewEnc : CollatedProducing input a -> CollatedProducing input (NewEnc ident a)
collateNewEnc {ident} {a} (Input i) =
  maybe (ProdNewEnc $ Input i) Input $ collateNewEnc input ident a i
collateNewEnc {ident} {a} (ProducedFrom {b} prim i) =
  maybe (ProdNewEnc $ ProducedFrom prim i) (ProducedFrom prim) $ collateNewEnc b ident a i
collateNewEnc x = ProdNewEnc x

export
collate : Producing input a -> CollatedProducing input a
collate {a = Bit} (InputBit i) = Input $ partialFromIndex i
collate {a = Bit} (BitProducedFrom prim i) = ProducedFrom prim $ partialFromIndex i
collate {a = _ & _} (x, y) = collatePair (collate x) (collate y)
collate {a = EncVect _ _} xs = collateVect $ map collate xs
collate {a = NewEnc _ _} (MkNewType x) = collateNewEnc $ collate x

