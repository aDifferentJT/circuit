module CollatedProducing

import Circuit
import Data.Hash
import Data.List
import Data.Vect
import Decidable.Equality
import Encodable
import IndexType
import PartialIndex
import Utils
import WithBitType

%default total

public export
data CollatedProducing : Encodable -> Encodable -> Type where
  Input : PartialIndex input a -> CollatedProducing input a
  ProducedFrom : {a : Encodable} -> {b : Encodable} -> Primitive input a b -> PartialIndex b c -> CollatedProducing input c
  (&&) : CollatedProducing input a -> CollatedProducing input b -> CollatedProducing input (a && b)
  ProdVect : Vect n (CollatedProducing input a) -> CollatedProducing input (EncVect n a)
  ProdNewEnc : CollatedProducing input a -> CollatedProducing input (NewEnc i a)

collatePair : {input : Encodable} -> CollatedProducing input a1 -> CollatedProducing input a2 -> CollatedProducing input (a1 && a2)
collatePair (Input i1) (Input i2) = maybe (Input i1 && Input i2) Input $ collatePair i1 i2
collatePair (ProducedFrom {a = c1} {b = b1} prim1 i1) (ProducedFrom {a = c2} {b = b2} prim2 i2) =
  case (decEq c1 c2, decEq b1 b2) of
       (Yes Refl, Yes Refl) =>
                              if hash prim1 == hash prim2
                                 then maybe (ProducedFrom prim1 i1 && ProducedFrom prim2 i2) (ProducedFrom prim1) $ collatePair i1 i2
                                 else ProducedFrom prim1 i1 && ProducedFrom prim2 i2
       _ => ProducedFrom prim1 i1 && ProducedFrom prim2 i2
collatePair x y = x && y

extractTermini : Vect (S n) (CollatedProducing input a) -> Maybe (Either (Vect (S n) (PartialIndex input a)) (Vect (S n) (b : Encodable ** c : Encodable ** (Primitive input b c, PartialIndex c a))))
extractTermini [Input i] = Just $ Left [i]
extractTermini [ProducedFrom {a} {b} prim i] = Just $ Right [(a ** b ** (prim, i))]
extractTermini [_] = Nothing
extractTermini (x :: xs@(_ :: _)) = case (x, extractTermini xs) of
  (Input i, Just (Left is)) => Just $ Left $ i :: is
  (ProducedFrom {a = b} {b = c} prim i, Just (Right ys)) => Just $ Right $ (b ** c ** (prim, i)) :: ys
  _ => Nothing

collateVect : {n : Nat} -> {input : Encodable} -> Vect n (CollatedProducing input a) -> CollatedProducing input (EncVect n a)
collateVect [] = ProdVect []
collateVect xs@(_ :: _) =
  case extractTermini xs of
    Nothing => ProdVect xs
    Just (Left is) => maybe (ProdVect xs) Input $ collateVect is
    Just (Right ys) => case decEqVectDPair ys of
      Nothing => ProdVect xs
      Just (b ** ys') => case decEqVectDPair ys' of
        Nothing => ProdVect xs
        Just (c ** ys'') => case nubBy hash $ toList $ map fst ys'' of
          [prim] => maybe (ProdVect xs) (ProducedFrom prim) $ collateVect $ map snd ys''
          _ => ProdVect xs

collateNewEnc : {input : Encodable} -> {ident : String} -> CollatedProducing input a -> CollatedProducing input (NewEnc ident a)
collateNewEnc (Input i) =
  maybe (ProdNewEnc $ Input i) Input $ collateNewEnc i
collateNewEnc (ProducedFrom {b} prim i) =
  maybe (ProdNewEnc $ ProducedFrom prim i) (ProducedFrom prim) $ collateNewEnc i
collateNewEnc x = ProdNewEnc x

export
collate : {input : Encodable} -> {a : Encodable} -> Producing input a -> CollatedProducing input a
collate {a = Bit} (InputBit i) = Input $ partialFromIndex i
collate {a = Bit} (BitProducedFrom prim i) = ProducedFrom prim $ partialFromIndex i
collate {a = _ && _} (x, y) = collatePair (collate x) (collate y)
collate {a = EncVect _ _} xs = collateVect $ map collate xs
collate {a = NewEnc _ _} (MkNewType x) = collateNewEnc $ collate x

