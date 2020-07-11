module Wires

import AuxProofs
import Circuit
import CollatedProducing
import Control.Monad.State
import Data.Fin
import Data.List
import Data.SortedSet
import Encodable
import Encoding
import EqOrdUtils
import IndexType
import Utils

%default total

data Terminus : Encodable -> Encodable -> Encodable -> Type where
  InputTerminus : PartialIndex input width -> Terminus input output width
  OutputTerminus : PartialIndex output width -> Terminus input output width
  PrimTerminus : String -> Bits64 -> (a : Encodable) -> PartialIndex a width -> Terminus input output width

Eq (Terminus input output width) where
  (InputTerminus i1)  == (InputTerminus i2)  = i1 == i2
  (OutputTerminus i1) == (OutputTerminus i2) = i1 == i2
  (PrimTerminus _ h1 a1 i1) == (PrimTerminus _ h2 a2 i2) =
    case decEq a1 a2 of
         Yes Refl => h1 == h2 && i1 == i2
         No _ => False
  (InputTerminus _)      == (OutputTerminus _)     = False
  (InputTerminus _)      == (PrimTerminus _ _ _ _) = False
  (OutputTerminus _)     == (InputTerminus _)      = False
  (OutputTerminus _)     == (PrimTerminus _ _ _ _) = False
  (PrimTerminus _ _ _ _) == (InputTerminus _)      = False
  (PrimTerminus _ _ _ _) == (OutputTerminus _)     = False

Ord (Terminus input output width) where
  compare (InputTerminus i1)  (InputTerminus i2)  = compare i1 i2
  compare (OutputTerminus i1) (OutputTerminus i2) = compare i1 i2
  compare (PrimTerminus _ h1 a1 i1) (PrimTerminus _ h2 a2 i2) =
    case decEq a1 a2 of
         Yes Refl => thenCompare (compare h1 h2) (compare i1 i2)
         No _ => compare a1 a2
  compare (InputTerminus _)      (OutputTerminus _)     = LT
  compare (InputTerminus _)      (PrimTerminus _ _ _ _) = LT
  compare (OutputTerminus _)     (InputTerminus _)      = GT
  compare (OutputTerminus _)     (PrimTerminus _ _ _ _) = LT
  compare (PrimTerminus _ _ _ _) (InputTerminus _)      = GT
  compare (PrimTerminus _ _ _ _) (OutputTerminus _)     = GT

data Wire : Encodable -> Encodable -> Type where
  MkWire : {width : Encodable} -> Terminus input output width -> Terminus input output width -> Wire input output

Eq (Wire input output) where
  (MkWire {width = width} i1 i2) == (MkWire {width = width'} i1' i2') =
    case decEq width width' of
         Yes Refl => i1 == i1' && i2 == i2'
         No _ => False

Ord (Wire input output) where
  compare (MkWire {width = width} i1 i2) (MkWire {width = width'} i1' i2') =
    case decEq width width' of
         Yes Refl => thenCompare (compare i1 i1') (compare i2 i2')
         No _ => compare width width'

collateTermini : {input : Encodable} -> {a : Encodable} -> Encoding (BitType (Terminus input output Bit)) a -> Encoding (Terminus input output) a
collateTermini (BitEncoding x) = BitEncoding $ removeBitType (Terminus input output) x
collateTermini UnitEnc = UnitEnc
collateTermini (x && y) =
  case (collateTermini x, collateTermini y) of
       (BitEncoding (InputTerminus i1), BitEncoding (InputTerminus i2)) => maybe (BitEncoding (InputTerminus i1) && BitEncoding (InputTerminus i2)) (BitEncoding . InputTerminus) $ collatePair i1 i2
       (BitEncoding (PrimTerminus name1 h1 b1 i1), BitEncoding (PrimTerminus name2 h2 b2 i2)) =>
         case (h1 == h2, decEq b1 b2) of
              (True, Yes p) => maybe (BitEncoding (PrimTerminus name1 h1 b1 i1) && BitEncoding (PrimTerminus name2 h2 b2 i2)) (BitEncoding . PrimTerminus name1 h1 b1) $ collatePair i1 $ rewrite p in i2
              _ => BitEncoding (PrimTerminus name1 h1 b1 i1) && BitEncoding (PrimTerminus name2 h2 b2 i2)
       (x, y) => x && y
collateTermini [] = []
collateTermini (x :: xs) =
  case (collateTermini x, collateTermini xs) of
       (BitEncoding (InputTerminus i1), BitEncoding (InputTerminus i2)) => maybe (BitEncoding (InputTerminus i1) :: BitEncoding (InputTerminus i2)) (BitEncoding . InputTerminus) $ collateVect i1 i2
       (BitEncoding (PrimTerminus name1 h1 b1 i1), BitEncoding (PrimTerminus name2 h2 b2 i2)) =>
         case (h1 == h2, decEq b1 b2) of
              (True, Yes p) => maybe (BitEncoding (PrimTerminus name1 h1 b1 i1) :: BitEncoding (PrimTerminus name2 h2 b2 i2)) (BitEncoding . PrimTerminus name1 h1 b1) $ collateVect i1 $ rewrite p in i2
              _ => BitEncoding (PrimTerminus name1 h1 b1 i1) :: BitEncoding (PrimTerminus name2 h2 b2 i2)
       (x, y) => x :: y
collateTermini (NewEncoding x) =
  case collateTermini x of
       BitEncoding (InputTerminus i) => maybe (NewEncoding $ BitEncoding $ InputTerminus i) (BitEncoding . InputTerminus) $ collateNewEnc i
       BitEncoding (PrimTerminus name h b i) => maybe (NewEncoding $ BitEncoding $ PrimTerminus name h b i) (BitEncoding . PrimTerminus name h b) $ collateNewEnc i
       x' => NewEncoding x'

mutual
  wiresFromPrim
    :  {input : Encodable}
    -> {a : Encodable}
    -> {b : Encodable}
    -> Primitive input a b
    -> State
      (SortedSet Bits64, SortedSet (Wire input output))
      (Encoding (BitType (Terminus input output Bit)) b)
  wiresFromPrim {b} (MkPrimitive name h f x) = do
    when (not $ contains h $ Basics.fst !get) $ do
      modify $ first $ insert h
      assert_total $ wires'' (PrimTerminus name h a) $ collate x
    pure $ map (PrimTerminus name h b) IndexTypes

  wires'
    :  {input : Encodable}
    -> {a : Encodable}
    -> CollatedProducing input a
    -> State
      (SortedSet Bits64, SortedSet (Wire input output))
      (Encoding (Terminus input output) a)
  wires' (BitEncoding (InputBit i)) = pure $ BitEncoding $ InputTerminus i
  wires' (BitEncoding (BitProducedFrom prim i)) = collateTermini . index i <$> wiresFromPrim prim
  wires' UnitEnc = pure UnitEnc
  wires' (x && y) = pure (!(wires' x) && !(wires' y))
  wires' [] = pure []
  wires' (x :: xs) = pure (!(wires' x) :: !(wires' xs))
  wires' (NewEncoding x) = NewEncoding <$> wires' x

  wires''
    :  {input : Encodable}
    -> {a : Encodable}
    -> ({width : Encodable} -> PartialIndex a width -> Terminus input output width)
    -> CollatedProducing input a
    -> State (SortedSet Bits64, SortedSet (Wire input output)) ()
  wires'' f x =
    modify $
      second $
      SortedSet.union $
      SortedSet.fromList $
      map (\(_ ** wire) => wire) $
      SortedSet.toList $
      encodingToSet $
      mapEncodings
        {f = Terminus input output}
        {g = \width => Wire input output}
        (\i, t => MkWire t $ f i)
        !(wires' x)

wires : {a : Encodable} -> {b : Encodable} -> (a ~> b) -> SortedSet (Wire a b)
wires {a} {b} f = snd $ snd $ flip runState (empty, empty) $ wires'' {input = a} {a = b} OutputTerminus $ collate $ f a inputProducing

