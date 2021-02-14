module Wires

import AuxProofs
import Circuit
import CollatedProducing
import Control.Monad.State
import Data.Fin
import Data.Hash
import Data.List
import Data.SortedMap
import Data.SortedSet
import Encodable
import Encoding
import EqOrdUtils
import IndexType
import LinearUtils
import Utils

%default total

public export
data Terminus : Encodable -> Encodable -> Encodable -> Type where
  InputTerminus : PartialIndex input width -> Terminus input output width
  OutputTerminus : PartialIndex output width -> Terminus input output width
  PrimTerminus : String -> Bits64 -> (a : Encodable) -> PartialIndex a width -> Terminus input output width

export
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

export
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

export
showIdent : Terminus input output width -> String
showIdent (InputTerminus i) = "in_" ++ showIdent i
showIdent (OutputTerminus i) = "out_" ++ showIdent i
showIdent (PrimTerminus name h a i) = showHashIdent h ++ "_" ++ showIdent i

public export
data Wire : Encodable -> Encodable -> Type where
  MkWire : {width : Encodable} -> Terminus input output width -> Terminus input output width -> Wire input output

export
Eq (Wire input output) where
  (MkWire {width = width} i1 i2) == (MkWire {width = width'} i1' i2') =
    case decEq width width' of
         Yes Refl => i1 == i1' && i2 == i2'
         No _ => False

export
Ord (Wire input output) where
  compare (MkWire {width = width} i1 i2) (MkWire {width = width'} i1' i2') =
    case decEq width width' of
         Yes Refl => thenCompare (compare i1 i1') (compare i2 i2')
         No _ => compare width width'

export
collateTermini : Encoding (BitType (Terminus input output Bit)) a -> Encoding (Terminus input output) a
collateTermini (BitEncoding x) = BitEncoding $ removeBitType (Terminus input output) x
collateTermini UnitEnc = UnitEnc
collateTermini (x && y) =
  case (collateTermini x, collateTermini y) of
       (BitEncoding (InputTerminus i1), BitEncoding (InputTerminus i2)) => maybe (BitEncoding (InputTerminus i1) && BitEncoding (InputTerminus i2)) (relax BitEncoding . InputTerminus) $ collatePair i1 i2
       (BitEncoding (PrimTerminus name1 h1 b1 i1), BitEncoding (PrimTerminus name2 h2 b2 i2)) =>
         case (h1 == h2, decEq b1 b2) of
              (True, Yes Refl) => maybe (BitEncoding (PrimTerminus name1 h1 b1 i1) && BitEncoding (PrimTerminus name2 h2 b2 i2)) (relax BitEncoding . PrimTerminus name1 h1 b1) $ collatePair i1 i2
              _ => BitEncoding (PrimTerminus name1 h1 b1 i1) && BitEncoding (PrimTerminus name2 h2 b2 i2)
       (x, y) => x && y
collateTermini [] = []
collateTermini (x :: xs) =
  case (collateTermini x, collateTermini xs) of
       (BitEncoding (InputTerminus i1), BitEncoding (InputTerminus i2)) => maybe (BitEncoding (InputTerminus i1) :: BitEncoding (InputTerminus i2)) (relax BitEncoding . InputTerminus) $ collateVect i1 i2
       (BitEncoding (PrimTerminus name1 h1 b1 i1), BitEncoding (PrimTerminus name2 h2 b2 i2)) =>
         case (h1 == h2, decEq b1 b2) of
              (True, Yes Refl) => maybe (BitEncoding (PrimTerminus name1 h1 b1 i1) :: BitEncoding (PrimTerminus name2 h2 b2 i2)) (relax BitEncoding . PrimTerminus name1 h1 b1) $ collateVect i1 i2
              _ => BitEncoding (PrimTerminus name1 h1 b1 i1) :: BitEncoding (PrimTerminus name2 h2 b2 i2)
       (x, y) => x :: y
collateTermini (NewEncoding x) =
  case collateTermini x of
       BitEncoding (InputTerminus i) => maybe (NewEncoding $ BitEncoding $ InputTerminus i) (relax BitEncoding . InputTerminus) $ collateNewEnc i
       BitEncoding (PrimTerminus name h b i) => maybe (NewEncoding $ BitEncoding $ PrimTerminus name h b i) (relax BitEncoding . PrimTerminus name h b) $ collateNewEnc i
       x' => NewEncoding x'

mutual
  wiresFromPrim
    :  {input : Encodable}
    -> {a : Encodable}
    -> {b : Encodable}
    -> Primitive prim input a b
    -> State
      ( SortedMap Bits64
        (  a' : Encodable
        ** b' : Encodable
        ** Primitive prim input a' b'
        )
      , SortedSet (Wire input output)
      )
      (Encoding (BitType (Terminus input output Bit)) b)
  wiresFromPrim p@(MkPrimitive name h f x) = do
    when (isNothing $ lookup h $ fst !get) $ do
      modify $ first $ insert h (a ** b ** p)
      assert_total $ wires'' (PrimTerminus name h a) $ collate x
    pure $ map (PrimTerminus name h b) IndexTypes

  wires'
    :  {input : Encodable}
    -> {a : Encodable}
    -> CollatedProducing prim input a
    -> State
      ( SortedMap Bits64
        (  a' : Encodable
        ** b' : Encodable
        ** Primitive prim input a' b'
        )
      , SortedSet (Wire input output)
      )
      (Encoding (Terminus input output) a)
  wires' (BitEncoding (InputBit i)) = pure $ BitEncoding $ InputTerminus i
  wires' (BitEncoding (BitProducedFrom prim i)) = collateTermini . index i <$> wiresFromPrim prim
  wires' UnitEnc = pure UnitEnc
  wires' (x && y) = pure (!(wires' x) && !(wires' y))
  wires' [] = pure []
  wires' (x :: xs) = pure (!(wires' x) :: !(wires' xs))
  wires' (NewEncoding x) = relax NewEncoding <$> wires' x

  wires''
    :  {input : Encodable}
    -> {a : Encodable}
    -> ({0 width : Encodable} -> PartialIndex a width -> Terminus input output width)
    -> CollatedProducing prim input a
    -> State
      ( SortedMap Bits64
        (  a' : Encodable
        ** b' : Encodable
        ** Primitive prim input a' b'
        )
      , SortedSet (Wire input output)
      )
      ()
  wires'' f x =
    modify $
      second $
      SortedSet.union $
      encodingToSet $
      mapEncodings
        {f = Terminus input output}
        {g = \width => Wire input output}
        (\i, t => MkWire t $ f i)
        !(wires' x)

export
wires
  :  {input : Encodable}
  -> {output : Encodable}
  -> Producing prim input output
  -> ( SortedMap Bits64
       (  a' : Encodable
       ** b' : Encodable
       ** Primitive prim input a' b'
       )
     , SortedSet (Wire input output)
     )
wires = fst . runState (empty, empty) . wires'' OutputTerminus . collate

