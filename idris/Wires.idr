module Wires

import AuxProofs
import Circuit
import CollatedEncoding
import CollatedProducing
import Control.Monad.State
import Data.Fin
import Data.SortedSet
import Encodable
import EqOrdUtils
import PartialIndex
import Utils
import WithBitType

%default total

data Terminus : Encodable -> Encodable -> Type where
  InputTerminus : PartialIndex input width -> Terminus input width
  PrimTerminus : String -> Bits64 -> (a : Encodable) -> PartialIndex a width -> Terminus input width

Eq (Terminus input width) where
  (InputTerminus i1) == (InputTerminus i2) = (==) @{EqPartialIndex input width} i1 i2
  (PrimTerminus _ h1 a1 i1) == (PrimTerminus _ h2 a2 i2) with (decEq a1 a2)
    (PrimTerminus _ h1 a i1) == (PrimTerminus _ h2 a i2) | Yes Refl = h1 == h2 && (==) @{EqPartialIndex a width} i1 i2
    | No _ = False
  (InputTerminus _) == (PrimTerminus _ _ _ _) = False
  (PrimTerminus _ _ _ _) == (InputTerminus _) = False

Ord (Terminus input width) where
  compare (InputTerminus i1) (InputTerminus i2) = compare @{OrdPartialIndex input width} i1 i2
  compare (PrimTerminus _ h1 a1 i1) (PrimTerminus _ h2 a2 i2) with (decEq a1 a2)
    compare (PrimTerminus _ h1 a i1) (PrimTerminus _ h2 a i2) | Yes Refl = thenCompare (compare h1 h2) (compare @{OrdPartialIndex a width} i1 i2)
    | No _ = compare a1 a2
  compare (InputTerminus _) (PrimTerminus _ _ _ _) = LT
  compare (PrimTerminus _ _ _ _) (InputTerminus _) = GT

mapTerminus : ((a : Encodable) -> PartialIndex a width1 -> PartialIndex a width2) -> Terminus input width1 -> Terminus input width2
mapTerminus f {input} (InputTerminus i) = InputTerminus $ f input i
mapTerminus f (PrimTerminus name h a i) = PrimTerminus name h a $ f a i

data Wire : Encodable -> Type where
  MkWire : Terminus input width -> Terminus input width -> Wire input

Eq (Wire input) where
  (MkWire {width = width} i1 i2) == (MkWire {width = width'} i1' i2') with (decEq width width')
    (MkWire {width} i1 i2) == (MkWire {width} i1' i2') | Yes Refl = i1 == i1' && i2 == i2'
    | No _ = False

Ord (Wire input) where
  compare (MkWire {width = width} i1 i2) (MkWire {width = width'} i1' i2') with (decEq width width')
    compare (MkWire {width} i1 i2) (MkWire {width} i1' i2') | Yes Refl =
      thenCompare (compare i1 i1') (compare i2 i2')
    | No _ = compare width width'

extractTermini : Vect (S n) (CollatedEncoding (Terminus input) width) -> Maybe (Either (Vect (S n) (PartialIndex input width)) (Vect (S n) ((String, Bits64), (a : Encodable ** PartialIndex a width))))
extractTermini [CollatedBit (InputTerminus i)] = Just $ Left [i]
extractTermini [CollatedBit (PrimTerminus name h a i)] = Just $ Right [((name, h), (a ** i))]
extractTermini [_] = Nothing
extractTermini {n = S _} (x :: xs) with (extractTermini xs)
  extractTermini (CollatedBit (InputTerminus i) :: _) | Just (Left is) = Just $ Left $ i :: is
  extractTermini (CollatedBit (PrimTerminus name h a i) :: _) | Just (Right ys) = Just $ Right $ ((name, h), (a ** i)) :: ys
  | _ = Nothing

collateTermini : WithBitType (Terminus input Bit) a -> CollatedEncoding (Terminus input) a
collateTermini {a = Bit} x = CollatedBit x
collateTermini {input} {a = a1 & a2} (x, y) with (collateTermini x, collateTermini y)
  collateTermini {input} {a = a1 & a2} _ | (CollatedBit (InputTerminus i1), CollatedBit (InputTerminus i2)) with (collatePair input a1 a2 i1 i2)
    | Nothing = CollatedBit (InputTerminus i1) && CollatedBit (InputTerminus i2)
    | Just i = CollatedBit $ InputTerminus i
  collateTermini {a = a1 & a2} _ | (CollatedBit (PrimTerminus name1 h1 b1 i1), CollatedBit (PrimTerminus name2 h2 b2 i2)) with (h1 == h2, decEq b1 b2)
    collateTermini {a = a1 & a2} _ | (CollatedBit (PrimTerminus name h b i1), CollatedBit (PrimTerminus _ _ b i2)) | (True, Yes Refl) with (collatePair b a1 a2 i1 i2)
      | Nothing = CollatedBit (PrimTerminus name h b i1) && CollatedBit (PrimTerminus name h b i2)
      | Just i = CollatedBit $ PrimTerminus name h b i
    | _ = CollatedBit (PrimTerminus name1 h1 b1 i1) && CollatedBit (PrimTerminus name2 h2 b2 i2)
  collateTermini _ | (x, y) = x && y
collateTermini {a = EncVect Z a} xs = CollatedVect []
collateTermini {input} {a = EncVect (S n) a} xs with (map collateTermini xs)
  | ts with (extractTermini ts)
    | Just (Left is) with (collateVect input (S n) a is)
      | Nothing = CollatedVect ts
      | Just i = CollatedBit $ InputTerminus i
    | Just (Right ys) with (removeDuplicates $ toList $ map fst ys)
      | [(name, h)] with (decEqVectDPair $ map snd ys)
        | Nothing = CollatedVect ts
        | Just (b ** is) with (collateVect b (S n) a is)
          | Nothing = CollatedVect ts
          | Just i = CollatedBit $ PrimTerminus name h b i
      | _ = CollatedVect ts
    | Nothing = CollatedVect ts
collateTermini {input} {a = NewEnc ident a} (MkNewType x) with (collateTermini x)
  | CollatedBit (InputTerminus i) with (collateNewEnc input ident a i)
    | Nothing = CollatedNewEnc $ CollatedBit $ InputTerminus i
    | Just i' = CollatedBit $ InputTerminus i'
  | CollatedBit (PrimTerminus name h b i) with (collateNewEnc b ident a i)
    | Nothing = CollatedNewEnc $ CollatedBit $ PrimTerminus name h b i
    | Just i' = CollatedBit $ PrimTerminus name h b i'
  | x' = CollatedNewEnc x'

mutual
  wiresFromPrim
    : Primitive input a b
    -> State
      (SortedSet Bits64, SortedSet (Wire input))
      (WithBitType (Terminus input Bit) b)
  wiresFromPrim {input} {a} {b} (MkPrimitive name h f x) = do
    when (not $ contains h $ Basics.fst !get) $ do
      modify $ first $ insert h
      assert_total $ wires'' (\width => PrimTerminus name h a) $ collate x
    pure $ mapBits (PrimTerminus name h b . partialFromIndex) IndexTypes

  wires'
    :  CollatedProducing input a
    -> State
      (SortedSet Bits64, SortedSet (Wire input))
      (CollatedEncoding (Terminus input) a)
  wires' (Input i) = pure $ CollatedBit $ InputTerminus i
  wires' (ProducedFrom prim i) = collateTermini . partialIndex i <$> wiresFromPrim prim
  wires' {a = a1 & a2} (x && y) = pure (!(wires' x) && !(wires' y))
  wires' {a = EncVect _ a} (ProdVect xs) = CollatedVect <$> traverse wires' xs
  wires' {a = NewEnc _ a} (ProdNewEnc x) = CollatedNewEnc <$> wires' x

  wires'' : ((width : Encodable) -> PartialIndex a width -> Terminus input width) -> CollatedProducing input a -> State (SortedSet Bits64, SortedSet (Wire input)) ()
  wires'' f x =
    modify $
      second $
      SortedSet.union $
      SortedSet.fromList $
      map (\(_ ** wire) => wire) $
      SortedSet.toList $
      partialEncodingToSet $
      mapCollatedEncoding
        {f = Terminus input}
        {g = \width => Wire input}
        (\width, i, t => MkWire t $ f width i)
        !(wires' x)

wires : (a ~> b) -> SortedSet (Wire a)
wires f = snd $ snd $ flip runState (empty, empty) $ wires'' (\width => InputTerminus) $ collate $ inputProducing

