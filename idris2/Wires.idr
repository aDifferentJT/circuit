module Wires

import AuxProofs
import Circuit
import CollatedEncoding
import CollatedProducing
import Control.Monad.State
import Data.Fin
import Data.List
import Data.SortedSet
import Encodable
import EqOrdUtils
import PartialIndex
import Utils
import WithBitType

%default total

data Terminus : Encodable -> Encodable -> Encodable -> Type where
  InputTerminus : PartialIndex input width -> Terminus input output width
  OutputTerminus : PartialIndex output width -> Terminus input output width
  PrimTerminus : String -> Int -> (a : Encodable) -> PartialIndex a width -> Terminus input output width

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

extractTermini : Vect (S n) (CollatedEncoding (Terminus input output) width) -> Maybe (Either (Vect (S n) (PartialIndex input width)) (Vect (S n) ((String, Int), (a : Encodable ** PartialIndex a width))))
extractTermini [CollatedBit (InputTerminus i)] = Just $ Left [i]
extractTermini [CollatedBit (PrimTerminus name h a i)] = Just $ Right [((name, h), (a ** i))]
extractTermini [_] = Nothing
extractTermini (x :: xs@(_ :: _)) =
  case (x, extractTermini xs) of
       (CollatedBit (InputTerminus i), Just (Left is)) => Just $ Left $ i :: is
       (CollatedBit (PrimTerminus name h a i), Just (Right ys)) => Just $ Right $ ((name, h), (a ** i)) :: ys
       _ => Nothing

collateTermini : {input : Encodable} -> {a : Encodable} -> WithBitType (Terminus input output Bit) a -> CollatedEncoding (Terminus input output) a
collateTermini {a = Bit} x = CollatedBit x
collateTermini {a = a1 && a2} (x, y) =
  case (collateTermini x, collateTermini y) of
       (CollatedBit (InputTerminus i1), CollatedBit (InputTerminus i2)) => maybe (CollatedBit (InputTerminus i1) && CollatedBit (InputTerminus i2)) (CollatedBit . InputTerminus) $ collatePair i1 i2
       (CollatedBit (PrimTerminus name1 h1 b1 i1), CollatedBit (PrimTerminus name2 h2 b2 i2)) =>
         case (h1 == h2, decEq b1 b2) of
              (True, Yes Refl) => maybe (CollatedBit (PrimTerminus name1 h1 b1 i1) && CollatedBit (PrimTerminus name2 h2 b2 i2)) (CollatedBit . PrimTerminus name1 h1 b1) $ collatePair i1 i2
              _ => CollatedBit (PrimTerminus name1 h1 b1 i1) && CollatedBit (PrimTerminus name2 h2 b2 i2)
       (x, y) => x && y
collateTermini {a = EncVect Z a} xs = CollatedVect []
collateTermini {a = EncVect (S n) a} xs =
  case map collateTermini xs of
       ts => case extractTermini ts of
                  Just (Left is) => case collateVect is of
                                         Nothing => CollatedVect ts
                                         Just i => CollatedBit $ InputTerminus i
                  Just (Right ys) => case nub $ toList $ map fst ys of
                                          [(name, h)] => case decEqVectDPair $ map snd ys of
                                                              Nothing => CollatedVect ts
                                                              Just (b ** is) => case collateVect is of
                                                                                     Nothing => CollatedVect ts
                                                                                     Just i => CollatedBit $ PrimTerminus name h b i
                                          _ => CollatedVect ts
                  Nothing => CollatedVect ts
collateTermini {input} {a = NewEnc ident a} (MkNewType x) =
  case collateTermini x of
       CollatedBit (InputTerminus i) => case collateNewEnc i of
                                             Nothing => CollatedNewEnc $ CollatedBit $ InputTerminus i
                                             Just i' => CollatedBit $ InputTerminus i'
       CollatedBit (PrimTerminus name h b i) => case collateNewEnc i of
                                                     Nothing => CollatedNewEnc $ CollatedBit $ PrimTerminus name h b i
                                                     Just i' => CollatedBit $ PrimTerminus name h b i'
       x' => CollatedNewEnc x'

mutual
  wiresFromPrim
    :  {input : Encodable}
    -> {a : Encodable}
    -> {b : Encodable}
    -> Primitive input a b
    -> State
      (SortedSet Int, SortedSet (Wire input output))
      (WithBitType (Terminus input output Bit) b)
  wiresFromPrim (MkPrimitive name h f x) = do
    when (not $ contains h $ fst !get) $ do
      modify $ first $ insert h
      assert_total $ wires'' (\width => PrimTerminus name h a) $ collate x
    pure $ mapBits (PrimTerminus name h b . partialFromIndex) IndexTypes

  wires'
    :  {input : Encodable}
    -> {a : Encodable}
    -> CollatedProducing input a
    -> State
      (SortedSet Int, SortedSet (Wire input output))
      (CollatedEncoding (Terminus input output) a)
  wires' (Input i) = pure $ CollatedBit $ InputTerminus i
  wires' (ProducedFrom prim i) = collateTermini . partialIndex i <$> wiresFromPrim prim
  wires' {a = a1 && a2} (x && y) = pure (!(wires' x) && !(wires' y))
  wires' {a = EncVect _ a} (ProdVect xs) = CollatedVect <$> traverse wires' xs
  wires' {a = NewEnc _ a} (ProdNewEnc x) = CollatedNewEnc <$> wires' x

  wires'' : {input : Encodable} -> {a : Encodable} -> ((width : Encodable) -> PartialIndex a width -> Terminus input output width) -> CollatedProducing input a -> State (SortedSet Int, SortedSet (Wire input output)) ()
  wires'' f x =
    modify $
      second $
      SortedSet.union $
      SortedSet.fromList $
      map (\(_ ** wire) => wire) $
      SortedSet.toList $
      partialEncodingToSet $
      mapCollatedEncoding
        {f = Terminus input output}
        {g = \width => Wire input output}
        (\width, i, t => MkWire t $ f width i)
        !(wires' x)

wires : {a : Encodable} -> {b : Encodable} -> (a ~> b) -> SortedSet (Wire a b)
wires f = snd $ snd $ flip runState (empty, empty) $ wires'' {input = a} {a = b} (\width => OutputTerminus) $ collate $ f inputProducing -- TODO this should use f

