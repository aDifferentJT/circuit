module Circuit

import public Bit
import Control.Monad.State
import public Data.Hash
import Data.SortedMap
import Data.Vect
import Decidable.Equality
import public Encodable
import IndexType
import public WithBitType
import Utils

%default total

public export
PrimType : Encodable -> Type
PrimType = WithBitType BitT

infixr 10 ~~>
public export
(~~>) : Encodable -> Encodable -> Type
a ~~> b = PrimType a -> PrimType b


mutual
  public export
  data Primitive : Encodable -> Encodable -> Encodable -> Type where
    MkPrimitive : String -> Int -> (a ~~> b) -> Producing input a -> Primitive input a b

  public export
  data ProducingBit : Encodable -> Type where
    InputBit : IndexType input -> ProducingBit input
    BitProducedFrom : {a : Encodable} -> {b : Encodable} -> Primitive input a b -> IndexType b -> ProducingBit input

  public export
  Producing : Encodable -> Encodable -> Type
  Producing input = WithBitType (ProducingBit input)


export
{0 input : Encodable} -> Hashable (Primitive input a b) where
  hash (MkPrimitive _ h _ _) = h

export
{input : Encodable} -> Hashable (ProducingBit input) where
  hash (InputBit i) = hash @{HashableIndexType} i
  hash (BitProducedFrom p i) = combineHashes (hash p) (hash @{HashableIndexType} i)

HashableProducing : {input : Encodable} -> {a : Encodable} -> Hashable (Producing input a)
HashableProducing = HashableWithBitType {t = ProducingBit input}


infixr 10 ~>
public export
(~>) : Encodable -> Encodable -> Type
a ~> b = {input : Encodable} -> Producing input a -> Producing input b


export
primitive : {a : Encodable} -> {b : Encodable} -> String -> (a ~~> b) -> {input : Encodable} -> Producing input a -> Producing input b
primitive {a} {b} name f {input} x = mapBits (BitProducedFrom primitive') IndexTypes
  where
    primitive' : Primitive input a b
    primitive' = MkPrimitive name (hash (name, hash @{HashableProducing} x)) f x


export
inputProducing : {input : Encodable} -> Producing input input
inputProducing = mapBits InputBit IndexTypes


mutual
  covering
  runPrimitive' : {input : Encodable} -> {a : Encodable} -> {b : Encodable} -> PrimType input -> Primitive input a b -> State (SortedMap Int (c : Encodable ** PrimType c)) (PrimType b)
  runPrimitive' inputs prim@(MkPrimitive _ _ f' x) = do
    y <- f' <$> simulate' inputs x
    --modify (insert (hash prim) (b ** y))
    pure y

  covering
  runPrimitive : {input : Encodable} -> {a : Encodable} -> {b : Encodable} -> PrimType input -> Primitive input a b -> State (SortedMap Int (c : Encodable ** PrimType c)) (PrimType b)
  runPrimitive inputs prim =
    case Data.SortedMap.lookup (hash prim) !get of
         Just (b' ** xs) => case decEq b b' of
                                 Yes Refl => pure xs
                                 No _ => runPrimitive' inputs prim
         Nothing => runPrimitive' inputs prim

  covering
  simulate' : {input : Encodable} -> {a : Encodable} -> PrimType input -> Producing input a -> State (SortedMap Int (c : Encodable ** PrimType c)) (PrimType a)
  simulate' {a = Bit} inputs (InputBit i) = pure $ bitAt i inputs
  simulate' {a = Bit} inputs (BitProducedFrom prim is) = bitAt is <$> runPrimitive inputs prim
  simulate' {a = _ && _} inputs (x, y) = pure (!(simulate' inputs x), !(simulate' inputs y))
  simulate' {a = EncVect _ _} inputs xs = traverse (simulate' inputs) xs
  simulate' {a = NewEnc _ _} inputs (MkNewType x) = MkNewType <$> simulate' inputs x

covering
export
simulate : {a : Encodable} -> {b : Encodable} -> (a ~> b) -> (a ~~> b)
simulate f inputs = fst $ flip runState empty $ simulate' inputs $ f inputProducing

