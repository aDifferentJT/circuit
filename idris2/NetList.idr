module NetList

import Circuit
import Control.Monad.State
import Data.DPair
import Data.Hash
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import EqOrdUtils
import IndexType
import LinearUtils
import Utils

%default total

public export
NetList : (Encodable -> Encodable -> Type) -> Encodable -> Type
NetList primT input = SortedMap (String, Bits64)
  (  a : Encodable
  ** b : Encodable
  ** ( primT a b
     , Encoding (BitType (Either (IndexType input) Bits64)) a
     , Encoding (BitType Bits64) b
     )
  )

mutual
  netListFromPrim
    :  {a : Encodable}
    -> {b : Encodable}
    -> Primitive primT input a b
    -> State (SortedSet Bits64, NetList primT input) ()
  netListFromPrim prim@(MkPrimitive name h f x) = do
    let output = map (hash . the (ProducingBit primT input Bit) . BitProducedFrom prim) IndexTypes
    when (isNothing $ SortedMap.lookup (name, h) $ snd !get) $ do
      primInput <- netList' x
      modify $ union (encodingBitTypeToSet output) *** insert (name, h) (a ** b ** (f, primInput, output))
  
  netList'
    :  {a : Encodable}
    -> Producing primT input a
    -> State (SortedSet Bits64, NetList primT input) (Encoding (BitType (Either (IndexType input) Bits64)) a)
  netList' {a = Bit} (BitEncoding (MkBitType x)) = do
    relax (BitEncoding . MkBitType) <$> case x of
      InputBit i => pure $ Left i
      BitProducedFrom prim i => do
        netListFromPrim prim
        pure $ Right $ hash x
  netList' UnitEnc = pure UnitEnc
  netList' (x && y) = liftA2 (relax2 $ relax (&&)) (netList' x) (netList' y)
  netList' [] = pure []
  netList' (x :: xs) = liftA2 (relax2 $ relax (::)) (netList' x) (netList' xs)
  netList' (NewEncoding x) = relax NewEncoding <$> netList' x

export
netList
  :  {input : Encodable}
  -> {output : Encodable}
  -> Producing primT input output
  -> ( ( SortedSet Bits64
       , NetList primT input
       )
     , Encoding (BitType (Either (IndexType input) Bits64)) output
     )
netList = runState (empty, empty) . netList'

