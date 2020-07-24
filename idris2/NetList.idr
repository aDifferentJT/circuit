module NetList

import Circuit
import Control.Monad.State
import Data.Hash
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import EqOrdUtils
import IndexType
import Utils

%default total

public export
NetList : Encodable -> Type
NetList input = SortedMap (String, Bits64)
  (  a : Encodable
  ** b : Encodable
  ** ( Encoding (BitType Bit) a -> Encoding (BitType Bit) b
     , Encoding (BitType (Either (IndexType input) Bits64)) a
     , Encoding (BitType Bits64) b
     )
  )

mutual
  netListFromPrim : {input : Encodable} -> {a : Encodable} -> {b : Encodable} -> Primitive input a b -> State (SortedSet Bits64, NetList input) ()
  netListFromPrim prim@(MkPrimitive name h f x) = do
    let output = map (hash . the (ProducingBit input Bit) . BitProducedFrom prim) IndexTypes
    when (isNothing $ SortedMap.lookup (name, h) $ snd !get) $ do
      primInput <- netList' x
      modify $ union (encodingToSet output) *** insert (name, h) (a ** b ** (f, primInput, output))
  
  netList'
    :  {input : Encodable}
    -> {a : Encodable}
    -> Producing input a
    -> State (SortedSet Bits64, NetList input) (Encoding (BitType (Either (IndexType input) Bits64)) a)
  netList' {a = Bit} (BitEncoding x) = do
    BitEncoding <$> case x of
                         InputBit i => pure $ Left i
                         BitProducedFrom prim i => do
                           netListFromPrim prim
                           pure $ Right $ hash x
  netList' UnitEnc = pure UnitEnc
  netList' (x && y) = pure (!(netList' x) && !(netList' y))
  netList' [] = pure []
  netList' (x :: xs) = pure (!(netList' x) :: !(netList' xs))
  netList' (NewEncoding x) = NewEncoding <$> netList' x

fromRight : Either a b -> Maybe b

export
netList
  :  {input : Encodable}
  -> {output : Encodable}
  -> Producing input output
  -> ( Encoding (BitType (Either (IndexType input) Bits64)) output
     , SortedSet Bits64
     , NetList input
     )
netList x = runState (netList' x) (empty, empty)

