module NetList

import Circuit
import Control.Monad.State
import Data.Hash
import Data.SortedSet
import Data.SortedMap
import Data.Vect
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
  netListFromPrim
    :  {input : Encodable}
    -> {a : Encodable}
    -> {b : Encodable}
    -> Primitive input a b
    -> State (SortedSet Bits64, NetList input) ()
  netListFromPrim {b} prim@(MkPrimitive name h f x) = do
    let output = map (hash . BitProducedFrom prim) $ IndexTypes {a = b}
    when (isNothing $ SortedMap.lookup (name, h) $ snd !get) $ do
      primInput <- netList' {input} x
      modify $ SortedSet.union (encodingToSet output) *** SortedMap.insert (name, h) (a ** b ** (f, primInput, output))
  
  netList'
    :  {input : Encodable}
    -> {a : Encodable}
    -> Producing input a
    -> State (SortedSet Bits64, NetList input) (Encoding (BitType (Either (IndexType input) Bits64)) a)
  netList' {a = Bit} (BitEncoding x) =
    BitEncoding <$> case x of
                         InputBit i => pure $ Left i
                         BitProducedFrom prim i => do
                           assert_total $ netListFromPrim prim
                           pure $ Right $ hash x
  netList' UnitEnc = pure UnitEnc
  netList' (x && y) = liftA2 (&&) (netList' x) (netList' y)
  netList' [] = pure []
  netList' (x :: xs) = liftA2 (::) (netList' x) (netList' xs)
  netList' (NewEncoding x) = NewEncoding <$> netList' x

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

