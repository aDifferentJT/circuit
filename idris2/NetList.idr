module NetList

import Circuit
import Control.Monad.State
import Data.Hash
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import IndexType
import Utils

%default total

public export
NetList : Type
NetList = SortedMap (String, Bits64)
  (  a : Encodable
  ** b : Encodable
  ** ( Encoding (BitType Bit) a -> Encoding (BitType Bit) b
     , Encoding (BitType Bits64) a
     , Encoding (BitType Bits64) b
     )
  )

encodingToSet : Ord t => {a : Encodable} -> Encoding (BitType t) a -> SortedSet t
encodingToSet {a = Bit} (BitEncoding x) = fromList [x]
encodingToSet UnitEnc = empty
encodingToSet (x && y) = encodingToSet x `union` encodingToSet y
encodingToSet [] = empty
encodingToSet (x :: xs) = encodingToSet x `union` encodingToSet xs
encodingToSet (NewEncoding x) = encodingToSet x

mutual
  netListFromPrim : {input : Encodable} -> {a : Encodable} -> {b : Encodable} -> Primitive input a b -> State (SortedSet Bits64, NetList) ()
  netListFromPrim prim@(MkPrimitive name h f x) = do
    let output = map (hash . the (ProducingBit input Bit) . BitProducedFrom prim) IndexTypes
    when (isNothing $ SortedMap.lookup (name, h) $ snd !get) $ do
      primInput <- netList' x
      modify $ union (encodingToSet output) *** insert (name, h) (a ** b ** (f, primInput, output))
  
  netList' : {input : Encodable} -> {a : Encodable} -> Producing input a -> State (SortedSet Bits64, NetList) (Encoding (BitType Bits64) a)
  netList' {a = Bit} (BitEncoding x) = do
    case x of
         InputBit i => pure ()
         BitProducedFrom prim i => netListFromPrim prim
    pure $ BitEncoding $ hash x
  netList' UnitEnc = pure UnitEnc
  netList' (x && y) = pure (!(netList' x) && !(netList' y))
  netList' [] = pure []
  netList' (x :: xs) = pure (!(netList' x) :: !(netList' xs))
  netList' (NewEncoding x) = NewEncoding <$> netList' x

export
netList
  :  {input : Encodable}
  -> {output : Encodable}
  -> Producing input output
  -> ( Encoding (BitType Bits64) input
     , SortedSet Bits64
     , Encoding (BitType Bits64) output
     , NetList
     )
netList x =
  let (outputBits, internalBits, nl) = runState (netList' x) (empty, empty) in
      ( map (hash . the (ProducingBit input Bit) . InputBit) IndexTypes
      , internalBits `difference` encodingToSet outputBits
      , outputBits
      , nl
      )

