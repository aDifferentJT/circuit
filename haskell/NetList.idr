module NetList

import Circuit
import Control.Monad.State
import Data.Hash
import Data.SortedMap
import Data.Vect
import IndexType
import Utils

%default total

public export
NetListOutput : Encodable -> Encodable -> Type
NetListOutput a b = Encoding (BitType (Either (IndexType a) Bits64)) b

public export
NetList : Encodable -> Type
NetList input = SortedMap (String, Bits64)
  (  a : Encodable
  ** b : Encodable
  ** ( NetListOutput input a
     , Encoding (BitType Bits64) b
     )
  )

mutual
  netListFromPrim : {input : Encodable} -> {a : Encodable} -> {b : Encodable} -> Primitive input a b -> State (NetList input) (NetListOutput input b)
  netListFromPrim prim@(MkPrimitive name h _ x) = do
    let output = map {f = \t => Encoding (BitType t) b} (hash . the (ProducingBit input Bit) . BitProducedFrom prim) IndexTypes
    when (isNothing $ SortedMap.lookup (name, h) !get) $
      modify $
      insert (name, h) (a ** b ** (!(netList' x), output))
    pure $ map {f = \t => Encoding (BitType t) b} Right output
  
  netList' : {input : Encodable} -> {a : Encodable} -> Producing input a -> State (NetList input) (NetListOutput input a)
  netList' {a = Bit} (BitEncoding x) =
    case x of
         InputBit i => pure $ BitEncoding $ Left i
         BitProducedFrom prim i => index i <$> netListFromPrim prim
  netList' UnitEnc = pure UnitEnc
  netList' (x && y) = pure (!(netList' x) && !(netList' y))
  netList' [] = pure []
  netList' (x :: xs) = pure (!(netList' x) :: !(netList' xs))
  netList' (NewEncoding x) = NewEncoding <$> netList' x

export
netList : {a : Encodable} -> {b : Encodable} -> (a ~> b) -> NetList a
netList {a} {b} f = snd $ flip runState empty $ netList' $ inputProducing

