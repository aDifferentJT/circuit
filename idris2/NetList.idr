module NetList

import Circuit
import Control.Monad.State
import Data.SortedMap
import Data.Vect
import IndexType
import Utils

%default total

public export
NetListOutput : Encodable -> Encodable -> Type
NetListOutput a b = WithBitType (Either (IndexType a) Int) b

public export
NetList : Encodable -> Type
NetList input = SortedMap (String, Int)
  (  a : Encodable
  ** b : Encodable
  ** ( NetListOutput input a
     , WithBitType Int b
     )
  )

mutual
  netListFromPrim : {input : Encodable} -> {a : Encodable} -> {b : Encodable} -> Primitive input a b -> State (NetList input) (NetListOutput input b)
  netListFromPrim prim@(MkPrimitive name h _ x) = do
    let output = mapBits (hash . BitProducedFrom prim) $ IndexTypes {a = b}
    when (isNothing $ SortedMap.lookup (name, h) !get) $
      modify $
      insert (name, h) (a ** b ** (!(netList' x), output))
    pure $ mapBits Right output
  
  netList' : {input : Encodable} -> {a : Encodable} -> Producing input a -> State (NetList input) (NetListOutput input a)
  netList' {a = Bit} (InputBit i) = pure $ Left i
  netList' {a = Bit} (BitProducedFrom prim i) =
    bitAt i <$> netListFromPrim prim
  netList' {a = a1 && a2} (x, y) =
    pure (!(netList' {a = a1} x), !(netList' {a = a2} y))
  netList' {a = EncVect _ a} xs = traverse (\x => netList' {a} $ assert_smaller xs x) xs
  netList' {a = NewEnc _ a} (MkNewType x) = MkNewType <$> netList' {a} x

export
netList : {a : Encodable} -> {b : Encodable} -> (a ~> b) -> NetList a
netList {a} {b} f = snd $ flip runState empty $ netList' $ inputProducing

