
import Analytics
import Circuit
import CommandLine
import Data.List
import Data.LVect
import Data.Nat
import Data.Stream
import Data.Vect
import IndexType
import JSON
import NatProofs
import Utils
import ZXCircuit

%default total

zSpider : {n : Nat} -> {m : Nat} -> (0 input : Encodable) -> (1 _ : LVect n (QBit input)) -> LVect m (QBit input)
zSpider input = zxPrimitive "Z" Z input

main : IO ()
main = do
  print $ toQGraph $ linearConstructProducing $ zSpider {n = 2} {m = 2}

