module Analytics

import Circuit
import Control.Monad.State
import Data.SortedMap

%default total

public export
record Analytics where
  constructor MkAnalytics
  size : Nat
  depth : Nat

export
Show Analytics where
  show (MkAnalytics size depth) = "Size: " ++ show size ++ ", Depth: " ++ show depth

merge : Analytics -> Analytics -> Analytics
merge (MkAnalytics size1 depth1) (MkAnalytics size2 depth2) = MkAnalytics (size1 + size2) (max depth1 depth2)

analytics' : Producing prim input a -> State (SortedMap Bits64 Nat) Analytics
analytics' (BitEncoding (MkBitType x)) =
  case x of
       InputBit _ => pure $ MkAnalytics 0 0
       BitProducedFrom (MkPrimitive _ h _ y) _ =>
         maybe
           (do
             MkAnalytics size depth <- analytics' y
             modify $ insert h $ S depth
             pure $ MkAnalytics (S size) (S depth)
           )
           (pure . MkAnalytics Z) $
           lookup h !get
analytics' UnitEnc = pure $ MkAnalytics 0 0
analytics' (x && y) = pure $ merge !(analytics' x) !(analytics' y)
analytics' [] = pure $ MkAnalytics 0 0
analytics' (x :: xs) = pure $ merge !(analytics' x) !(analytics' xs)
analytics' (NewEncoding x) = analytics' x

export
analytics : Producing prim input a -> Analytics
analytics = snd . runState empty . analytics'

