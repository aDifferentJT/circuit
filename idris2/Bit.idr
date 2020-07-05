module Bit

import Data.Hash

%default total

public export
data BitT = B0 | B1

export
Show BitT where
  show B0 = "0"
  show B1 = "1"

public export
data IsBit : Integer -> Type where
  ItIs0 : IsBit 0
  ItIs1 : IsBit 1

export
fromInteger : (x : Integer) -> {auto prf : IsBit x} -> BitT
fromInteger _ {prf} = fromInteger' prf
  where
    fromInteger' : IsBit x -> BitT
    fromInteger' ItIs0 = B0
    fromInteger' ItIs1 = B1

export
Hashable BitT where
  hash B0 = hash (the Int 0)
  hash B1 = hash (the Int 1)

export
bitNot : BitT -> BitT
bitNot B0 = B1
bitNot B1 = B0



