module Bit

import Data.Hash

%default total

public export
data Bit = B0 | B1

export
Show Bit where
  show B0 = "0"
  show B1 = "1"

public export
data IsBit : Integer -> Type where
  ItIs0 : IsBit 0
  ItIs1 : IsBit 1

export
fromInteger : (x : Integer) -> {auto prf : IsBit x} -> Bit
fromInteger _ {prf} = fromInteger' prf
  where
    fromInteger' : IsBit x -> Bit
    fromInteger' ItIs0 = B0
    fromInteger' ItIs1 = B1

export
Hashable Bit where
  hash B0 = hash (the Int 0)
  hash B1 = hash (the Int 1)

export
bitNot : Bit -> Bit
bitNot B0 = B1
bitNot B1 = B0

