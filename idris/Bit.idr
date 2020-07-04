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
fromInteger _ {prf = ItIs0} = B0
fromInteger _ {prf = ItIs1} = B1

export
Hashable BitT where
  saltedHash64 B0 = saltedHash64 (the Int 0)
  saltedHash64 B1 = saltedHash64 (the Int 1)

export
bitNot : BitT -> BitT
bitNot B0 = B1
bitNot B1 = B0



