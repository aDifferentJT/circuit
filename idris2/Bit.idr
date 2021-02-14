module Bit

import LinearUtils

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
bitNot : (1 _ : Bit) -> Bit
bitNot B0 = B1
bitNot B1 = B0

public export
Discard Bit where
  discard B0 = ()
  discard B1 = ()

public export
Dup Bit where
  dup B0 = B0 # B0
  dup B1 = B1 # B1

  release B0 = MkUnrestricted B0
  release B1 = MkUnrestricted B1

