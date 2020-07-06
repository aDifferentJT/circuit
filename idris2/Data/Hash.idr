module Data.Hash

import Data.Vect
import Utils

%default total

public export
interface Hashable a where
  hash : a -> Bits64

salt : Bits64
salt = 0x16fc397cf62f64d3

byte : Bits64 -> Bits64 -> Bits64
byte n w = prim__shr_Bits64 (prim__and_Bits64 mask w) offset
  where
    offset : Bits64
    offset = 8 * n
    mask : Bits64
    mask = prim__shl_Bits64 0xff (the Bits64 offset)

export
addSalt : Bits64 -> Bits64 -> Bits64
addSalt salt x = foldr (\b,acc => (acc `prim__shl_Bits64` 10) + acc + b) salt [byte (fromInteger n) x | n <- [7,6..0]]

export
Hashable () where
  hash () = salt

export
Hashable Bits64 where
  hash = addSalt salt

export
Hashable Integer where
  hash n = hash $ the Bits64 $ fromInteger n

export
Hashable Int where
  hash n = hash $ the Integer $ cast n

export
Hashable Char where
  hash = hash . ord

export
(Hashable a, Hashable b) => Hashable (a, b) where
  hash (x, y) = addSalt (hash x) (hash y)

export
Hashable a => Hashable (Vect n a) where
  hash [] = salt
  hash (x :: xs) = addSalt (hash x) (hash xs)

export
Hashable a => Hashable (List a) where
  hash [] = salt
  hash (x :: xs) = addSalt (hash x) (hash xs)

export
HashableVect : Hashable a -> Hashable (Vect n a)
HashableVect _ = autoDer

export
Hashable String where
  hash = hash . unpack

