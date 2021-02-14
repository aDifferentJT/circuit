module Data.Hash

import Bit
import Data.LVect
import Data.Nat
import Data.Vect
import LinearUtils
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
    mask = prim__shl_Bits64 0xff offset

export
addSalt : Bits64 -> Bits64 -> Bits64
addSalt salt x = foldr (\b,acc => (acc `prim__shl_Bits64` 10) + acc + b) salt [byte (fromInteger n) x | n <- [7,6..0]]

linearSHL : (1 _ : LVect 64 Bit) -> Nat -> LVect 64 Bit
linearSHL bs n = drop n (linearRewrite (\m => LVect m Bit) (plusCommutative n 64) $ bs ++ (vectToLVect $ replicate n 0))

linearSHR : (1 _ : LVect 64 Bit) -> Nat -> LVect 64 Bit
linearSHR bs n = take 64 (linearRewrite (\m => LVect m Bit) (plusCommutative 64 n) $ (vectToLVect $ replicate n 0) ++ bs)

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
Hashable Nat where
  hash n = hash $ the Integer $ cast n

export
Hashable Char where
  hash = hash . ord

export
Hashable Bit where
  hash B0 = hash (the Int 0)
  hash B1 = hash (the Int 1)

export
(Hashable a, Hashable b) => Hashable (a, b) where
  hash (x, y) = addSalt (hash x) (hash y)

export
Hashable a => Hashable (Maybe a) where
  hash Nothing = hash ()
  hash (Just x) = hash x

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

