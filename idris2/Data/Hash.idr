module Data.Hash

import Data.Vect
import Utils

%default total

public export
interface Hashable a where
  hash : a -> Int

export
combineHashes : Int -> Int -> Int
combineHashes = (*)

export
Hashable () where
  hash () = 0

export
Hashable Int where
  hash n = n

export
Hashable Integer where
  hash n = cast n

export
Hashable Char where
  hash = hash . ord

export
(Hashable a, Hashable b) => Hashable (a, b) where
  hash (x, y) = combineHashes (hash x) (hash y)

export
Hashable a => Hashable (Vect n a) where
  hash [] = hash ()
  hash (x :: xs) = combineHashes (hash x) (hash xs)

export
Hashable a => Hashable (List a) where
  hash [] = hash ()
  hash (x :: xs) = combineHashes (hash x) (hash xs)

export
HashableVect : Hashable a -> Hashable (Vect n a)
HashableVect _ = autoDer

export
Hashable String where
  hash = hash . unpack

