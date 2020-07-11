module VectProofs

import Data.Vect

%default total

consConcat : (x : a) -> (xs : Vect m a) -> (ys : Vect n a) -> (x :: xs) ++ ys = x :: (xs ++ ys)
consConcat x xs ys = Refl

public export
concatReplicate : (m : Nat) -> (n : Nat) -> (x : a) -> replicate m x ++ replicate n x = replicate (m + n) x
concatReplicate Z _ _ = Refl
concatReplicate (S m) n x = cong (x ::) $ concatReplicate m n x

public export
mapReplicate : (f : a -> b) -> (n : Nat) -> (x : a) -> map f (replicate n x) = replicate n (f x)
mapReplicate _ Z _ = Refl
mapReplicate f (S n) x = cong (f x ::) $ mapReplicate f n x

public export
indexReplicate : (k : Fin n) -> (x : a) -> index k (replicate n x) = x
indexReplicate FZ x = Refl
indexReplicate (FS k) x = indexReplicate k x

