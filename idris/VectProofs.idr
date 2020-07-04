module VectProofs

import Data.Vect

%access public export
%default total

private
consConcat : (x : a) -> (xs : Vect m a) -> (ys : Vect n a) -> (x :: xs) ++ ys = x :: (xs ++ ys)
consConcat x xs ys = Refl

concatReplicate : (m : Nat) -> (n : Nat) -> (x : a) -> Data.Vect.replicate m x ++ replicate n x = replicate (m + n) x
concatReplicate Z _ _ = Refl
concatReplicate (S m) n x = cong $ concatReplicate m n x

mapReplicate : (f : a -> b) -> (n : Nat) -> (x : a) -> map f (Vect.replicate n x) = Vect.replicate n (f x)
mapReplicate _ Z _ = Refl
mapReplicate f (S n) x = cong $ mapReplicate f n x

indexReplicate : (k : Fin n) -> (x : a) -> index k (replicate n x) = x
indexReplicate FZ x = Refl
indexReplicate (FS k) x = indexReplicate k x

