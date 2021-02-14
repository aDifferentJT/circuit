module Data.LVect

import Data.Fin
import Data.Nat
import Data.Vect
import LinearUtils
import Utils

public export
data LVect : Nat -> Type -> Type where
  Nil : LVect Z a
  (::) : (1 _ : a) -> (1 _ : LVect n a) -> LVect (S n) a

public export
Discard a => Discard (LVect n a) where
  discard [] = ()
  discard (x :: xs) = let () = discard x in discard xs

public export
vectToLVect : Vect n a -> LVect n a
vectToLVect [] = []
vectToLVect (x :: xs) = x :: vectToLVect xs

public export
lVectToVect : LVect n a -> Vect n a
lVectToVect [] = []
lVectToVect (x :: xs) = x :: lVectToVect xs

public export
Functor (LVect n) where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

public export
head : LVect (S n) a -> a
head (x :: _) = x

public export
tail : LVect (S n) a -> LVect n a
tail (_ :: xs) = xs

public export
init : LVect (S n) a -> LVect n a
init [x] = []
init (x :: xs@(_ :: _)) = x :: init xs

public export
last : LVect (S n) a -> a
last [x] = x
last (_ :: xs@(_ :: _)) = last xs

public export
index : Fin n -> LVect n a -> a
index FZ (x :: _) = x
index (FS i) (_ :: xs) = index i xs

public export
take : Discard a => (n : Nat) -> (1 _ : LVect (n + m) a) -> LVect n a
take Z xs = let () = discard xs in []
take (S n) (x :: xs) = x :: take n xs

public export
drop : Discard a => (n : Nat) -> (1 _ : LVect (n + m) a) -> LVect m a
drop Z xs = xs
drop (S n) (x :: xs) = let () = discard x in drop n xs

public export
(++) : (1 _ : LVect m a) -> (1 _ : LVect n a) -> LVect (m + n) a
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

public export
reverse : (xs : LVect n a) -> LVect n a
reverse = vectToLVect . reverse . lVectToVect

public export
splitAt : (n : Nat) -> LVect (n + m) a -> LPair (LVect n a) (LVect m a)
splitAt n = pairToLPair . (vectToLVect *** vectToLVect) . splitAt n . lVectToVect

public export
zipWith : (a -> b -> c) -> LVect n a -> LVect n b -> LVect n c
zipWith f [] [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

public export
linearZipWith : ((1 _ : a) -> (1 _ : b) -> c) -> (1 _ : LVect n a) -> (1 _ : LVect n b) -> LVect n c
linearZipWith f [] [] = []
linearZipWith f (x :: xs) (y :: ys) = f x y :: linearZipWith f xs ys

public export
unzip : LVect n (LPair a b) -> LPair (LVect n a) (LVect n b)
unzip [] = [] # []
unzip ((x # y) :: xys) =
  let (xs # ys) = unzip xys in
      (x :: xs # y :: ys)

