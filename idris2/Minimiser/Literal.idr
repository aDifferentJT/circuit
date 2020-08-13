module Minimiser.Literal

import Utils

%default total

public export
data Literal a = Pos a | Neg a

export
Functor Literal where
  map f (Pos x) = Pos $ f x
  map f (Neg x) = Neg $ f x

export
Eq a => Eq (Literal a) where
  (Pos x) == (Pos y) = x == y
  (Neg x) == (Neg y) = x == y
  (Pos x) == (Neg y) = False
  (Neg x) == (Pos y) = False

export
Ord a => Ord (Literal a) where
  compare (Pos x) (Pos y) = compare x y
  compare (Neg x) (Neg y) = compare x y
  compare (Pos x) (Neg y) = compare x y `thenCompare` GT
  compare (Neg x) (Pos y) = compare x y `thenCompare` LT

export
Show a => Show (Literal a) where
  show (Pos x) = "Pos (" ++ show x ++ ")"
  show (Neg x) = "Neg (" ++ show x ++ ")"

export
negate : Literal a -> Literal a
negate (Pos x) = Neg x
negate (Neg x) = Pos x

export
covers : Eq a => List (Literal a) -> List (Literal a) -> Bool
covers x y = all (flip elem y) x

