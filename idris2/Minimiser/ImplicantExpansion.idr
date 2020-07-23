module Minimiser.ImplicantExpansion

import Data.List
import Minimiser.Literal

%default total

removeEach : List a -> List (List a)
removeEach [] = []
removeEach (x :: xs) = xs :: map (x ::) (removeEach xs)

sequentialSearch'
  :  Eq a
  => (offSet : List (List (Literal a)))
  -> List (Literal a)
  -> List (Literal a)
  -> List (Literal a)
sequentialSearch' offSet term1 [] = term1
sequentialSearch' offSet term1 (lit :: term2) =
  if ((term1 ++ term2) `covers`) `any` offSet
     then sequentialSearch' offSet (lit :: term1) term2
     else sequentialSearch' offSet term1 term2

sequentialSearch
  :  Eq a
  => (offSet : List (List (Literal a)))
  -> List (Literal a)
  -> List (Literal a)
sequentialSearch offSet = sequentialSearch' offSet []

export
multipleSequentialSearch
  : Ord a
  => (offSet : List (List (Literal a)))
  -> List (Literal a)
  -> List (List (Literal a))
multipleSequentialSearch offSet xs =
  let ys = nub $ map sort $ map (sequentialSearch offSet) $ filter (not . flip any offSet . covers) $ removeEach $ xs in
      if isNil ys
         then [xs]
         else ys

