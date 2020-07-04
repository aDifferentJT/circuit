module Data.DPair.Extra

import Data.Vect

%default total
%access public export

second : {f : a -> Type} -> {g : a -> Type} -> ({x : a} -> f x -> g x) -> (x : a ** f x) -> (x : a ** g x)
second h (x ** y) = (x ** h y)

mapFstSecondDep :
     {f : a -> Type}
  -> (g : a -> Type)
  -> (h : {x : a} -> f x -> g x)
  -> (xs : Vect _ (x : a ** f x))
  -> map DPair.fst (map (second h) xs) = map DPair.fst xs
mapFstSecondDep _ _ [] = Refl
mapFstSecondDep {f} g h ((_ ** _) :: xs) = cong $ mapFstSecondDep {f} g h xs

