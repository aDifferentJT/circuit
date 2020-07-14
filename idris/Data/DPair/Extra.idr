module Data.DPair.Extra

import Data.Vect

%default total

public export
second : {f : a -> Type} -> {g : a -> Type} -> ({x : a} -> f x -> g x) -> DPair a f -> DPair a g
second h (MkDPair x y) = MkDPair x (h y)

infixl 3 ***
public export
(***) : {f : a -> Type} -> {g : b -> Type} -> (h : a -> b) -> ({x : a} -> f x -> g (h x)) -> DPair a f -> DPair b g
(***) h i (x ** y) = (h x ** i y)

public export
mapFstSecondDep
  :  {a : Type}
  -> {f : a -> Type}
  -> (g : a -> Type)
  -> (h : {x : a} -> f x -> g x)
  -> (xs : Vect n (DPair a f))
  -> map DPair.fst (map (second h) xs) = map DPair.fst xs
mapFstSecondDep _ _ [] = Refl
mapFstSecondDep {f} g h (MkDPair x _ :: xs) = cong $ mapFstSecondDep {f} g h xs

