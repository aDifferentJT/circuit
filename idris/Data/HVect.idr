module Data.HVect

import Data.Vect

%default total

public export
data HVect : Vect n Type -> Type where
  Nil : HVect []
  (::) : t -> HVect ts -> HVect (t :: ts)

public export
replicate : {as : Vect n a} -> (f : a -> Type) -> ((x : a) -> f x) -> HVect (map f as)
replicate {as = []} f g = []
replicate {as = a :: as} f g = g a :: replicate f g

public export
hVectToVect : {xs : Vect n t1} -> {f : t1 -> Type} -> ({x : t1} -> f x -> t2) -> HVect (map f xs) -> Vect n t2
hVectToVect {xs = []} g [] = []
hVectToVect {xs = x :: xs} {f} g (y :: ys) = g y :: hVectToVect {f} g ys

public export
vectToHVect : Vect n t -> HVect (replicate n t)
vectToHVect [] = []
vectToHVect (x :: xs) = x :: vectToHVect xs

public export
hVectOneElement : {n : Nat} -> {k : Fin n} -> {as : Vect n a} -> (f : a -> Type) -> f (index k as) -> HVect (map (\a => Maybe (f a)) as)
hVectOneElement {k = FZ} {as = _ :: _} f x = Just x :: replicate (\a => Maybe (f a)) (\_ => Nothing)
hVectOneElement {k = FS k} {as = _ :: as} f x = Nothing :: hVectOneElement {k} {as} f x

public export
zip : HVect as -> HVect bs -> HVect (zipWith Pair as bs)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

public export
zipMaps : {f : a -> Type} -> {g : a -> Type} -> (as : Vect n a) -> zipWith Pair (map f as) (map g as) = map (\x => (f x, g x)) as
zipMaps [] = Refl
zipMaps (a :: as) = cong $ zipMaps as

