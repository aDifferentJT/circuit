module Data.HVect

import Data.Vect

%default total

public export
data HVect : Vect n Type -> Type where
  Nil : HVect []
  (::) : t -> HVect ts -> HVect (t :: ts)

public export
replicate : {n : Nat} -> {0 as : Vect n a} -> (0 f : a -> Type) -> ((0 x : a) -> f x) -> HVect (map f as)
replicate {n = Z} {as = []} f g = []
replicate {n = S n} {as = a :: as} f g = g a :: replicate {n} {as} f g

public export
hVectToVect : {n : Nat} -> {0 xs : Vect n t1} -> {0 f : t1 -> Type} -> ({0 x : t1} -> f x -> t2) -> HVect (map f xs) -> Vect n t2
hVectToVect {n = Z} {xs = []} g [] = []
hVectToVect {n = S _} {xs = _ :: _} g (y :: ys) = g y :: hVectToVect {f} g ys

public export
hVectOneElement : {n : Nat} -> {k : Fin n} -> {0 as : Vect n a} -> (0 f : a -> Type) -> f (index k as) -> HVect (map (\a => Maybe (f a)) as)
hVectOneElement {n = S _} {k = FZ} {as = _ :: _} f x = Just x :: replicate (\a => Maybe (f a)) (\_ => Nothing)
hVectOneElement {n = S _} {k = FS k} {as = _ :: as} f x = Nothing :: hVectOneElement {k} {as} f x

public export
zip : HVect as -> HVect bs -> HVect (zipWith Pair as bs)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

public export
zipMaps : {0 f : a -> Type} -> {0 g : a -> Type} -> (as : Vect n a) -> zipWith Pair (map f as) (map g as) = map (\x => (f x, g x)) as
zipMaps [] = Refl
zipMaps (a :: as) = cong ((f a, g a) ::) $ zipMaps as

