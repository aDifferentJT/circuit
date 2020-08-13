module Utils

import Data.DPair.Extra
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Decidable.Equality

%default total

public export
autoDer : {auto x : a} -> a
autoDer {x} = x

public export
listToVect : List a -> (n : Nat ** Vect n a)
listToVect [] = (0 ** [])
listToVect (x :: xs) = let (n ** xs') = listToVect xs in (S n ** x :: xs')

public export
replicate : {n : Nat} -> a -> Vect n a
replicate {n} = replicate n

public export
first : (a -> a') -> (a, b) -> (a', b)
first f (x, y) = (f x, y)

public export
second : (b -> b') -> (a, b) -> (a, b')
second f (x, y) = (x, f y)

infixr 3 &&&
public export
(&&&) : (a -> b1) -> (a -> b2) -> a -> (b1, b2)
(&&&) f g x = (f x, g x)

infixr 3 ***
public export
(***) : (a1 -> b1) -> (a2 -> b2) -> (a1, a2) -> (b1, b2)
(***) f g (x, y) = (f x, g y)

infixr 3 ****
public export
(****) : (a1 -> b1 -> c1) -> (a2 -> b2 -> c2) -> (a1, a2) -> (b1, b2) -> (c1, c2)
(****) f g (x1, x2) (y1, y2) = (f x1 y1, g x2 y2)


mapLeft : (a -> a') -> Either a b -> Either a' b
mapLeft f (Left x)  = Left (f x)
mapLeft f (Right x) = Right x

export
zipVect : {n : Nat} -> (Vect m a -> b) -> Vect m (Vect n a) -> Vect n b
zipVect {n = Z} f xss = []
zipVect {n = S n} f xss = f (map head xss) :: zipVect f (map tail xss)

export
zipUnequalVect
  :  {n : Nat}
  -> {0 f : Vect m Nat -> Nat}
  -> {a : Type}
  -> ((xs : Vect m (o : Nat ** Vect o a)) -> Vect (f (map DPair.fst xs)) a)
  -> (xss : Vect m (o : Nat ** Vect n (Vect o a)))
  -> Vect n (Vect (f (map DPair.fst xss)) a)
zipUnequalVect {n = Z} g xss = []
zipUnequalVect {n = S n} g xss =
  (rewrite sym $ mapFstSecondDep (\o => Vect o a) head xss in
           g $ map (second head) xss
  ) :: (rewrite sym $ mapFstSecondDep (\o => Vect n (Vect o a)) tail xss in
                zipUnequalVect {n} {f} g $ map (second tail) xss
       )


export
showHashIdent : Bits64 -> String
showHashIdent = pack . showHashIdent'
  where
    nybble : Bits64 -> Char
    nybble = chr . ((ord 'a') +) . cast . prim__cast_Bits64Integer

    showHashIdent' : Bits64 -> List Char
    showHashIdent' 0 = []
    showHashIdent' n = nybble (prim__and_Bits64 n 0xf) :: showHashIdent' (assert_smaller n $ prim__shr_Bits64 n 4)


export
decEqVectDPair : DecEq a => {n : Nat} -> {0 f : a -> Type} -> Vect (S n) (x : a ** f x) -> Maybe (x : a ** Vect (S n) (f x))
decEqVectDPair [(x ** y)] = Just (x ** [y])
decEqVectDPair {n = S _} (MkDPair x y :: xs) with (decEqVectDPair xs)
  decEqVectDPair (MkDPair _ _ :: _) | Nothing = Nothing
  decEqVectDPair (MkDPair x y :: _) | Just (MkDPair x' ys) with (decEq x x')
    decEqVectDPair (MkDPair x y :: _) | Just (MkDPair x ys) | Yes Refl = Just (x ** (y :: ys))
    decEqVectDPair (MkDPair _ _ :: _) | Just (MkDPair _ _)  | No _ = Nothing


export
thenCompare : Ordering -> Lazy Ordering -> Ordering
thenCompare LT y = LT
thenCompare EQ y = y
thenCompare GT y = GT

export
liftA2 : Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 g x y = g <$> x <*> y

