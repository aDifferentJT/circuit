module Utils

import Data.DPair.Extra
import Data.SortedMap
import Data.SortedSet
import Data.Vect

%access public export
%default total

autoDer : {auto x : a} -> a
autoDer {x} = x

listToVect : List a -> (n : Nat ** Vect n a)
listToVect [] = (0 ** [])
listToVect (x :: xs) with (listToVect xs)
  | (n ** xs') = (S n ** x :: xs')

replicate : {n : Nat} -> a -> Vect n a
replicate {n} = replicate n

first : (a -> a') -> (a, b) -> (a', b)
first f (x, y) = (f x, y)

second : (b -> b') -> (a, b) -> (a, b')
second f (x, y) = (x, f y)

infixl 3 ***
(***) : (a -> b) -> (a' -> b') -> (a, a') -> (b, b')
(***) f g (x, y) = (f x, g y)


mapLeft : (a -> a') -> Either a b -> Either a' b
mapLeft f (Left x)  = Left (f x)
mapLeft f (Right x) = Right x


fromJust : (x : Maybe a) -> IsJust x -> a
fromJust (Just x) ItIsJust = x


zipVect : (Vect m a -> b) -> Vect m (Vect n a) -> Vect n b
zipVect {n = Z} f xss = []
zipVect {n = S n} f xss = f (map head xss) :: zipVect f (map tail xss)

zipUnequalVect : {f : Vect m Nat -> Nat}
  -> ((xs : Vect m (o : Nat ** Vect o a)) -> Vect (f (map DPair.fst xs)) a)
  -> (xss : Vect m (o : Nat ** Vect n (Vect o a)))
  -> Vect n (Vect (f (map DPair.fst xss)) a)
zipUnequalVect {n = Z} g xss = []
zipUnequalVect {a} {n = (S n)} g xss =
  (rewrite sym $ mapFstSecondDep (\o => Vect o a) head xss in
           g $ map (second head) xss
           )
    :: (rewrite sym $ mapFstSecondDep (\o => Vect n (Vect o a)) tail xss in
       zipUnequalVect g $ map (second tail) xss
       )


showHashIdent : Bits64 -> String
showHashIdent = pack . concatMap byteAlpha . b64ToBytes
  where
    byteAlpha : Bits8 -> List Char
    byteAlpha c = map (chr . ((ord 'a') +) . prim__zextB8_Int)
      [ prim__andB8 0xF $ prim__lshrB8 c 4
      , prim__andB8 0xF c
      ]


decEqVectDPair : DecEq a => {f : a -> Type} -> Vect (S n) (x : a ** f x) -> Maybe (x : a ** Vect (S n) (f x))
decEqVectDPair [(x ** y)] = Just (x ** [y])
decEqVectDPair {n = S _} ((x ** y) :: xs) with (decEqVectDPair xs)
  decEqVectDPair _ | Nothing = Nothing
  decEqVectDPair ((x ** y) :: _) | Just (x' ** ys) with (decEq x x')
    decEqVectDPair ((x ** y) :: _) | Just (x ** ys) | Yes Refl = Just (x ** (y :: ys))
    decEqVectDPair _ | Just _ | No _ = Nothing


removeDuplicates : Ord a => List a -> List a
removeDuplicates = SortedSet.toList . SortedSet.fromList

removeDuplicatesWith : Ord b => (a -> b) -> List a -> List a
removeDuplicatesWith f = map snd . SortedMap.toList . SortedMap.fromList . map (\x => (f x, x))

