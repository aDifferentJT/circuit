module LinearUtils

import Control.Monad.State

%default total

public export
relax : ((1 _ : a) -> b) -> a -> b
relax f x = f x

public export
relax2 : (a -> (1 _ : b) -> c) -> a -> b -> c
relax2 f x y = f x y

public export
linearRewrite : (0 p : (a -> Type)) -> (0 _ : x = y) -> (1 _ : p y) -> p x
linearRewrite _ Refl x = x

public export
linearReplace : {0 p : (a -> Type)} -> (0 _ : x = y) -> (1 _ : p x) -> p y
linearReplace Refl x = x

public export
(.) : (1 _ : (1 _ : b) -> c) -> (1 _ : (1 _ : a) -> b) -> (1 _ : a) -> c
(f . g) x = f (g x)

public export
flip : (1 _ : (1 _ : a) -> (1 _ : b) -> c) -> (1 _ : b) -> (1 _ : a) -> c
flip f x y = f y x

public export
mixedFlip : (1 _ : (1 _ : a) -> b -> c) -> b -> (1 _ : a) -> c
mixedFlip f x y = f y x

public export
interface Discard a where
  discard : (1 _ : a) -> ()

public export
data Unrestricted a = MkUnrestricted a

public export
getUnrestricted : (1 _ : Unrestricted a) -> a
getUnrestricted (MkUnrestricted x) = x

public export
map : ((1 _ : a) -> b) -> (1 _ : Unrestricted a) -> Unrestricted b
map f (MkUnrestricted x) = MkUnrestricted $ f x

public export
(<$>) : ((1 _ : a) -> b) -> (1 _ : Unrestricted a) -> Unrestricted b
(<$>) = map

public export
(<*>) : (1 _ : Unrestricted ((1 _ : a) -> b)) -> (1 _ : Unrestricted a) -> Unrestricted b
(MkUnrestricted f) <*> (MkUnrestricted x) = MkUnrestricted $ f x

public export
liftA2 : ((1 _ : a) -> (1 _ : b) -> c) -> (1 _ : Unrestricted a) -> (1 _ : Unrestricted b) -> Unrestricted c
liftA2 f (MkUnrestricted x) (MkUnrestricted y) = MkUnrestricted (f x y)


public export
interface Dup a where
  dup : (1 _ : a) -> LPair a a
  release : (1 _ : a) -> Unrestricted a


public export
pairToLPair : (a, b) -> LPair a b
pairToLPair (x, y) = x # y

public export
lPairToPair : LPair a b -> (a, b)
lPairToPair (x # y) = (x, y)

public export
fst : LPair a b -> a
fst (x # _) = x

public export
snd : LPair a b -> b
snd (_ # y) = y

public export
first : (a -> a') -> LPair a b -> LPair a' b
first f (x # y) = f x # y

public export
second : (b -> b') -> LPair a b -> LPair a b'
second f (x # y) = x # f y

public export
(***) : ((1 _ : a) -> a') -> ((1 _ : b) -> b') -> (1 _ : LPair a b) -> LPair a' b'
(***) f g (x # y) = f x # g y

public export
(****) : ((1 _ : a1) -> (1 _ : b1) -> c1) -> ((1 _ : a2) -> (1 _ : b2) -> c2) -> (1 _ : LPair a1 a2) -> (1 _ : LPair b1 b2) -> LPair c1 c2
(****) f g (x1 # x2) (y1 # y2) = f x1 y1 # g x2 y2

