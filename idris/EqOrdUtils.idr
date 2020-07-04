module EqOrdUtils

%default total

%access export

[EqVoid] Eq Void where
  _ == _ impossible

[OrdVoid] Ord Void using EqVoid where
  compare _ _ impossible

EqEither : (Eq a, Eq b) => Eq (Either a b)
EqEither = %implementation

[OrdEither] (Ord a, Ord b) => Ord (Either a b) where
  compare (Left x)  (Left y)  = compare x y
  compare (Right x) (Right y) = compare x y
  compare (Left x)  (Right y) = LT
  compare (Right x) (Left y)  = GT

EqPair : (Eq a, Eq b) => Eq (a, b)
EqPair = %implementation

OrdPair : (Ord a, Ord b) => Ord (a, b)
OrdPair = %implementation

data T : Type

[EqDPair] ((x : a) -> Eq (f x), DecEq a) => Eq (DPair a f) where
  (==) @{eqF} (x1 ** y1) (x2 ** y2) with (decEq x1 x2)
    (==) @{eqF} (x ** y1) (x ** y2) | Yes Refl = (==) @{eqF x} y1 y2
    (==) _ _ | No _ = False

private
EqFromOrd : Ord a => Eq a
EqFromOrd = %implementation

private
[EqFromOrdDPair] ((x : a) -> Ord (f x), DecEq a) => Eq (DPair a f) where
  (==) @{ordF} = (==) @{EqDPair @{\x => EqFromOrd @{ordF x}}}

[OrdDPair] ((x : a) -> Ord (f x), DecEq a, Ord a) => Ord (DPair a f) using EqFromOrdDPair where
  compare @{ordF} (x1 ** y1) (x2 ** y2) with (decEq x1 x2)
    compare @{ordF} (x ** y1) (x ** y2) | Yes Refl = compare @{ordF x} y1 y2
    compare (x1 ** _) (x2 ** _) | No _ = compare x1 x2

