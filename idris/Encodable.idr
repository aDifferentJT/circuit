module Encodable

%default total

infixr 9 &
public export
data Encodable : Type where
  Bit     : Encodable
  (&)     : Encodable -> Encodable -> Encodable
  EncVect : Nat -> Encodable -> Encodable
  NewEnc  : String -> Encodable -> Encodable

export
DecEq Encodable where
  decEq Bit Bit = Yes Refl
  decEq (a & b) (a' & b') with (decEq a a', decEq b b')
    decEq (a & b) (a  & b ) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (a & b) (a  & b') | (Yes Refl, No  p   ) = No $ \Refl => p Refl
    decEq (a & b) (a' & b ) | (No  p,    Yes Refl) = No $ \Refl => p Refl
    decEq (a & b) (a' & b') | (No  p,    No  _   ) = No $ \Refl => p Refl
  decEq (EncVect n a) (EncVect n' a') with (decEq n n', decEq a a')
    decEq (EncVect n a) (EncVect n  a ) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (EncVect n a) (EncVect n  a') | (Yes Refl, No  p   ) = No $ \Refl => p Refl
    decEq (EncVect n a) (EncVect n' a ) | (No  p,    Yes Refl) = No $ \Refl => p Refl
    decEq (EncVect n a) (EncVect n' a') | (No  p,    No  _   ) = No $ \Refl => p Refl
  decEq (NewEnc i a) (NewEnc i' a') with (decEq i i', decEq a a')
    decEq (NewEnc i a) (NewEnc i  a ) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (NewEnc i a) (NewEnc i  a') | (Yes Refl, No  p   ) = No $ \Refl => p Refl
    decEq (NewEnc i a) (NewEnc i' a ) | (No  p,    Yes Refl) = No $ \Refl => p Refl
    decEq (NewEnc i a) (NewEnc i' a') | (No  p,    No  _   ) = No $ \Refl => p Refl
  decEq Bit           (_ & _)       = No $ \Refl impossible
  decEq Bit           (EncVect _ _) = No $ \Refl impossible
  decEq Bit           (NewEnc _ _)  = No $ \Refl impossible
  decEq (_ & _)       Bit           = No $ \Refl impossible
  decEq (_ & _)       (EncVect _ _) = No $ \Refl impossible
  decEq (_ & _)       (NewEnc _ _)  = No $ \Refl impossible
  decEq (EncVect _ _) Bit           = No $ \Refl impossible
  decEq (EncVect _ _) (_ & _)       = No $ \Refl impossible
  decEq (EncVect _ _) (NewEnc _ _)  = No $ \Refl impossible
  decEq (NewEnc _ _)  Bit           = No $ \Refl impossible
  decEq (NewEnc _ _)  (_ & _)       = No $ \Refl impossible
  decEq (NewEnc _ _)  (EncVect _ _) = No $ \Refl impossible

export
Eq Encodable where
  a == b with (decEq a b)
    | Yes _ = True
    | No _ = False

export
Ord Encodable where
  compare Bit           Bit           = EQ
  compare Bit           (_ & _)       = LT
  compare Bit           (EncVect _ _) = LT
  compare Bit           (NewEnc _ _)  = LT
  compare (_ & _)       Bit           = GT
  compare (a & b)       (a' & b')     = thenCompare (compare a a') (compare b b')
  compare (_ & _)       (EncVect _ _) = LT
  compare (_ & _)       (NewEnc _ _)  = LT
  compare (EncVect _ _) Bit           = GT
  compare (EncVect _ _) (_ & _)       = GT
  compare (EncVect m a) (EncVect n b) = thenCompare (compare m n) (compare a b)
  compare (EncVect _ _) (NewEnc _ _)  = LT
  compare (NewEnc _ _)  Bit           = GT
  compare (NewEnc _ _)  (_ & _)       = GT
  compare (NewEnc _ _)  (EncVect _ _) = GT
  compare (NewEnc i a)  (NewEnc i' b) = thenCompare (compare i i') (compare a b)

export
encPairInjective : ((a & b) = (a' & b')) -> (a = a', b = b')
encPairInjective Refl = (Refl, Refl)

export
encVectInjective : (EncVect n a = EncVect n' a') -> (n = n', a = a')
encVectInjective Refl = (Refl, Refl)

export
newEncInjective : {i : String} -> {a : Encodable} -> {i' : String} -> {b : Encodable} -> (NewEnc i a = NewEnc i' b) -> a = b
newEncInjective Refl = Refl


public export
data LTE : Encodable -> Encodable -> Type where
  LTERefl : Encodable.LTE a a
  LTFst : LTE a b1 -> LTE a (b1 & b2)
  LTSnd : LTE a b2 -> LTE a (b1 & b2)
  LTVect : LTE a b -> LTE a (EncVect n b)
  LTNewEnc : LTE a b -> LTE a (NewEnc i b)

export
lteTrans : Encodable.LTE a b -> Encodable.LTE b c -> Encodable.LTE a c
lteTrans p1 LTERefl = p1
lteTrans p1 (LTFst p2) = LTFst $ lteTrans p1 p2
lteTrans p1 (LTSnd p2) = LTSnd $ lteTrans p1 p2
lteTrans p1 (LTVect p2) = LTVect $ lteTrans p1 p2
lteTrans p1 (LTNewEnc p2) = LTNewEnc $ lteTrans p1 p2

lteFst : LTE (a & _) b -> LTE a b
lteFst = lteTrans $ LTFst LTERefl

lteSnd : LTE (_ & a) b -> LTE a b
lteSnd = lteTrans $ LTSnd LTERefl

lteVect : LTE (EncVect _ a) b -> LTE a b
lteVect = lteTrans $ LTVect LTERefl

lteNewEnc : LTE (NewEnc _ a) b -> LTE a b
lteNewEnc = lteTrans $ LTNewEnc LTERefl

mutual
  export
  Uninhabited (LTE (a & _) a) where
    uninhabited LTERefl impossible
    uninhabited {a = _ & _} (LTFst p) = absurd $ lteFst p
    uninhabited {a = a & b} (LTSnd p) = absurd $ lteFst p
    uninhabited {a = EncVect n a} (LTVect p) = absurd $ lteFst p
    uninhabited {a = NewEnc _ _} (LTNewEnc p) = absurd $ lteFst p

  export
  Uninhabited (LTE (_ & a) a) where
    uninhabited LTERefl impossible
    uninhabited {a = _ & _} (LTFst p) = absurd $ lteSnd p
    uninhabited {a = a & b} (LTSnd p) = absurd $ lteSnd p
    uninhabited {a = EncVect n a} (LTVect p) = absurd $ lteSnd p
    uninhabited {a = NewEnc _ _} (LTNewEnc p) = absurd $ lteSnd p

  export
  Uninhabited (LTE (EncVect _ a) a) where
    uninhabited LTERefl impossible
    uninhabited {a = _ & _} (LTFst p) = absurd $ lteVect p
    uninhabited {a = a & b} (LTSnd p) = absurd $ lteVect p
    uninhabited {a = EncVect n a} (LTVect p) = absurd $ lteVect p
    uninhabited {a = NewEnc _ _} (LTNewEnc p) = absurd $ lteVect p

  export
  Uninhabited (LTE (NewEnc _ a) a) where
    uninhabited LTERefl impossible
    uninhabited {a = _ & _} (LTFst p) = absurd $ lteNewEnc p
    uninhabited {a = a & b} (LTSnd p) = absurd $ lteNewEnc p
    uninhabited {a = EncVect n a} (LTVect p) = absurd $ lteNewEnc p
    uninhabited {a = NewEnc _ _} (LTNewEnc p) = absurd $ lteNewEnc p

export
lteAntiSymmetric : {a : Encodable} -> {b : Encodable} -> LTE a b -> LTE b a -> a = b
lteAntiSymmetric LTERefl _ = Refl
lteAntiSymmetric _ LTERefl = Refl

lteAntiSymmetric (LTFst p1) (LTFst p2) with (lteAntiSymmetric (lteFst p1) (lteFst p2))
  | Refl = absurd p1
lteAntiSymmetric (LTFst p1) (LTSnd p2) with (lteAntiSymmetric (lteSnd p1) (lteFst p2))
  | Refl = absurd p1
lteAntiSymmetric (LTFst p1) (LTVect p2) with (lteAntiSymmetric (lteVect p1) (lteFst p2))
  | Refl = absurd p1
lteAntiSymmetric (LTFst p1) (LTNewEnc p2) with (lteAntiSymmetric (lteNewEnc p1) (lteFst p2))
  | Refl = absurd p1

lteAntiSymmetric (LTSnd p1) (LTFst p2) with (lteAntiSymmetric (lteFst p1) (lteSnd p2))
  | Refl = absurd p1
lteAntiSymmetric (LTSnd p1) (LTSnd p2) with (lteAntiSymmetric (lteSnd p1) (lteSnd p2))
  | Refl = absurd p1
lteAntiSymmetric (LTSnd p1) (LTVect p2) with (lteAntiSymmetric (lteVect p1) (lteSnd p2))
  | Refl = absurd p1
lteAntiSymmetric (LTSnd p1) (LTNewEnc p2) with (lteAntiSymmetric (lteNewEnc p1) (lteSnd p2))
  | Refl = absurd p1

lteAntiSymmetric (LTVect p1) (LTFst p2) with (lteAntiSymmetric (lteFst p1) (lteVect p2))
  | Refl = absurd p1
lteAntiSymmetric (LTVect p1) (LTSnd p2) with (lteAntiSymmetric (lteSnd p1) (lteVect p2))
  | Refl = absurd p1
lteAntiSymmetric (LTVect p1) (LTVect p2) with (lteAntiSymmetric (lteVect p1) (lteVect p2))
  | Refl = absurd p1
lteAntiSymmetric (LTVect p1) (LTNewEnc p2) with (lteAntiSymmetric (lteNewEnc p1) (lteVect p2))
  | Refl = absurd p1

lteAntiSymmetric (LTNewEnc p1) (LTFst p2) with (lteAntiSymmetric (lteFst p1) (lteNewEnc p2))
  | Refl = absurd p1
lteAntiSymmetric (LTNewEnc p1) (LTSnd p2) with (lteAntiSymmetric (lteSnd p1) (lteNewEnc p2))
  | Refl = absurd p1
lteAntiSymmetric (LTNewEnc p1) (LTVect p2) with (lteAntiSymmetric (lteVect p1) (lteNewEnc p2))
  | Refl = absurd p1
lteAntiSymmetric (LTNewEnc p1) (LTNewEnc p2) with (lteAntiSymmetric (lteNewEnc p1) (lteNewEnc p2))
  | Refl = absurd p1

