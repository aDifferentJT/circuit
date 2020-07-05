module NatProofs

import Data.DPair.Extra
import Data.Nat
import Data.Vect
import Utils

%default total

export
maxNat : Nat -> Nat -> Nat
maxNat Z     y     = y
maxNat x     Z     = x
maxNat (S x) (S y) = S (maxNat x y)

maxNatXZIsX : (x : Nat) -> maxNat x Z = x
maxNatXZIsX Z     = Refl
maxNatXZIsX (S x) = Refl

export
xSmallerThanMaxNatXY : (x : Nat) -> (y : Nat) -> LTE x (maxNat x y)
xSmallerThanMaxNatXY Z     y     = LTEZero
xSmallerThanMaxNatXY x     Z     = rewrite maxNatXZIsX x in lteRefl
xSmallerThanMaxNatXY (S x) (S y) = LTESucc (xSmallerThanMaxNatXY x y)

export
ySmallerThanMaxNatXY : (x : Nat) -> (y : Nat) -> LTE y (maxNat x y)
ySmallerThanMaxNatXY Z     y     = lteRefl
ySmallerThanMaxNatXY x     Z     = LTEZero
ySmallerThanMaxNatXY (S x) (S y) = LTESucc (ySmallerThanMaxNatXY x y)


export
maxNats : Vect (S m) Nat -> Nat
maxNats [n] = n
maxNats (n :: ns@(_ :: _)) = maxNat n (maxNats ns)

export
maxNatsWithProofs : (f : a -> Nat) -> Vect (S m) a -> (n : Nat ** Vect (S m) (x : a ** LTE (f x) n))
maxNatsWithProofs f [x] =
  (f x ** [(x ** lteRefl)])
maxNatsWithProofs f (x :: xs@(_ :: _)) =
  let (n ** ys) = maxNatsWithProofs f xs in
  (  maxNat (f x) n
  ** (x ** xSmallerThanMaxNatXY (f x) n)
  :: map (second $ \p => lteTransitive p (ySmallerThanMaxNatXY (f x) n)) ys
  )

minusSuccLeftSucc : (left : Nat) -> (right : Nat) -> {auto smaller : LTE right left} -> S (left `minus` right) = S left `minus` right
minusSuccLeftSucc left     Z                                   = rewrite minusZeroRight left in Refl
minusSuccLeftSucc (S left) (S right) {smaller=LTESucc smaller} = minusSuccLeftSucc left right

plusLeftSuccRightSucc : (left : Nat) -> (right : Nat) -> S left + right = left + S right
plusLeftSuccRightSucc left right =
  rewrite plusCommutative (S left) right in
          rewrite sym (plusSuccRightSucc right left) in
                  rewrite plusCommutative right left in
                          plusSuccRightSucc left right

export
plusMinusCancel : (m : Nat) -> (n : Nat) -> {auto smaller : LTE n m} -> n + (m `minus` n) = m
plusMinusCancel m Z = rewrite minusZeroRight m in Refl
plusMinusCancel (S m) (S n) {smaller=LTESucc smaller} =
  rewrite plusLeftSuccRightSucc n (m `minus` n) in
          rewrite minusSuccLeftSucc m n in
                  plusMinusCancel (S m) n {smaller=lteSuccRight smaller}

