
import Analytics
import Circuit
import C_Circuit
import Data.Bits
import Data.Vect
import GUI
import IndexType
import NatProofs
import Utils

%default total

not : (input : Encodable) -> Bit' input -> Bit' input
not input = primitive "not" bitNot input

fullAdder' : Bit -> Bit -> Bit -> (Bit, Bit)
fullAdder' B0 B0 B0 = (B0, B0)
fullAdder' B0 B0 B1 = (B1, B0)
fullAdder' B0 B1 B0 = (B1, B0)
fullAdder' B0 B1 B1 = (B0, B1)
fullAdder' B1 B0 B0 = (B1, B0)
fullAdder' B1 B0 B1 = (B0, B1)
fullAdder' B1 B1 B0 = (B0, B1)
fullAdder' B1 B1 B1 = (B1, B1)

fullAdder : (input : Encodable) -> (Bit' input) -> (Bit' input) -> (Bit' input) -> (Bit' input, Bit' input)
fullAdder input = primitive "fullAdder" fullAdder' input

data IntBits : Nat -> Encodable -> Type where
  MkInt : Vect n (Bit' input) -> IntBits n input

IntBitsEnc : Nat -> Encodable
IntBitsEnc n = NewEnc ("Int " ++ show n) $ EncVect n Bit

EncodingValue (Bit' input) (IntBits n input) where
  builderEncodable = IntBitsEnc n
  constructEncodingValue (MkInt x) = NewEncoding $ constructEncodingValue {t = Bit' input} x
  deconstructEncodingValue (NewEncoding x) = MkInt $ deconstructEncodingValue {t = Bit' input} x

EncodingBuilder (Bit' input) (IntBits n input) where
  builderInput _ = UnitEnc
  builderOutput {input} {n} _ = builderEncodable {t = Bit' input} {a = IntBits n input}
  constructEncodingFunction {input} x UnitEnc = constructEncodingValue {t = Bit' input} x
  deconstructEncodingFunction {input} f = deconstructEncodingValue {t = Bit' input} $ f UnitEnc

rippleAdder
  :  (input : Encodable)
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> (IntBits n input, Bit' input)
rippleAdder {n = Z} input (MkInt []) (MkInt []) c = (MkInt [], c)
rippleAdder {n = S _} input (MkInt (x :: xs)) (MkInt (y :: ys)) c =
  let (z, c') = fullAdder input x y c in
      let (MkInt zs, c'') = rippleAdder input (MkInt xs) (MkInt ys) c' in
          (MkInt (z :: zs), c'')


data CarryType
  = Kill
  | Propagate
  | Generate

CarryType' : Encodable -> Type
CarryType' input = (Bit' input, Bit' input)

EncodingValue Bit CarryType where
  builderEncodable = Bit && Bit
  constructEncodingValue Kill = 0 && 0
  constructEncodingValue Propagate = 1 && 0
  constructEncodingValue Generate = 0 && 1
  deconstructEncodingValue (BitEncoding x && BitEncoding y) =
    case (x, y) of
         (B0, B0) => Kill
         (B1,  _) => Propagate
         (B0, B1) => Generate

EncodingBuilder Bit CarryType where
  builderInput _ = UnitEnc
  builderOutput _ = builderEncodable {t = Bit} {a = CarryType}
  constructEncodingFunction x UnitEnc = constructEncodingValue {t = Bit} x
  deconstructEncodingFunction f = deconstructEncodingValue {t = Bit} $ f UnitEnc

mergeCarries' : CarryType -> CarryType -> CarryType
mergeCarries' _ Kill      = Kill
mergeCarries' c Propagate = c
mergeCarries' _ Generate  = Generate

mergeCarries : (input : Encodable) -> CarryType' input -> CarryType' input -> CarryType' input
mergeCarries input = primitive "mergeCarries" mergeCarries' input

halfAdderLookahead' : Bit -> Bit -> (Bit, CarryType)
halfAdderLookahead' B0 B0 = (B0, Kill)
halfAdderLookahead' B0 B1 = (B1, Propagate)
halfAdderLookahead' B1 B0 = (B1, Propagate)
halfAdderLookahead' B1 B1 = (B0, Generate)

halfAdderLookahead : (input : Encodable) -> Bit' input -> Bit' input -> (Bit' input, CarryType' input)
halfAdderLookahead input = primitive "halfAdderLookahead" halfAdderLookahead' input

generateCarries : (input : Encodable) -> Vect n (Bit' input) -> Vect n (Bit' input) -> (Vect n (Bit' input), Vect n (CarryType' input))
generateCarries input xs ys = unzip $ zipWith (halfAdderLookahead input) xs ys

applyCarry' : Bit -> CarryType -> Bit
applyCarry' _ Kill      = B0
applyCarry' c Propagate = c
applyCarry' _ Generate  = B1

applyCarry : (input : Encodable) -> Bit' input -> CarryType' input -> Bit' input
applyCarry input = primitive "applyCarry" applyCarry' input

performCarries : (input : Encodable) -> Bit' input -> (Vect n (Bit' input), Vect n (CarryType' input)) -> (Vect n (Bit' input), (Bit' input))
performCarries input c (xs, cs) =
  let cs' = c :: map (applyCarry input c) cs in
  (map fst $ zipWith (halfAdderLookahead input) xs $ init $ cs', last cs')

carryLookaheadAdder
  :  {n : Nat}
  -> (input : Encodable)
  -> ((CarryType' input -> CarryType' input -> CarryType' input) -> Vect n (CarryType' input) -> Vect n (CarryType' input))
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> (IntBits n input, Bit' input)
carryLookaheadAdder input propagate (MkInt xs) (MkInt ys) c =
  first MkInt $
  performCarries input c $
  second (propagate (mergeCarries input)) $
  generateCarries input xs ys


ripplePropagation' : (a -> a -> a) -> Vect n a -> Vect n a
ripplePropagation' f [] = []
ripplePropagation' f [x] = [x]
ripplePropagation' {n = S (S _)} f (x :: xs@(_ :: _)) =
  let ys = ripplePropagation' f xs in
      f (head ys) x :: ys

ripplePropagation : (a -> a -> a) -> Vect n a -> Vect n a
ripplePropagation f = reverse . ripplePropagation' f . reverse


koggeStonePropagation' : (a -> a -> a) -> {n : Nat} -> (k : Nat ** LTE k n) -> Vect n a -> Vect n a
koggeStonePropagation' f {n} (k ** smaller) xs =
  let xs' = the (Vect (k + (n `minus` k)) a) $ rewrite plusMinusCancel n k in xs in
  let (xs'1, xs'2) = splitAt k xs' in
  rewrite sym $ plusMinusCancel n k in
  xs'1
  ++ (zipWith f
       (take (n `minus` k) {m = k} $ rewrite plusCommutative (n `minus` k) k in xs')
       (xs'2)
     )

isNo : Dec p -> Bool
isNo (Yes _) = False
isNo (No _) = True

covering
takeBefore : (n -> Bool) -> Stream n -> List n
takeBefore p (x :: xs)
    = if p x
         then []
         else x :: takeBefore p xs

koggeStonePropagation : {n : Nat} -> (a -> a -> a) -> Vect n a -> Vect n a
koggeStonePropagation {n} f =
  foldl (.) id $
  map (koggeStonePropagation' f) $
  assert_total $
  map (the ((m : Nat ** Dec (LTE m n)) -> (m : Nat ** LTE m n)) $ \(m ** Yes p) => (m ** p)) $
  reverse $
  takeBefore (the ((m : Nat ** Dec (LTE m n)) -> Bool) $ \(m ** p) => isNo p) $
  map (\m => (m ** isLTE m n)) $
  iterate (*2) 1


{-
clearBottomSetBit : {n : Nat} -> Fin n -> Fin n
clearBottomSetBit k =
  let
    res =
      bitsToInt $
        (MkBits $ natToBits {n = nextBytes 64} $ finToNat k) `and`
        ( (MkBits $ natToBits {n = nextBytes 64} $ finToNat k) `minus`
          (MkBits $ natToBits {n = nextBytes 64} 1)
        )
  in
    fromInteger res {prf = believe_me {a = IsJust (Just res)} ItIsJust}

halfFin : {n : Nat} -> Fin n -> Fin n
halfFin k =
  let res = cast k `div` 2 in
      fromInteger res {prf = believe_me {a = IsJust (Just res)} ItIsJust}

minusFin : Fin n -> (y : Nat) -> Fin (n `minus` y)
minusFin {n} x Z = rewrite minusZeroRight n in x
minusFin FZ (S y) = assert_total $ idris_crash "minusFin"
minusFin (FS x) (S y) = minusFin x y

lteFinToNat : {n : Nat} -> (k : Fin (S n)) -> LTE (finToNat k) n
lteFinToNat FZ= LTEZero
lteFinToNat {n = S _} (FS k) = LTESucc $ lteFinToNat k

brentKungPropagation' : {n : Nat} -> (a -> a -> a) -> Vect n a -> Fin n -> a
brentKungPropagation' f xs FZ = index FZ xs
brentKungPropagation' {n} f xs k =
  let k' = case clearBottomSetBit (FS k) of
                FZ => rewrite sym $ minusZeroRight n in halfFin (FS k) `minusFin` 1
                FS k' => k'
  in
  f (brentKungPropagation' f xs $ assert_smaller k k')
    (brentKungPropagation' f
      (drop (finToNat $ FS k') $ the (Vect ((finToNat $ FS k') + (n `minus` (finToNat $ FS k'))) a) $ foo)
      --(drop (finToNat $ FS k') $ the (Vect ((finToNat $ FS k') + (n `minus` (finToNat $ FS k'))) a) $ rewrite__impl (\n' => Vect n' a) ?foo xs)
      {-( drop (finToNat $ FS k') $
        the (Vect ((finToNat $ FS k') + (n `minus` (finToNat $ FS k'))) a) $
        rewrite__impl
          (\n' => Vect n' a)
          (the ((finToNat $ FS k') + (n `minus` (finToNat $ FS k')) = n) ?foo)
          xs
      )-}
        {-(plusMinusCancel n (finToNat $ FS k') {smaller = lteFinToNat $ FS k'})-}
      (assert_smaller k $ k `minusFin` (finToNat $ FS k'))
    )
  where
    foo : Vect (S (plus (finToNat k') (minus n (S (finToNat k'))))) a

brentKungPropagation : {n : Nat} -> (a -> a -> a) -> Vect n a -> Vect n a
brentKungPropagation f xs = map (brentKungPropagation' f xs) range
-}


rippleAdder2
  :  {n : Nat}
  -> (input : Encodable)
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> (IntBits n input, Bit' input)
rippleAdder2 input = carryLookaheadAdder input ripplePropagation

koggeStoneAdder
  :  {n : Nat}
  -> (input : Encodable)
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> (IntBits n input, Bit' input)
koggeStoneAdder input = carryLookaheadAdder input koggeStonePropagation

{-
brentKungAdder
  :  {n : Nat}
  -> (input : Encodable)
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> (IntBits n input, Bit' input)
brentKungAdder input = carryLookaheadAdder input brentKungPropagation
-}


covering
test : (n : Nat) -> IO ()
test n =
  guiSimulate "Ripple Adder"
    {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $
    constructProducing
      {f = \input => IntBits n input -> IntBits n input -> Bit' input -> (IntBits n input, Bit' input)}
      {f' = \input' => autoDer}
      (rippleAdder {n})

printAnalytics : (n : Nat) -> IO ()
printAnalytics n = do
  putStr "Ripple Adder:                       "
  printLn $
    analytics {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $
    constructProducing
      {f = \input => IntBits n input -> IntBits n input -> Bit' input -> (IntBits n input, Bit' input)}
      {f' = \input' => autoDer}
      (rippleAdder {n})
  putStr "Carry Lookahead overhead:           "
  printLn $
    analytics {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $
    constructProducing
      {f = \input => IntBits n input -> IntBits n input -> Bit' input -> (IntBits n input, Bit' input)}
      {f' = \input' => autoDer}
      (\input => carryLookaheadAdder {n} input (const id))
  putStr "Carry Lookahead style Ripple Adder: "
  printLn $
    analytics {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $
    constructProducing
      {f = \input => IntBits n input -> IntBits n input -> Bit' input -> (IntBits n input, Bit' input)}
      {f' = \input' => autoDer}
      (rippleAdder2 {n})
  putStr "Kogge Stone Adder:                  "
  printLn $
    analytics {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $
    constructProducing
      {f = \input => IntBits n input -> IntBits n input -> Bit' input -> (IntBits n input, Bit' input)}
      {f' = \input' => autoDer}
      (koggeStoneAdder {n})
  {-
  putStr "Brent Kung Adder:                   "
  printLn $ analytics {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $ constructProducing $ brentKungAdder {n}
  -}

covering
main : IO ()
main = do
  printAnalytics 128
  test 4

{-
exportList : FFI_Export FFI_C "adder.h" []
exportList = Data (PrimType Bit) "bit_t"
  $ Fun fromCBit "fromCBit"
  $ Fun toCBit "toCBit"
  $ Data (PrimType (Bit && Bit)) "bit2_t"
  $ Fun fromCBit2 "fromCBit2"
  $ Fun toCBit2 "toCBit2"
  $ Data (PrimType (Bit && Bit && Bit)) "bit3_t"
  $ Fun fromCBit3 "fromCBit3"
  $ Fun toCBit3 "toCBit3"
  $ Fun bitNot "not"
  $ Fun fullAdder' "fullAdder"
  $ End
  where
    fromCBit : FromCType Bit
    fromCBit = fromCPoly Bit
    toCBit : ToCType Bit
    toCBit = toCPoly Bit
    fromCBit2 : FromCType (Bit && Bit)
    fromCBit2 = fromCPoly (Bit && Bit)
    toCBit2 : ToCType (Bit && Bit)
    toCBit2 = toCPoly (Bit && Bit)
    fromCBit3 : FromCType (Bit && Bit && Bit)
    fromCBit3 = fromCPoly (Bit && Bit && Bit)
    toCBit3 : ToCType (Bit && Bit && Bit)
    toCBit3 = toCPoly (Bit && Bit && Bit)
    -}

