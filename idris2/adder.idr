
import Analytics
import Circuit
import CommandLine
import Data.Fin
import Data.List
import Data.LVect
import Data.Nat
import Data.Stream
import Data.Vect
import IndexType
import NatProofs
import LinearUtils
import Utils

%default total

not : (0 input : Encodable) -> Bit' input -> Bit' input
not input = primitive "not" (relax bitNot) input

fullAdder' : Bit -> Bit -> Bit -> LPair Bit Bit
fullAdder' B0 B0 B0 = B0 # B0
fullAdder' B0 B0 B1 = B1 # B0
fullAdder' B0 B1 B0 = B1 # B0
fullAdder' B0 B1 B1 = B0 # B1
fullAdder' B1 B0 B0 = B1 # B0
fullAdder' B1 B0 B1 = B0 # B1
fullAdder' B1 B1 B0 = B0 # B1
fullAdder' B1 B1 B1 = B1 # B1

fullAdder : (0 input : Encodable) -> (Bit' input) -> (Bit' input) -> (Bit' input) -> LPair (Bit' input) (Bit' input)
fullAdder input = primitive "fullAdder" fullAdder' input

data IntBits : Nat -> Encodable -> Type where
  MkInt : (1 _ : LVect n (Bit' input)) -> IntBits n input

IntBitsEnc : Nat -> Encodable
IntBitsEnc n = NewEnc ("Int " ++ show n) $ EncVect n Bit

{n : Nat} -> EncodingValue (Bit' input) (IntBits n input) where
  builderEncodable = IntBitsEnc n
  constructEncodingValue (MkInt x) = NewEncoding $ constructEncodingValue x
  deconstructEncodingValue (NewEncoding x) = MkInt $ deconstructEncodingValue x

rippleAdder
  :  (0 input : Encodable)
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> LPair (IntBits n input) (Bit' input)
rippleAdder input (MkInt []) (MkInt []) c = (MkInt [] # c)
rippleAdder input (MkInt (x :: xs)) (MkInt (y :: ys)) c =
  let (z # c') = fullAdder input x y c in
      let (MkInt zs # c'') = rippleAdder input (MkInt xs) (MkInt ys) c' in
          (MkInt (z :: zs) # c'')


data CarryType
  = Kill
  | Propagate
  | Generate

CarryType' : Encodable -> Type
CarryType' input = LPair (Bit' input) (Bit' input)

EncodingValue Bit CarryType where
  builderEncodable = Bit && Bit
  constructEncodingValue Kill = 0 && 0
  constructEncodingValue Propagate = 1 && 0
  constructEncodingValue Generate = 0 && 1
  deconstructEncodingValue (BitEncoding (MkBitType B0) && BitEncoding (MkBitType B0)) = Kill
  deconstructEncodingValue (BitEncoding (MkBitType B1) && BitEncoding (MkBitType B0)) = Propagate
  deconstructEncodingValue (BitEncoding (MkBitType B1) && BitEncoding (MkBitType B1)) = Propagate
  deconstructEncodingValue (BitEncoding (MkBitType B0) && BitEncoding (MkBitType B1)) = Generate

mergeCarries' : CarryType -> CarryType -> CarryType
mergeCarries' _ Kill      = Kill
mergeCarries' c Propagate = c
mergeCarries' _ Generate  = Generate

mergeCarries : (0 input : Encodable) -> CarryType' input -> CarryType' input -> CarryType' input
mergeCarries input = primitive "mergeCarries" mergeCarries' input

halfAdderLookahead' : Bit -> Bit -> LPair Bit CarryType
halfAdderLookahead' B0 B0 = (B0 # Kill)
halfAdderLookahead' B0 B1 = (B1 # Propagate)
halfAdderLookahead' B1 B0 = (B1 # Propagate)
halfAdderLookahead' B1 B1 = (B0 # Generate)

halfAdderLookahead : (0 input : Encodable) -> Bit' input -> Bit' input -> LPair (Bit' input) (CarryType' input)
halfAdderLookahead input = primitive "halfAdderLookahead" halfAdderLookahead' input

generateCarries : (0 input : Encodable) -> LVect n (Bit' input) -> LVect n (Bit' input) -> LPair (LVect n (Bit' input)) (LVect n (CarryType' input))
generateCarries input xs ys = unzip $ zipWith (halfAdderLookahead input) xs ys

applyCarry' : Bit -> CarryType -> Bit
applyCarry' _ Kill      = B0
applyCarry' c Propagate = c
applyCarry' _ Generate  = B1

applyCarry : (0 input : Encodable) -> Bit' input -> CarryType' input -> Bit' input
applyCarry input = primitive "applyCarry" applyCarry' input

performCarries : (0 input : Encodable) -> Bit' input -> LPair (LVect n (Bit' input)) (LVect n (CarryType' input)) -> LPair (LVect n (Bit' input)) (Bit' input)
performCarries input c (xs # cs) =
  let cs' = c :: map (applyCarry input c) cs in
      ((map fst $ zipWith (halfAdderLookahead input) xs $ init $ cs') # last cs')

carryLookaheadAdder
  :  {n : Nat}
  -> ({0 a : Type} -> (a -> a -> a) -> Vect n a -> Vect n a)
  -> (0 input : Encodable)
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> LPair (IntBits n input) (Bit' input)
carryLookaheadAdder propagate input (MkInt xs) (MkInt ys) c =
  first (relax MkInt) $
  performCarries input c $
  second (vectToLVect . propagate (mergeCarries input) . lVectToVect) $
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
koggeStonePropagation' f (k ** smaller) xs =
  let
    xs' : Vect (k + (n `minus` k)) a
    xs' = rewrite plusMinusCancel n k in xs
  in
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

koggeStonePropagation : {n : Nat} -> (a -> a -> a) -> Vect n a -> Vect n a
koggeStonePropagation f =
  foldl (.) id $
  map (koggeStonePropagation' f) $
  assert_total $
  map (the ((m : Nat ** Dec (LTE m n)) -> (m : Nat ** LTE m n)) $ \(m ** Yes p) => (m ** p)) $
  reverse $
  takeBefore (the ((m : Nat ** Dec (LTE m n)) -> Bool) $ \(m ** p) => isNo p) $
  map (\m => (m ** isLTE m n)) $
  iterate (*2) 1


clearBottomSetBit : {n : Nat} -> Fin n -> Fin n
clearBottomSetBit k =
  let res = cast k `prim__and_Integer` (cast k - 1) in
      fromInteger res {prf = believe_me {a = IsJust (Just res)} ItIsJust}

halfFin : {n : Nat} -> Fin n -> Fin n
halfFin k =
  let res = cast k `div` 2 in
      fromInteger res {prf = believe_me {a = IsJust (Just res)} ItIsJust}

minusFin : Fin n -> (y : Nat) -> Fin (n `minus` y)
minusFin x Z = rewrite minusZeroRight n in x
minusFin FZ (S y) = assert_total $ idris_crash "minusFin"
minusFin (FS x) (S y) = minusFin x y

lteFinToNat : {n : Nat} -> (k : Fin (S n)) -> LTE (finToNat k) n
lteFinToNat FZ = LTEZero
lteFinToNat {n = S _} (FS k) = LTESucc $ lteFinToNat k

brentKungPropagation' : {n : Nat} -> (a -> a -> a) -> Vect n a -> Fin n -> a
brentKungPropagation' f xs FZ = index FZ xs
brentKungPropagation' f xs k =
  let k' = case clearBottomSetBit (FS k) of
                FZ => rewrite sym $ minusZeroRight n in halfFin (FS k) `minusFin` 1
                FS k' => k'
  in
  f (brentKungPropagation' f xs $ assert_smaller k k')
    (brentKungPropagation' f
      (snd $ splitAt (finToNat $ FS k') $ rewrite plusMinusCancel n (finToNat $ FS k') {smaller = lteFinToNat $ FS k'} in xs)
      (assert_smaller k $ k `minusFin` (finToNat $ FS k'))
    )

brentKungPropagation : {n : Nat} -> (a -> a -> a) -> Vect n a -> Vect n a
brentKungPropagation f xs = map (brentKungPropagation' f xs) range


rippleAdder2
  :  {n : Nat}
  -> (0 input : Encodable)
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> LPair (IntBits n input) (Bit' input)
rippleAdder2 = carryLookaheadAdder ripplePropagation

koggeStoneAdder
  :  {n : Nat}
  -> (0 input : Encodable)
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> LPair (IntBits n input) (Bit' input)
koggeStoneAdder = carryLookaheadAdder koggeStonePropagation

brentKungAdder
  :  {n : Nat}
  -> (0 input : Encodable)
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> LPair (IntBits n input) (Bit' input)
brentKungAdder = carryLookaheadAdder brentKungPropagation

covering
test : (n : Nat) -> IO ()
test n = commandLine "Carry Lookahead Adder" {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $ constructProducing $ brentKungAdder {n}

printAnalytics : Nat -> IO ()
printAnalytics n = do
  putStr "Ripple Adder:                       "
  printLn $ analytics {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $ constructProducing {prim = BinarySimPrim} $ rippleAdder {n}
  putStr "Carry Lookahead overhead:           "
  printLn $ analytics {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $ constructProducing {prim = BinarySimPrim} $ carryLookaheadAdder {n} (const id)
  putStr "Carry Lookahead style Ripple Adder: "
  printLn $ analytics {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $ constructProducing {prim = BinarySimPrim} $ rippleAdder2 {n}
  putStr "Kogge Stone Adder:                  "
  printLn $ analytics {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $ constructProducing {prim = BinarySimPrim} $ koggeStoneAdder {n}
  putStr "Brent Kung Adder:                   "
  printLn $ analytics {input = IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc} $ constructProducing {prim = BinarySimPrim} $ brentKungAdder {n}

covering
main : IO ()
main = do
  printAnalytics 10
  test 4

