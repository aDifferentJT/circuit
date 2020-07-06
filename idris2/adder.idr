
import Circuit
import C_Circuit
import Data.Vect
import IndexType
import Pretty

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

{n : Nat} -> EncodingValue (Bit' input) (IntBits n input) where
  builderEncodable = IntBitsEnc n
  constructEncodingValue (MkInt x) = NewEncoding $ constructEncodingValue x
  deconstructEncodingValue (NewEncoding x) = MkInt $ deconstructEncodingValue x

rippleAdder
  :  (input : Encodable)
  -> IntBits n input
  -> IntBits n input
  -> Bit' input
  -> (IntBits n input, Bit' input)
rippleAdder input (MkInt []) (MkInt []) c = (MkInt [], c)
rippleAdder input (MkInt (x :: xs)) (MkInt (y :: ys)) c =
  let (z, c') = fullAdder input x y c in
      let (MkInt zs, c'') = rippleAdder input (MkInt xs) (MkInt ys) c' in
          (MkInt (z :: zs), c'')

testPure : (n : Nat) -> PrimType (IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc) -> PrimType (IntBitsEnc n && Bit)
testPure n = simulate (IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc) $ rippleAdder {n}

test : (n : Nat) -> PrimType (IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc) -> IO ()
test n = prettySimulate (IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc) (rippleAdder {n}) EmptyIndex

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

main : IO ()
main = do
  test 4 $ replicate 0

