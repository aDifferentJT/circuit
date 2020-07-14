
import Circuit
import C_Circuit
import Data.Vect
import GUI
import IndexType
import Utils

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

testPure : (n : Nat) -> PrimType (IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc) -> PrimType (IntBitsEnc n && Bit)
testPure n = simulate {f = \input => IntBits n input -> IntBits n input -> Bit' input -> (IntBits n input, Bit' input)} {f' = \input' => autoDer} (IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc) $ rippleAdder {n}

test : (n : Nat) -> IO ()
test n = guiSimulate "Ripple Adder" {f = \input => IntBits n input -> IntBits n input -> Bit' input -> (IntBits n input, Bit' input)} {f' = \input' => autoDer} (IntBitsEnc n && IntBitsEnc n && Bit && UnitEnc) (rippleAdder {n})

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
  test 4

