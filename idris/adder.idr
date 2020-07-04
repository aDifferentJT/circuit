
import Circuit
import C_Circuit
import PartialIndex
import Pretty

not : Bit ~> Bit
not = primitive {a = Bit} {b = Bit} "not" bitNot

fullAdder' : (Bit & Bit & Bit) ~~> (Bit & Bit)
fullAdder' (B0, B0, B0) = (B0, B0)
fullAdder' (B0, B0, B1) = (B1, B0)
fullAdder' (B0, B1, B0) = (B1, B0)
fullAdder' (B0, B1, B1) = (B0, B1)
fullAdder' (B1, B0, B0) = (B1, B0)
fullAdder' (B1, B0, B1) = (B0, B1)
fullAdder' (B1, B1, B0) = (B0, B1)
fullAdder' (B1, B1, B1) = (B1, B1)

fullAdder : (Bit & Bit & Bit) ~> (Bit & Bit)
fullAdder = primitive {a = Bit & Bit & Bit} {b = Bit & Bit} "fullAdder" fullAdder'

IntBits : Nat -> Encodable
IntBits n = NewEnc ("Int " ++ show n) $ EncVect n Bit

rippleAdder : (IntBits n & IntBits n & Bit) ~> (IntBits n & Bit)
rippleAdder (MkNewType [], MkNewType [], c) = (MkNewType [], c)
rippleAdder (MkNewType (x::xs), MkNewType (y::ys), c) =
  let (z, c') = fullAdder (x, y, c) in
  let (MkNewType zs, c'') = rippleAdder (MkNewType xs, MkNewType ys, c') in
  (MkNewType (z::zs), c'')

test : {n : Nat} -> PrimType (IntBits n & IntBits n & Bit) -> IO ()
test {n} = prettySimulate {a = IntBits n & IntBits n & Bit} {b = IntBits n & Bit} rippleAdder emptyIndex

exportList : FFI_Export FFI_C "adder.h" []
exportList = Data (PrimType Bit) "bit_t"
  $ Fun fromCBit "fromCBit"
  $ Fun toCBit "toCBit"
  $ Data (PrimType (Bit & Bit)) "bit2_t"
  $ Fun fromCBit2 "fromCBit2"
  $ Fun toCBit2 "toCBit2"
  $ Data (PrimType (Bit & Bit & Bit)) "bit3_t"
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
    fromCBit2 : FromCType (Bit & Bit)
    fromCBit2 = fromCPoly (Bit & Bit)
    toCBit2 : ToCType (Bit & Bit)
    toCBit2 = toCPoly (Bit & Bit)
    fromCBit3 : FromCType (Bit & Bit & Bit)
    fromCBit3 = fromCPoly (Bit & Bit & Bit)
    toCBit3 : ToCType (Bit & Bit & Bit)
    toCBit3 = toCPoly (Bit & Bit & Bit)

main : IO ()
main = test $ (MkNewType [0,0], MkNewType [0,0], 0)

