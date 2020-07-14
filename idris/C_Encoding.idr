module C_Encoding

import Bit
import Control.Monad.State
import Data.List
import Data.SortedMap
import Encodable
import Encoding
import IndexType
import ParseIndex
import Utils

%default total

%include C "idris_c_encoding.h"
%link C "idris_c_encoding.so"

public export
C_Encoding : Type
C_Encoding = Ptr

encodableType : Encodable -> Int
encodableType Bit = 0
encodableType UnitEnc = 1
encodableType (_ && _) = 2
encodableType (EncVect _ _) = 2
encodableType (NewEnc _ _) = 3

newEncLabel : Encodable -> String
newEncLabel (NewEnc ident _) = ident
newEncLabel _ = ""

countChildren : Encodable -> Int
countChildren (Bit) = 0
countChildren (UnitEnc) = 0
countChildren (_ && UnitEnc) = 1
countChildren (_ && a1 && a2) = 1 + assert_total (countChildren (a1 && a2))
countChildren (_ && _) = 2
countChildren (EncVect n _) = cast n
countChildren (NewEnc _ _) = 1

encodableIdent : Encodable -> String
encodableIdent (NewEnc ident _) = ident
encodableIdent _ = ""

encodingBit : {a : Encodable} -> Encoding (BitType Bit) a -> Int
encodingBit {a = Bit} (BitEncoding x) =
  case x of
       B0 => 0
       B1 => 1
encodingBit _ = 2

childAt
  :  {a : Encodable}
  -> Encoding (BitType Bit) a
  -> Maybe (IndexType a -> IO ())
  -> Int
  -> (b : Encodable ** (Encoding (BitType Bit) b, Maybe (IndexType b -> IO ())))
childAt {a = a && _} (x && _) flip 0 = (a ** (x, (. LeftIndex) <$> flip))
childAt {a = _ && _ && _} (_ && x) flip i = childAt x ((. RightIndex) <$> flip) (i - 1)
childAt {a = _ && a} (_ && x) flip 1 = (a ** (x, (. RightIndex) <$> flip))
childAt {a = EncVect (S _) a} (x :: _) flip 0 = (a ** (x, (. HeadIndex) <$> flip))
childAt (_ :: xs) flip i = childAt xs ((. TailIndex) <$> flip) (i - 1)
childAt {a = NewEnc _ a} (NewEncoding x) flip 0 = (a ** (x, (. NewEncIndex) <$> flip))
childAt _ _ _ = (UnitEnc ** (UnitEnc, Nothing))

C_Context : Type
C_Context = FFI_C.Raw (a : Encodable ** (Encoding (BitType Bit) a, Maybe (IndexType a -> IO ())))

mutual
  childAt' : C_Context -> Int -> C_Encoding
  childAt' (MkRaw (a ** (x, flip))) i = let (_ ** (y, flip')) = childAt x flip i in
                              packEncoding (assert_smaller x y) flip'
  flip' : C_Context -> ()
  flip' (MkRaw (_ ** (_, Nothing))) = unsafePerformIO $ putStrLn "Cannot edit non-editable"
  flip' (MkRaw (Bit ** (_, Just flip))) = unsafePerformIO $ flip EmptyIndex
  flip' (MkRaw (_ ** (_, Just _))) = unsafePerformIO $ putStrLn "Cannot flip non-bit"
  
  export
  packEncoding : {a : Encodable} -> Encoding (BitType Bit) a -> Maybe (IndexType a -> IO ()) -> C_Encoding
  packEncoding {a} x flip =
    unsafePerformIO $ assert_total $ foreign FFI_C "mkEncoding"
      (Int -> Int -> String -> Int -> CFnPtr (C_Context -> Int -> C_Encoding) -> Int -> CFnPtr (C_Context -> ()) -> C_Context -> IO C_Encoding)
      (encodableType a)
      (countChildren a)
      (encodableIdent a)
      (encodingBit x)
      (MkCFnPtr childAt')
      (maybe 0 (\_ => 1) flip)
      (MkCFnPtr flip')
      (MkRaw (a ** (x, flip)))

