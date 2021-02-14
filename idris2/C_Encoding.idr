module C_Encoding

import Bit
import Control.Monad.State
import Data.DPair
import Data.List
import Data.SortedMap
import Encodable
import Encoding
import IndexType
import ParseIndex
import Utils

%default total

public export
C_Encoding : Type
C_Encoding = AnyPtr

%foreign "C:mkEncoding, idris2_c_encoding"
mkC_Encoding : Int -> Int -> String -> Int -> (Int -> C_Encoding) -> Int -> PrimIO () -> C_Encoding

encodableType : Encoding _ _ -> Int
encodableType (BitEncoding _) = 0
encodableType UnitEnc = 1
encodableType (_ && _) = 2
encodableType [] = 2
encodableType (_ :: _) = 2
encodableType (NewEncoding _) = 3

newEncLabel : Encoding _ _ -> String
newEncLabel (NewEncoding {ident} _) = ident
newEncLabel _ = ""

countChildren : Encoding _ _ -> Int
countChildren (BitEncoding _) = 0
countChildren UnitEnc = 0
countChildren (_ && UnitEnc) = 1
countChildren (_ && x@(_ && _)) = 1 + assert_total (countChildren x)
countChildren (_ && _) = 2
countChildren [] = 0
countChildren (_ :: xs) = 1 + countChildren xs
countChildren (NewEncoding _) = 1

encodableIdent : Encoding _ _ -> String
encodableIdent (NewEncoding {ident} _) = ident
encodableIdent _ = ""

encodingBit : Encoding (BitType Bit) a -> Int
encodingBit (BitEncoding (MkBitType x)) =
  case x of
       B0 => 0
       B1 => 1
encodingBit _ = 2

childAt
  :  Encoding (BitType Bit) a
  -> Maybe (IndexType a -> IO ())
  -> Int
  -> (Exists (\b => (Encoding (BitType Bit) b, Maybe (IndexType b -> IO ()))))
childAt {a = a && _} (x && _) flip 0 = Evidence a (x, (. LeftIndex) <$> flip)
childAt {a = _ && _ && _} (_ && x@(_ && _)) flip i = childAt x ((. RightIndex) <$> flip) (i - 1)
childAt {a = _ && a} (_ && x) flip 1 = Evidence a (x, (. RightIndex) <$> flip)
childAt {a = EncVect (S _) a} (x :: _) flip 0 = Evidence a (x, (. HeadIndex) <$> flip)
childAt (_ :: xs) flip i = childAt xs ((. TailIndex) <$> flip) (i - 1)
childAt {a = NewEnc _ a} (NewEncoding x) flip 0 = Evidence a (x, (. NewEncIndex) <$> flip)
childAt _ _ _ = Evidence UnitEnc (UnitEnc, Nothing)

export
packEncoding : Encoding (BitType Bit) a -> Maybe (IndexType a -> IO ()) -> C_Encoding
packEncoding x flip =
  mkC_Encoding
    (encodableType x)
    (countChildren x)
    (encodableIdent x)
    (encodingBit x)
    (\i => let Evidence _ (y, flip') = childAt x flip i in
               packEncoding (assert_smaller x y) flip'
    )
    (maybe 0 (\_ => 1) flip)
    (toPrim $ case x of
                  BitEncoding (MkBitType _) => maybe (putStrLn "Cannot edit non-editable") ($ EmptyIndex) flip
                  _ => putStrLn "Cannot flip non-bit"
    )

