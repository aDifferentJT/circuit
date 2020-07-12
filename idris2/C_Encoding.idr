module C_Encoding
import Debug.Trace

import Bit
import Control.Monad.State
import Data.List
import Data.SortedMap
import Encodable
import Encoding
import IndexType
import ParseIndex
import System.FFI
import Utils

%default total

traceShowId : Show a => a -> a
traceShowId x = trace (show x) x

public export
C_Encoding : Type
C_Encoding = Struct "Encoding"
  [ ("numDescendants", Int)
  , ("types", AnyPtr)
  , ("numChildren", AnyPtr)
  , ("idents", AnyPtr)
  , ("indexToIdent", AnyPtr)
  , ("bits", AnyPtr)
  , ("children", AnyPtr)
  , ("editable", Int)
  , ("bitButtons", AnyPtr)
  , ("flipBitAt", AnyPtr)
  ]

%foreign "C:mkEncoding, gui"
mkC_Encoding : Int -> String -> String -> Int -> String -> String -> String -> String -> Int -> (String -> PrimIO ()) -> C_Encoding

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

encodableIdent : Encodable -> State (String, SortedMap String Int) Int
encodableIdent (NewEnc ident _) = (lookup ident . snd <$> get) >>= f
  where
    f : Maybe Int -> State (String, SortedMap String Int) Int
    f Nothing = do
      n <- cast . length . fst <$> get
      modify ((++ ident ++ "\0") *** insert ident n)
      pure n
    f (Just i) = pure i
encodableIdent _ = pure 0

encodingBit : {a : Encodable} -> Encoding (BitType Bit) a -> Int
encodingBit {a = Bit} (BitEncoding x) =
  case x of
       B0 => 0
       B1 => 1
encodingBit _ = 2

children : {a : Encodable} -> Encoding (BitType Bit) a -> List (b : Encodable ** Encoding (BitType Bit) b)
children (BitEncoding _) = []
children UnitEnc = []
children {a = a && UnitEnc} (x && UnitEnc) = [(a ** x)]
children {a = a && _ && _} (x && ys) = (a ** x) :: children ys
children {a = a && b} (x && y) = [(a ** x), (b ** y)]
children [] = []
children {a = EncVect _ a} (x :: xs) = (a ** x) :: children xs
children {a = NewEnc _ a} (NewEncoding x) = [(a ** x)]

record PackedEncoding where
  constructor MkPackedEncoding
  type : Int
  numChildren : Int
  indexToIdent : Int
  bit : Int
  indexToChildren : Int

Show PackedEncoding where
  show x = show (type x, numChildren x, bit x, indexToChildren x)

packEncoding''
  :  (a : Encodable ** Encoding (BitType Bit) a)
  -> State (List (a : Encodable ** Encoding (BitType Bit) a)) (Int -> State (String, SortedMap String Int) PackedEncoding)
packEncoding'' (a ** x) = do
  m <- the Int . cast . List.length <$> get
  modify (++ children x)
  pure (\n => pure $ MkPackedEncoding (encodableType a) (countChildren a) !(encodableIdent a) (encodingBit x) (m + n))

packEncoding'
  :  Int
  -> List (a : Encodable ** Encoding (BitType Bit) a)
  -> State (String, SortedMap String Int) (List PackedEncoding)
packEncoding' _ [] = pure []
packEncoding' n xs =
  let (ys, zs) = runState (traverse packEncoding'' xs) [] in
      let n' = n + cast (length ys) in
          pure $ !(traverse ($ n') ys) ++ !(packEncoding' n' (assert_smaller xs zs))

export
packEncoding : {a : Encodable} -> Encoding (BitType Bit) a -> Maybe (IndexType a -> IO ()) -> C_Encoding
packEncoding x flip =
  let (xs, idents, _) = runState (packEncoding' 0 [(a ** x)]) ("", empty) in
      mkC_Encoding
        (cast $ length xs)
        (pack $ map (chr . type) $ xs)
        (pack $ map (chr . numChildren) $ xs)
        (cast $ length idents)
        (traceShowId idents)
        (pack $ map (chr . indexToIdent) $ xs)
        (pack $ map (chr . bit) $ xs)
        (pack $ map (chr . indexToChildren) $ xs)
        (maybe 0 (\_ => 1) flip)
        ( maybe
          (\_ => toPrim $ putStrLn "Cannot edit non-editable")
          (\flip', x => toPrim $ either putStrLn flip' $ parseIndex' a $ map ((`minus` 1) . fromInteger . cast . ord) $ unpack x)
          flip
        )

export
packBits : {a : Encodable} -> Encoding (BitType Bit) a -> String
packBits x =
  let (xs, _) = runState (packEncoding' 0 [(a ** x)]) ("", empty) in
      (pack $ map (chr . bit) $ xs)

