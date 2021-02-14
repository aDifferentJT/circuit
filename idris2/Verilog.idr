module Verilog

import Circuit
import Control.Monad.ExceptT
import Control.Monad.Random
import Control.Monad.State
import Data.DPair
import Data.Hash
import Data.List
import Data.SortedMap
import Data.SortedSet
import Data.Strings
import Data.Vect
import Encodable
import IndexType
import MinimisePrimitive
import NetList
import Utils

%default total
%ambiguity_depth 10

mapNilHeadTail : List b -> (a -> b) -> (a -> b) -> List a -> List b
mapNilHeadTail xs f g [] = xs
mapNilHeadTail _ f g (x :: xs) = f x :: map g xs

data PortType = Input | Output

portNames' : PortType -> (b : Encodable) -> PartialIndex a b -> List String
portNames' Input  Bit i = ["in_"  ++ showIdent i]
portNames' Output Bit i = ["out_" ++ showIdent i]
portNames' t UnitEnc i = []
portNames' t (b1 && b2) i
  =  (portNames' t b1 $ compose i $ LeftIndex EmptyIndex)
  ++ (portNames' t b2 $ compose i $ RightIndex EmptyIndex)
portNames' Input  (EncVect n Bit) i = ["in_"  ++ showIdent i]
portNames' Output (EncVect n Bit) i = ["out_" ++ showIdent i]
portNames' t (EncVect Z b) i = []
portNames' t (EncVect (S n) b) i
  =  (portNames' t b $ compose i $ HeadIndex EmptyIndex)
  ++ (portNames' t (assert_smaller (EncVect (S n) b) $ EncVect n b) $ compose i $ TailIndex EmptyIndex)
portNames' t (NewEnc _ b) i = portNames' t b (compose i $ NewEncIndex EmptyIndex)

portNames : PortType -> Encodable -> List String
portNames t a = portNames' t a EmptyIndex

portDecls' : PortType -> (b : Encodable) -> PartialIndex a b -> List String
portDecls' Input  Bit i = ["input  in_"  ++ showIdent i ++ ";"]
portDecls' Output Bit i = ["output out_" ++ showIdent i ++ ";"]
portDecls' t UnitEnc i = []
portDecls' t (b1 && b2) i
  =  (portDecls' t b1 $ compose i $ LeftIndex EmptyIndex)
  ++ (portDecls' t b2 $ compose i $ RightIndex EmptyIndex)
portDecls' Input  (EncVect (S n) Bit) i = ["input  [" ++ show n ++ ":0] in_"  ++ showIdent i ++ ";"]
portDecls' Output (EncVect (S n) Bit) i = ["output [" ++ show n ++ ":0] out_" ++ showIdent i ++ ";"]
portDecls' t (EncVect Z b) i = []
portDecls' t (EncVect (S n) b) i
  =  (portDecls' t b $ compose i $ HeadIndex EmptyIndex)
  ++ (portDecls' t (assert_smaller (EncVect (S n) b) $ EncVect n b) $ compose i $ TailIndex EmptyIndex)
portDecls' t (NewEnc _ b) i = portDecls' t b (compose i $ NewEncIndex EmptyIndex) 

portDecls : PortType -> Encodable -> List String
portDecls t a = portDecls' t a EmptyIndex

getWire' : {a : Encodable} -> IndexType a -> (List String, Maybe Nat)
getWire' EmptyIndex = ([], Nothing)
getWire' (LeftIndex  i) = first ("Left"  ::) $ getWire' i
getWire' (RightIndex i) = first ("Right" ::) $ getWire' i
getWire' {a = EncVect _ Bit} (HeadIndex i) = ([], Just Z)
getWire' {a = EncVect _ Bit} (TailIndex i) = second (map S) $ getWire' i
getWire' (HeadIndex  i) = first ("Head"  ::) $ getWire' i
getWire' (TailIndex  i) = first ("Tail"  ::) $ getWire' i
getWire' {a = NewEnc ident _} (NewEncIndex i) = first ((pack $ filter (not . isSpace) $ unpack ident) ::) $ getWire' i

getWire : {input : Encodable} -> Either (IndexType input) Bits64 -> String
getWire (Left i) =
  let (ident, index) = getWire' i in
      "in_" ++ (concat $ intersperse "_" ident) ++ maybe "" (\index' => "[" ++ show index' ++ "]") index
getWire (Right h) = showHashIdent h

getEncodingBits : Encoding (BitType t) (EncVect n Bit) -> Vect n t
getEncodingBits [] = []
getEncodingBits (BitEncoding (MkBitType x) :: xs) = x :: getEncodingBits xs

assignOutputs' : {input : Encodable} -> {output : Encodable} -> {a : Encodable} -> PartialIndex output a -> Encoding (BitType (Either (IndexType input) Bits64)) a -> List String
assignOutputs' {a = Bit} i (BitEncoding (MkBitType x)) = ["assign out_" ++ showIdent i ++ " = " ++ getWire x ++ ";"]
assignOutputs' i UnitEnc = []
assignOutputs' i (x && y) = assignOutputs' (compose i $ LeftIndex EmptyIndex) x ++ assignOutputs' (compose i $ RightIndex EmptyIndex) y
assignOutputs' {a = EncVect _ Bit} i xs
  =  [ "assign out_" ++ showIdent i ++ " =" ]
  ++ ( mapNilHeadTail ["  {"] ("  { " ++) ("  , " ++)
     $ toList
     $ reverse
     $ map getWire
     $ getEncodingBits xs
     )
  ++ [ "  };" ]
assignOutputs' i [] = []
assignOutputs' i (x :: xs) = assignOutputs' (compose i $ HeadIndex EmptyIndex) x ++ assignOutputs' (compose i $ TailIndex EmptyIndex) xs
assignOutputs' i (NewEncoding x) = assignOutputs' (compose i $ NewEncIndex EmptyIndex) x

assignOutputs : {input : Encodable} -> {output : Encodable} -> Encoding (BitType (Either (IndexType input) Bits64)) output -> List String
assignOutputs = assignOutputs' EmptyIndex

processNetListEntry
  :  ( String
     , (  a : Encodable
       ** b : Encodable
       ** ( BinarySimPrim a b
          , Encoding (BitType (Either (IndexType input) Bits64)) a
          , Encoding (BitType Bits64) b
          )
       )
     )
  -> StateT (List String) RandomM (List String)
processNetListEntry (primName, (primInput ** primOutput ** (f, _, _))) = do
  res <- lift $ runExceptT $ minimisePrimitive f
  case res of
       Left e => do
         modify (("Failed to analyse primitive: " ++ primName) ::)
         modify (e ::)
         pure []
       Right outputs => pure $ concat $ the (List (List String))
         [ [ "module " ++ primName ]
         , concat $ map (map ("  " ++)) $ the (List (List String))
           [ mapNilHeadTail ["("] ("( " ++) (", " ++)
           $  portNames Input primInput
           ++ portNames Output primOutput
           , [ ");" ]
           , portDecls Input primInput
           , portDecls Output primOutput
           , concat
           $ encodingToList
           $ mapWithIndex
               (\dest, formula => concat $ the (List (List String))
                 [ [ "assign " ++ ("out_" ++ showIdent dest) ]
                 , concat $ map (map ("  " ++)) $ the (List (List String))
                   [ concat
                   $ mapNilHeadTail
                       [["= 0"]]
                       (mapNilHeadTail ["= 0"] ("=  " ++) ("   " ++))
                       (mapNilHeadTail [] ("|| " ++) ("   " ++))
                   $ map ((++ [")"]) . mapNilHeadTail ["1"] ("(  " ++) ("&& " ++))
                   $ map
                       ( map
                         ( (the (Literal String -> String) $ \lit => case lit of
                             Pos x => " " ++ x
                             Neg x => "!" ++ x
                           )
                         . map (("in_" ++) . showIdent)
                         )
                       )
                   $ formula
                   , [ ";" ]
                   ]
                 ]
               )
               outputs
           ]
         , [ "endmodule"
           , ""
           ]
         ]
export
verilog : String -> {input : Encodable} -> {output : Encodable} -> Producing BinarySimPrim input output -> StateT (List String) RandomM String
verilog name x =
  let ((internalBits, nl), outputBits) = netList x in
      map (unlines . concat) $ sequence $ the (List (StateT (List String) RandomM (List String)))
        [ concat <$> traverse processNetListEntry
          (SortedMap.toList $ SortedMap.fromList $ map (first fst) $ SortedMap.toList nl)
        , pure [ "module " ++ (pack $ filter (not . isSpace) $ unpack name) ]
        , pure $ concat $ map (map ("  " ++)) $ the (List (List String))
          [ mapNilHeadTail ["("] ("( " ++) (", " ++)
          $  portNames Input input
          ++ portNames Output output
          , [ ");" ]
          , portDecls Input input
          , portDecls Output output
          , map (("wire " ++) . (++ ";") . showHashIdent) $ SortedSet.toList internalBits
          , assignOutputs outputBits
          , concatMap
            (\((primName, primHash), (_ ** _ ** (_, x, y))) => concat $ the (List (List String))
              [ [ primName ++ " " ++ showHashIdent primHash ]
              , concat $ map (map ("  " ++)) $ the (List (List String))
                [ mapNilHeadTail ["("] ("( " ++) (", " ++)
                $  (map getWire $ encodingToList {t = Either (IndexType input) Bits64} x)
                ++ (map showHashIdent $ encodingToList y)
                , [ ");" ]
                ]
              ]
            )
            (SortedMap.toList nl)
          ]
        , pure [ "endmodule" ]
        ]

