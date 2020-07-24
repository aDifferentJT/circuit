module Verilog

import Circuit
import Control.Monad.ExceptT
import Control.Monad.Random
import Control.Monad.State
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

portNames' : (a : Encodable) -> (b : Encodable) -> PartialIndex a b -> PortType -> List String
portNames' a Bit i Input  = ["in_"  ++ showIdent i]
portNames' a Bit i Output = ["out_" ++ showIdent i]
portNames' a UnitEnc i t = []
portNames' a (b1 && b2) i t = portNames' a b1 (compose i $ LeftIndex EmptyIndex) t ++ portNames' a b2 (compose i $ RightIndex EmptyIndex) t
portNames' a (EncVect n Bit) i Input  = ["in_"  ++ showIdent i]
portNames' a (EncVect n Bit) i Output = ["out_" ++ showIdent i]
portNames' a (EncVect Z b) i t = []
portNames' a (EncVect (S n) b) i t
  =  portNames' a b (compose i $ HeadIndex EmptyIndex) t
  ++ portNames' a (assert_smaller (EncVect (S n) b) $ EncVect n b) (compose i $ TailIndex EmptyIndex) t
portNames' a (NewEnc _ b) i t = portNames' a b (compose i $ NewEncIndex EmptyIndex) t

portNames : Encodable -> PortType -> List String
portNames a = portNames' a a EmptyIndex

portDecls' : (a : Encodable) -> (b : Encodable) -> PartialIndex a b -> PortType -> List String
portDecls' a Bit i Input  = ["input  in_"  ++ showIdent i ++ ";"]
portDecls' a Bit i Output = ["output out_" ++ showIdent i ++ ";"]
portDecls' a UnitEnc i t = []
portDecls' a (b1 && b2) i t = portDecls' a b1 (compose i $ LeftIndex EmptyIndex) t ++ portDecls' a b2 (compose i $ RightIndex EmptyIndex) t
portDecls' a (EncVect (S n) Bit) i Input  = ["input  [" ++ show n ++ ":0] in_"  ++ showIdent i ++ ";"]
portDecls' a (EncVect (S n) Bit) i Output = ["output [" ++ show n ++ ":0] out_" ++ showIdent i ++ ";"]
portDecls' a (EncVect Z b) i t = []
portDecls' a (EncVect (S n) b) i t
  =  portDecls' a b (compose i $ HeadIndex EmptyIndex) t
  ++ portDecls' a (assert_smaller (EncVect (S n) b) $ EncVect n b) (compose i $ TailIndex EmptyIndex) t
portDecls' a (NewEnc _ b) i t = portDecls' a b (compose i $ NewEncIndex EmptyIndex) t

portDecls : Encodable -> PortType -> List String
portDecls a = portDecls' a a EmptyIndex

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
getEncodingBits (BitEncoding x :: xs) = x :: getEncodingBits xs

assignOutputs' : {input : Encodable} -> {output : Encodable} -> {a : Encodable} -> PartialIndex output a -> Encoding (BitType (Either (IndexType input) Bits64)) a -> List String
assignOutputs' {a = Bit} i (BitEncoding x) = ["assign out_" ++ showIdent i ++ " = " ++ getWire x ++ ";"]
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

export
verilog : String -> {input : Encodable} -> {output : Encodable} -> Producing input output -> StateT (List String) RandomM String
verilog name x =
  let (outputBits, internalBits, nl) = netList x in
      map (unlines . concat) $ sequence $ the (List (StateT (List String) RandomM (List String)))
        [ concat <$> traverse
          (\(primName, (primInput ** primOutput ** (f, _, _))) => the (StateT (List String) RandomM (List String)) $ do
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
                     $  portNames primInput Input
                     ++ portNames primOutput Output
                     , [ ");" ]
                     , portDecls primInput Input
                     , portDecls primOutput Output
                     , concat $
                       encodingToList $
                       zipWith
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
                         (IndexTypes {a = primOutput})
                         outputs
                     ]
                   , [ "endmodule"
                     , ""
                     ]
                   ]
          )
          (SortedMap.toList $ SortedMap.fromList $ map (first fst) $ SortedMap.toList nl)
        , pure [ "module " ++ (pack $ filter (not . isSpace) $ unpack name) ]
        , pure $ concat $ map (map ("  " ++)) $ the (List (List String))
          [ mapNilHeadTail ["("] ("( " ++) (", " ++)
          $  portNames input Input
          ++ portNames output Output
          , [ ");" ]
          , portDecls input Input
          , portDecls output Output
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

