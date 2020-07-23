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

encodingToList : {a : Encodable} -> Encoding (BitType t) a -> List t
encodingToList {a = Bit} (BitEncoding x) = [x]
encodingToList UnitEnc = []
encodingToList (x && y) = encodingToList x ++ encodingToList y
encodingToList [] = []
encodingToList (x :: xs) = encodingToList x ++ encodingToList xs
encodingToList (NewEncoding x) = encodingToList x

export
verilog : String -> {input : Encodable} -> {a : Encodable} -> Producing input a -> StateT (List String) RandomM String
verilog name x =
  let (inputBits, internalBits, outputBits, nl) = netList x in
      map (unlines . concat) $ sequence $ the (List (StateT (List String) RandomM (List String)))
        [ concat <$> traverse
          (\(primName, (primInput ** primOutput ** (f, _, _))) => do
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
                     $  (map (("input  in_" ++) . showIdent) $ encodingToList $ IndexTypes {a = primInput})
                     ++ (map (("output out_" ++) . showIdent) $ encodingToList $ IndexTypes {a = primOutput})
                     , [ ");" ]
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
        , pure $ concat $ map (map ("  " ++))
          [ mapNilHeadTail ["("] ("( " ++) (", " ++) $
            (map (("input  " ++) . showHashIdent) $ encodingToList inputBits) ++
            (map (("output " ++) . showHashIdent) $ encodingToList outputBits)
          , [ ");" ]
          , map (("wire " ++) . (++ ";") . showHashIdent) $ SortedSet.toList internalBits
          , concatMap
            (\((primName, primHash), (_ ** _ ** (_, x, y))) => concat
              [ [ primName ++ " " ++ showHashIdent primHash ]
              , concat $ map (map ("  " ++)) $ the (List (List String))
                [ mapNilHeadTail ["("] ("( " ++) (", " ++) $
                  (map (showHashIdent) $ encodingToList x) ++
                  (map (showHashIdent) $ encodingToList y)
                , [ ");" ]
                ]
              ]
            )
            (SortedMap.toList nl)
          ]
        , pure [ "endmodule" ]
        ]

