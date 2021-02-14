module ZXCircuit

import Circuit
import Data.Hash
import Data.SortedMap
import Data.SortedSet
import IndexType
import JSON
import LinearUtils
import Utils
import Wires

%default total

public export
data NodeType = Z | X

Dup NodeType where
  dup Z = Z # Z
  dup X = X # X

  release Z = MkUnrestricted Z
  release X = MkUnrestricted X

export
Show NodeType where
  show Z = "Z"
  show X = "X"

public export
QBit : Encodable -> Type
QBit input = ProducingBit (\_, _ => NodeType) input Bit

export
zxPrimitive
  :  String
  -> NodeType
  -> (0 input : Encodable)
  -> {auto t' : LinearEncodingBuilder (ProducingBit (\_, _ => NodeType) input Bit) t}
  -> t
zxPrimitive name node input =
    deconstructLinearEncodingFunction $
    \x => let MkUnrestricted x' = release x in
              map (BitProducedFrom $ zxPrimitive' x') IndexTypes
  where
    zxPrimitive' : Producing (\_, _ => NodeType) input (linearBuilderInput @{t'}) -> Primitive (\_, _ => NodeType) input (linearBuilderInput @{t'}) (linearBuilderOutput @{t'})
    zxPrimitive' x = MkPrimitive
      name
      (addSalt (hash name) (hash @{HashableEncoding} x))
      node
      x

QGraph : JSONType
QGraph = JSONObject
  [ ( "wire_vertices"
    , JSONDict
      ( JSONObject
        [ ( "annotation"
          , JSONObject
            [ ( "boundary"
              , JSONBool
              )
            , ( "coord"
              , JSONArray JSONNumber
              )
            , ( "input"
              , JSONBool
              )
            , ( "output"
              , JSONBool
              )
            ]
          )
        ]
      )
    )
  , ( "node_vertices"
    , JSONDict
      ( JSONObject
        [ ( "annotation"
          , JSONObject
            [ ( "coord"
              , JSONArray JSONNumber
              )
            ]
          )
        , ( "data"
          , JSONObject
            [ ( "type"
              , JSONString
              )
            , ( "value"
              , JSONString
              )
            ]
          )
        ]
      )
    )
  , ( "undir_edges"
    , JSONDict
      ( JSONObject
        [ ( "src"
          , JSONString
          )
        , ( "tgt"
          , JSONString
          )
        ]
      )
    )
  , ( "scalar"
    , JSONString
    )
  ]


terminusComposeIndex
  :  Terminus input output a
  -> PartialIndex a b
  -> Terminus input output b
terminusComposeIndex (InputTerminus i1) i2 = InputTerminus $ compose i1 i2
terminusComposeIndex (OutputTerminus i1) i2 = OutputTerminus $ compose i1 i2
terminusComposeIndex (PrimTerminus name h a i1) i2 = PrimTerminus name h a $ compose i1 i2

splitWireToBits
  :  Wire input output
  -> List (Terminus input output Bit, Terminus input output Bit)
splitWireToBits (MkWire {width = Bit} src tgt) = [(src, tgt)]
splitWireToBits (MkWire {width = UnitEnc} src tgt) = []
splitWireToBits (MkWire {width = (a && b)} src tgt) = assert_total
  $  splitWireToBits (MkWire (terminusComposeIndex src $ LeftIndex EmptyIndex) (terminusComposeIndex tgt $ LeftIndex EmptyIndex))
  ++ splitWireToBits (MkWire (terminusComposeIndex src $ RightIndex EmptyIndex) (terminusComposeIndex tgt $ RightIndex EmptyIndex))
splitWireToBits (MkWire {width = (EncVect Z a)} src tgt) = []
splitWireToBits (MkWire {width = (EncVect (S n) a)} src tgt) = assert_total
  $  splitWireToBits (MkWire (terminusComposeIndex src $ HeadIndex EmptyIndex) (terminusComposeIndex tgt $ HeadIndex EmptyIndex))
  ++ splitWireToBits (MkWire (terminusComposeIndex src $ TailIndex EmptyIndex) (terminusComposeIndex tgt $ TailIndex EmptyIndex))
splitWireToBits (MkWire {width = (NewEnc _ a)} src tgt) = assert_total
  $ splitWireToBits $ MkWire (terminusComposeIndex src $ NewEncIndex EmptyIndex) (terminusComposeIndex tgt $ NewEncIndex EmptyIndex)

export
toQGraph
  :  {input : Encodable}
  -> {output : Encodable}
  -> Producing (\_, _ => NodeType) input output
  -> JSONValue QGraph
toQGraph x =
  let (nodes, ws) = wires x in
      [ ( "wire_vertices"
        , JSONMkDict
          $  ( map
               (\i =>
                 ( "in_" ++ showIdent i
                 , [ ( "annotation"
                     , [ ("boundary", JSONMkBool True)
                       , ("coord", [-1, 1])
                       , ("input", JSONMkBool True)
                       , ("output", JSONMkBool False)
                       ]
                     )
                   ]
                 )
               )
             $ encodingToList
             $ IndexTypes {a = input}
             )
          ++ ( map
               (\i =>
                 ( "out_" ++ showIdent i
                 , [ ( "annotation"
                     , [ ("boundary", JSONMkBool True)
                       , ("coord", [-1, 1])
                       , ("input", JSONMkBool False)
                       , ("output", JSONMkBool True)
                       ]
                     )
                   ]
                 )
               )
             $ encodingToList
             $ IndexTypes {a = output}
             )
        )
      , ( "node_vertices"
        , JSONMkDict
        $ map
          (\(h, (_ ** _ ** MkPrimitive _ _ zxType _)) =>
            ( showHashIdent h
            , [ ( "annotation"
                , [("coord", [-1, 1])]
                )
              , ( "data"
                , [ ("type", JSONMkString $ show zxType)
                  , ("value", "0")
                  ]
                )
              ]
            )
          )
        $ toList nodes
        )
      , ( "undir_edges"
        , JSONMkDict
        $ zipWithIndex
          (\i, (src, tgt) =>
            ( "e" ++ show i
            , [ ( "src"
                , JSONMkString $ case src of
                    InputTerminus i => "in_" ++ showIdent i
                    OutputTerminus i => "out_" ++ showIdent i
                    PrimTerminus _ h _ _ => showHashIdent h
                )
              , ( "tgt"
                , JSONMkString $ case tgt of
                    InputTerminus i => "in_" ++ showIdent i
                    OutputTerminus i => "out_" ++ showIdent i
                    PrimTerminus _ h _ _ => showHashIdent h
                )
              ]
            )
          )
        $ concatMap splitWireToBits
        $ toList ws
        )
      , ( "scalar"
        , "{\"power2\": 0, \"phase\": \"0\"}"
        )
      ]

export
linearConstructProducing
  :  {0 f : Encodable -> Type}
  -> {auto f' : (0 input' : Encodable) -> LinearEncodingBuilder (ProducingBit prim input' Bit) (f input')}
  -> {input : Encodable}
  -> {auto 0 isInputToT : linearBuilderInput @{f' input} = input}
  -> ((0 input' : Encodable) -> f input')
  -> Producing prim input (linearBuilderOutput @{f' input})
linearConstructProducing g = constructLinearEncodingFunction @{f' input} (g input) $ rewrite isInputToT in inputProducing

