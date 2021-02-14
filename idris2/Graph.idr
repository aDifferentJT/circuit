module Graph

import Circuit
import Control.Monad.Random
import Control.Monad.State
import Data.DPair
import Data.Hash
import Data.List
import Data.Maybe
import Data.SortedMap
import Data.SortedSet
import Encodable
import EqOrdUtils
import IndexType
import Language.Dot.AST
import Language.Dot.Print
import Utils
import Wires

%default total
%ambiguity_depth 10

data End = Sink | Src

Show End where
  show Sink = "sink"
  show Src = "src"

record Nodes (input : Encodable) (output : Encodable) where
  constructor MkNodes
  inputs  : SortedMap NodeID (Exists $ PartialIndex input)
  outputs : SortedMap NodeID (Exists $ PartialIndex output)
  primitives :
    SortedMap Bits64
      ( String
      , Maybe (Exists (\primInput => SortedMap NodeID (Exists $ PartialIndex primInput)))
      , Maybe (Exists (\primOutput => SortedMap NodeID (Exists $ PartialIndex primOutput)))
      )

terminusNode
  :  End
  -> {width : Encodable}
  -> Terminus input output width
  -> State (Nodes input output) NodeID
terminusNode s (InputTerminus i) = do
  let ident = MkNodeID (show s ++ "_in_" ++ showIdent i) Nothing Nothing
  modify $ record { inputs $= insert ident (Evidence width i) }
  pure ident
terminusNode s (OutputTerminus i) = do
  let ident = MkNodeID (show s ++ "_out_" ++ showIdent i) Nothing Nothing
  modify $ record { outputs $= insert ident (Evidence width i) }
  pure ident
terminusNode s (PrimTerminus name h a i) = do
  let ident = MkNodeID (show s ++ "_" ++ (showHashIdent $ hash (h, i))) Nothing Nothing
  (name', sinks, srcs) <- fromMaybe (name, Nothing, Nothing) . lookup h . primitives <$> get
  case s of
       Sink =>
         case sinks of
              Nothing =>
                modify $ record { primitives $= insert h (name', Just $ Evidence a $ singleton ident $ Evidence width i, srcs) }
              Just (Evidence a' sinks') =>
                case unsafeAssumeEq a a' of
                     Refl => modify $ record { primitives $= insert h (name', Just $ Evidence a' $ insert ident (Evidence width i) sinks', srcs) }
       Src  => do
         case srcs of
              Nothing => modify $ record { primitives $= insert h (name', sinks, Just $ Evidence a $ singleton ident $ Evidence width i) }
              Just (Evidence a' srcs') =>
                case unsafeAssumeEq a a' of
                     Refl => modify $ record { primitives $= insert h (name', sinks, Just $ Evidence a' $ insert ident (Evidence width i) srcs') }
  pure ident

wireStmt
  :  {input : Encodable}
  -> {output : Encodable}
  -> Wire input output
  -> State (Nodes input output) Stmt
wireStmt (MkWire i o) = pure $ EdgeStmt [Left !(terminusNode Src i), Left !(terminusNode Sink o)] {nonEmpty = IsNonEmpty} Nothing

partitionLeftRight : List (NodeID, Exists $ PartialIndex (a && b)) -> (List NodeID, List (NodeID, Exists $ PartialIndex a), List (NodeID, Exists $ PartialIndex b))
partitionLeftRight [] = ([], [], [])
partitionLeftRight ((ident, Evidence (a && b) EmptyIndex) :: xs) = first (ident ::) $ partitionLeftRight xs
partitionLeftRight ((ident, Evidence width (LeftIndex x)) :: xs) = second (first ((ident, Evidence width x) ::)) $ partitionLeftRight xs
partitionLeftRight ((ident, Evidence width (RightIndex x)) :: xs) = second (second ((ident, Evidence width x) ::)) $ partitionLeftRight xs

partitionHeadTail : List (NodeID, (Exists $ PartialIndex (EncVect (S n) a))) -> (List NodeID, List (NodeID, Exists $ PartialIndex a), List (NodeID, Exists $ PartialIndex $ EncVect n a))
partitionHeadTail [] = ([], [], [])
partitionHeadTail ((ident, Evidence (EncVect (S n) a) EmptyIndex) :: xs) = first (ident ::) $ partitionHeadTail xs
partitionHeadTail ((ident, Evidence width (HeadIndex x)) :: xs) = second (first ((ident, Evidence width x) ::)) $ partitionHeadTail xs
partitionHeadTail ((ident, Evidence width (TailIndex x)) :: xs) = second (second ((ident, Evidence width x) ::)) $ partitionHeadTail xs

partitionNewEncIndex : List (NodeID, (Exists $ PartialIndex (NewEnc newEncIndex a))) -> (Maybe String, List NodeID, List (NodeID, Exists $ PartialIndex a))
partitionNewEncIndex [] = (Nothing, [], [])
partitionNewEncIndex ((ident, Evidence (NewEnc _ a) EmptyIndex) :: xs) = second (first (ident ::)) $ partitionNewEncIndex xs
partitionNewEncIndex ((ident, Evidence width (NewEncIndex x)) :: xs) = first (const $ Just newEncIndex) $ second (second ((ident, Evidence width x) ::)) $ partitionNewEncIndex xs

record NodeTree where
  constructor MkNodeTree
  root : NodeID
  attrs : Maybe AttrList
  children : List NodeTree

nodeTreeStmts : (reversed : Bool) -> NodeTree -> List Stmt
nodeTreeStmts reversed tree = concat
  [ [ NodeStmt (root tree) (attrs tree)
    , SubgraphStmt
      ( Nothing
      , concat
        [ [ AssignStmt "rank" "same" ]
        , case children tree of
               [] => []
               cs@(_ :: _) => [ EdgeStmt (map (Left . root) $ cs) Nothing ]
        ]
      )
    ]
  , concatMap
    (\child =>
      EdgeStmt
        ( if reversed
          then [Left $ root child, Left $ root tree]
          else [Left $ root tree, Left $ root child]
        )
        { nonEmpty = if reversed then IsNonEmpty else IsNonEmpty }
        Nothing
      :: (nodeTreeStmts reversed $ assert_smaller tree child)
    )
    (children tree)
  ]

Random NodeID where
  randomIO = do
    ident <- (showHashIdent . prim__cast_IntegerBits64 . cast . the Int) <$> randomIO
    pure $ MkNodeID ident Nothing Nothing

  randomRIO _ = randomIO

mutual
  orderEncPair : List (NodeID, (Exists $ PartialIndex (a && b))) -> RandomM NodeTree
  orderEncPair xs with (partitionLeftRight xs)
    orderEncPair _ | ([], leftNodes, rightNodes) =
      pure $ MkNodeTree !randomM (Just [[("shape", "point")]]) $ !(orderEncoding leftNodes) :: !(orderRight rightNodes)
    orderEncPair _ | (rootNode :: _, leftNodes, rightNodes) =
      pure $ MkNodeTree rootNode (Just [[("shape", "point")]]) $ !(orderEncoding leftNodes) :: !(orderRight rightNodes)

  orderNestedEncPair : List (NodeID, (Exists $ PartialIndex (a && b))) -> RandomM (List NodeTree)
  orderNestedEncPair xs with (partitionLeftRight xs)
    orderNestedEncPair _ | ([], leftNodes, rightNodes) =
      pure $ !(orderEncoding leftNodes) :: !(orderRight rightNodes)
    orderNestedEncPair _ | (rootNode :: _, leftNodes, rightNodes) =
      pure [MkNodeTree rootNode (Just [[("shape", "point")]]) $ !(orderEncoding leftNodes) :: !(orderRight rightNodes)]

  orderEncVect : List (NodeID, (Exists $ PartialIndex (EncVect (S _) a))) -> RandomM NodeTree
  orderEncVect xs with (partitionHeadTail xs)
    orderEncVect _ | ([], headNodes, tailNodes) =
        pure $ MkNodeTree !randomM (Just [[("shape", "point")]]) $ !(orderEncoding headNodes) :: !(orderTail tailNodes)
    orderEncVect _ | (rootNode :: _, headNodes, tailNodes) =
        pure $ MkNodeTree rootNode (Just [[("shape", "point")]]) $ !(orderEncoding headNodes) :: !(orderTail tailNodes)

  orderNestedEncVect : List (NodeID, (Exists $ PartialIndex (EncVect (S _) a))) -> RandomM (List NodeTree)
  orderNestedEncVect xs with (partitionHeadTail xs)
    orderNestedEncVect _ | ([], headNodes, tailNodes) =
      pure $ !(orderEncoding headNodes) :: !(orderTail tailNodes)
    orderNestedEncVect _ | (rootNode :: _, headNodes, tailNodes) =
      pure [MkNodeTree rootNode (Just [[("shape", "point")]]) $ !(orderEncoding headNodes) :: !(orderTail tailNodes)]

  orderNewEnc : List (NodeID, (Exists $ PartialIndex (NewEnc _ a))) -> RandomM NodeTree
  orderNewEnc xs with (partitionNewEncIndex xs)
    orderNewEnc _ | (ident, [], descendentNodes) =
      pure $ MkNodeTree !randomM (Just [[("label", "\"" ++ fromMaybe "???" ident ++ "\"")]]) [!(orderEncoding descendentNodes)]
    orderNewEnc _ | (ident, rootNode :: _, descendentNodes) =
      pure $ MkNodeTree rootNode (Just [[("label", "\"" ++ fromMaybe "???" ident ++ "\"")]]) [!(orderEncoding descendentNodes)]

  orderRight : List (NodeID, (Exists $ PartialIndex a)) -> RandomM (List NodeTree)
  orderRight [] = pure []
  orderRight xs@((ident, Evidence _ (LeftIndex _)) :: _) = orderNestedEncPair xs
  orderRight xs@((ident, Evidence _ (RightIndex _)) :: _) = orderNestedEncPair xs
  orderRight xs = pure [!(orderEncoding xs)]

  orderTail : List (NodeID, (Exists $ PartialIndex a)) -> RandomM (List NodeTree)
  orderTail [] = pure []
  orderTail xs@((ident, Evidence _ (HeadIndex _)) :: _) = orderNestedEncVect xs
  orderTail xs@((ident, Evidence _ (TailIndex _)) :: _) = orderNestedEncVect xs
  orderTail xs = pure [!(orderEncoding xs)]

  orderEncoding : List (NodeID, (Exists $ PartialIndex a)) -> RandomM NodeTree
  orderEncoding [] = pure $ MkNodeTree !randomM Nothing []
  orderEncoding ((ident, Evidence _ EmptyIndex) :: xs) = record {root = ident} <$> orderEncoding xs
  orderEncoding xs@((_, Evidence _ (LeftIndex _)) :: _) = orderEncPair xs
  orderEncoding xs@((_, Evidence _ (RightIndex _)) :: _) = orderEncPair xs
  orderEncoding xs@((_, Evidence _ (HeadIndex _)) :: _) = orderEncVect xs
  orderEncoding xs@((_, Evidence _ (TailIndex _)) :: _) = orderEncVect xs
  orderEncoding xs@((_, Evidence _ (NewEncIndex _)) :: _) = orderNewEnc xs

{-
sinkSrcNodes
  :  ( Bits64
     , String
     , Maybe (Exists (\primInput => SortedMap NodeID (Exists $ PartialIndex primInput)))
     , Maybe (Exists (\primOutput => SortedMap NodeID (Exists $ PartialIndex primOutput)))
     )
  -> List Stmt
sinkSrcNodes (primID, name, sinkNodes, srcNodes) = concat
  [ [ SubgraphStmt
      ( Just $ "cluster_" ++ showHashIdent primID
      , [ AssignStmt "label" $ "\"" ++ name ++ "\""
        , EdgeStmt
          [ Right
            ( Nothing
            , concat
              [ [ AssignStmt "rank" "same" ]
              , let idents =
                  case sinkNodes of
                       Nothing => []
                       Just (Evidence _ x) => keys x
                in
                map (\ident => NodeStmt ident (Just [[("label", "\"\"")]])) idents
              ]
            )
          , Right
            ( Nothing
            , concat
              [ [ AssignStmt "rank" "same" ]
              , let idents =
                  case srcNodes of
                       Nothing => []
                       Just (Evidence _ x) => keys x
                in
                map (\ident => NodeStmt ident (Just [[("label", "\"\"")]])) idents
              ]
            )
          ]
          (Just [[("style", "invis")]])
        ]
      )
    ]
  , case sinkNodes of
         Nothing => []
         Just (Evidence _ x) => snd $ orderEncoding True $ SortedMap.toList x
  , case srcNodes of
         Nothing => []
         Just (Evidence _ x) => snd $ orderEncoding True $ SortedMap.toList x
  ]
  -}

export
graph
  :  {input : Encodable}
  -> {output : Encodable}
  -> Producing prim input output
  -> RandomM String
graph x = do
  let ws = wires x
  let ordDPair = OrdDPair
  let (MkNodes inputs outputs primitives, wireStmts) = runState (MkNodes empty empty empty) $ traverse wireStmt $ SortedSet.toList $ snd ws
  pure $
    printGraph $
    MkGraph False Directed
      ( Nothing
      , concat
        [ wireStmts
        , [ SubgraphStmt
            ( Just "cluster_inputs"
            , concat
              [ [ AssignStmt "label" "\"input\""
                ]
              , nodeTreeStmts False !(orderEncoding $ SortedMap.toList inputs)
              ]
            )
          , SubgraphStmt
            ( Just "cluster_outputs"
            , concat
              [ [ AssignStmt "label" "\"output\""
                ]
              , nodeTreeStmts True !(orderEncoding $ SortedMap.toList outputs)
              ]
            )
          ]
        --, concatMap sinkSrcNodes $ SortedMap.toList primitives
        ]
      )

