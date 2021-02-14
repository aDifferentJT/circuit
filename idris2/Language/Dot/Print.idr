module Language.Dot.Print

import Data.List
import Data.Maybe
import Language.Dot.AST

%default total

printCompassPoint : CompassPoint -> String
printCompassPoint N  = "n"
printCompassPoint NE = "ne"
printCompassPoint E  = "e"
printCompassPoint SE = "se"
printCompassPoint S  = "s"
printCompassPoint SW = "sw"
printCompassPoint W  = "w"
printCompassPoint NW = "nw"
printCompassPoint C  = "c"

printNodeID : NodeID -> String
printNodeID (MkNodeID ident portID portPt) = ident ++ maybe "" (":" ++) portID ++ maybe "" ((":" ++) . printCompassPoint) portPt

printAttrList : AttrList -> String
printAttrList = concatMap (\as => "[" ++ (concat $ intersperse ";" $ map (\(lhs, rhs) => lhs ++ "=" ++ rhs) $ as) ++ "]")

mutual
  printSubgraph : GraphType -> Subgraph -> String
  printSubgraph directed (ident, stmts) = concat
    [ "subgraph "
    , fromMaybe "" ident
    , " {"
    , (concat $ intersperse ";" $ map (\stmt => printStmt directed $ assert_smaller stmts stmt) $ stmts)
    , "}"
    ]

  printStmt : GraphType -> Stmt -> String
  printStmt _ (NodeStmt ident attrs) = printNodeID ident ++ maybe "" printAttrList attrs
  printStmt directed (EdgeStmt nodes attrs) = concat
    [ concat
    $ intersperse
      ( case directed of
             Undirected => "--"
             Directed   => "->"
      )
    $ map (either printNodeID (\subgraph => printSubgraph directed $ assert_smaller nodes subgraph))
    $ nodes
    , maybe "" printAttrList attrs
    ]
  printStmt _ (Attr t attrs) = concat
    [ case t of
           GraphAttr => "graph"
           NodeAttr  => "node"
           EdgeAttr  => "edge"
    , printAttrList attrs
    ]
  printStmt _ (AssignStmt lhs rhs) = lhs ++ "=" ++ rhs
  printStmt directed (SubgraphStmt subgraph) = printSubgraph directed subgraph

export
printGraph : Graph -> String
printGraph (MkGraph strict directed (ident, stmts)) = concat
  [ if strict then "strict " else ""
  , case directed of
         Undirected => "graph "
         Directed   => "digraph "
  , fromMaybe "" ident
  , " {"
  , concat $ intersperse ";" $ map (\stmt => printStmt directed $ assert_smaller stmts stmt) $ stmts
  , "}"
  ]

