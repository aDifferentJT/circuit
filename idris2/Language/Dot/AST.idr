module Language.Dot.AST

import Data.Hash
import Data.List

%default total

public export
ID : Type
ID = String

public export
data CompassPoint
  = N
  | NE
  | E
  | SE
  | S
  | SW
  | W
  | NW
  | C

export
Eq CompassPoint where
  N  == N  = True
  NE == NE = True
  E  == E  = True
  SE == SE = True
  S  == S  = True
  SW == SW = True
  W  == W  = True
  NW == NW = True
  C  == C  = True
  _  == _  = False

compassPointToNat : CompassPoint -> Nat
compassPointToNat N  = 0
compassPointToNat NE = 1
compassPointToNat E  = 2
compassPointToNat SE = 3
compassPointToNat S  = 4
compassPointToNat SW = 5
compassPointToNat W  = 6
compassPointToNat NW = 7
compassPointToNat C  = 8

export
Ord CompassPoint where
  compare x y = compare (compassPointToNat x) (compassPointToNat y)

export
Hashable CompassPoint where
  hash x = hash $ compassPointToNat x

public export
data NodeID = MkNodeID ID (Maybe ID) (Maybe CompassPoint)

export
Eq NodeID where
  (MkNodeID ident1 portID1 portPt1) == (MkNodeID ident2 portID2 portPt2)
    =  ident1 == ident1
    && portID1 == portID2
    && portPt1 == portPt2

export
Ord NodeID where
  compare (MkNodeID ident1 portID1 portPt1) (MkNodeID ident2 portID2 portPt2)
    = compare (ident1, portID1, portPt1) (ident2, portID2, portPt2)

export
Hashable NodeID where
  hash (MkNodeID ident portID portPt) = hash (ident, portID, portPt)

public export
AttrList : Type
AttrList = List (List (ID, ID))

public export
Subgraph' : Type -> Type
Subgraph' stmt = (Maybe ID, List stmt)

public export
data AttrType
  = GraphAttr
  | NodeAttr
  | EdgeAttr
  
public export
data Stmt : Type where
  NodeStmt : NodeID -> Maybe AttrList -> Stmt
  EdgeStmt : (nodes : List (Either NodeID (Subgraph' Stmt))) -> {auto 0 nonEmpty : NonEmpty nodes} -> Maybe AttrList -> Stmt
  Attr : AttrType -> AttrList -> Stmt
  AssignStmt : ID -> ID -> Stmt
  SubgraphStmt : Subgraph' Stmt -> Stmt

public export
Subgraph : Type
Subgraph = Subgraph' Stmt

public export
data GraphType = Undirected | Directed

public export
data Graph : Type where
  MkGraph : (strict : Bool) -> GraphType -> Subgraph -> Graph

