module Minimiser.CDSearch
import Debug.Trace

import Control.Monad.ExceptT
import Control.Monad.Random
import Data.List
import Data.SortedMap
import Minimiser.Literal

%default total

mostFrequent : Ord a => List (List a) -> List a
mostFrequent xss
  = fst
  $ foldl
    ( the ((List a, Nat) -> (a, Nat) -> (List a, Nat))
    $ \(xs, m), (x, n) => case compare m n of
                              LT => ([x], n)
                              EQ => (x::xs, m)
                              GT => (xs, m)
    )
    ([], 0)
  $ toList
  $ foldr (mergeWith (+)) empty
  $ map
    ( fromList
    . map (\x => (x, S Z))
    )
  $ xss

findImplicant
  :  Ord a
  => ( onSet : List (List (Literal a)))
  -> (offSet : List (List (Literal a)))
  -> ExceptT String RandomM (List (Literal a))
findImplicant onSet offSet = do
  lit <- exceptFromMaybe "Could not find implicant" $ rndSelect' $ mostFrequent onSet
  let offSet' = filter (not . elem (negate lit)) offSet
  if isNil offSet'
     then pure [lit]
     else let onSet' = assert_smaller onSet $ filter (not . elem (negate lit)) $ filter isCons $ map (filter (/= lit)) onSet in
              (lit ::) <$> findImplicant onSet' offSet'

export
cdSearch
  :  Ord a
  => ( onSet : List (List (Literal a)))
  -> (offSet : List (List (Literal a)))
  -> ExceptT String RandomM (List (List (Literal a)))
cdSearch onSet offSet =
  if isNil onSet
     then pure []
     else do
       implicant <- findImplicant onSet offSet
       let onSet' = assert_smaller onSet $ filter (not . covers implicant) onSet
       (implicant ::) <$> cdSearch onSet' offSet

