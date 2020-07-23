module Minimiser.ShrinkCover

import Control.Monad.ExceptT
import Control.Monad.Random
import Data.List
import Minimiser.Literal
import Utils

%default total

getEssentials'
  : Eq a
  => (essentials : List (List (Literal a)))
  -> (onSetUncovered : List (List (Literal a)))
  -> (onSet : List (List (Literal a)))
  -> (implicants : List (List (Literal a)))
  -> ( List (List (Literal a)) -- Essential PIs
     , List (List (Literal a)) -- onSetUncovered
     , List (List (Literal a)) -- Non-essential PIs
     )
getEssentials' essentials onSetUncovered [] implicants =
  ( essentials
  , onSetUncovered
  , implicants
  )
getEssentials' essentials onSetUncovered (onTerm :: onSet) implicants =
  case filter (flip covers onTerm) implicants of
       [essential] => getEssentials'
                        (essential :: essentials)
                        (filter (not . covers essential) onSetUncovered)
                        (assert_smaller (onTerm :: onSet) $ filter (not . covers essential) onSet)
                        (filter (/= essential) implicants)
       _ => getEssentials' essentials (onTerm :: onSetUncovered) onSet implicants

export
getEssentials
  : Eq a
  => (onSet : List (List (Literal a)))
  -> (implicants : List (List (Literal a)))
  -> ( List (List (Literal a)) -- Essential PIs
     , List (List (Literal a)) -- onSetUncovered
     , List (List (Literal a)) -- Non-essential PIs
     )
getEssentials = getEssentials' [] []

export
generateCovers
  :  Eq a
  => (onSet : List (List (Literal a)))
  -> (implicants : List (List (Literal a)))
  -> List (List (Literal a), List (List (Literal a)))
generateCovers onSet = map $ \implicant => (implicant, filter (covers implicant) onSet)

greedySelectImplicants'
  :  Eq a
  => (uncovered : List (List (Literal a)))
  -> (implicants : List (List (Literal a), List (List (Literal a))))
  -> ExceptT String RandomM (List (List (Literal a)))
greedySelectImplicants' [] implicants = pure []
greedySelectImplicants' uncovered implicants = do
  (implicant, covered) <- exceptFromMaybe "Could not select implicants"
                        $ rndSelect'
                        $ fst
                        $ foldl
                          ( \(xs, m), (x, n) => case compare m n of
                                                     LT => ([x], n)
                                                     EQ => (x::xs, m)
                                                     GT => (xs, m)
                          )
                          ([], 0)
                        $ map (\(x, y) => ((x, y), length y))
                        $ implicants
  implicants <- greedySelectImplicants'
    (filter (not . flip elem covered) uncovered)
    (assert_smaller implicants $ filter (isCons . snd) $ map (second $ filter $ not . flip elem covered) implicants)
  pure $ implicant :: implicants

export
greedySelectImplicants
  :  Eq a
  => List (List (Literal a), List (List (Literal a)))
  -> ExceptT String RandomM (List (List (Literal a)))
greedySelectImplicants = greedySelectImplicants' empty

