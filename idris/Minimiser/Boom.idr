module Minimiser.Boom

import Minimiser.CDSearch
import Control.Monad.ExceptT
import Control.Monad.Random
import Minimiser.ImplicantExpansion
import Minimiser.Literal
import Minimiser.ShrinkCover
import Utils

%default total

export
boom
  :  Ord a
  => ( onSet : List (List (Literal a)))
  -> (offSet : List (List (Literal a)))
  -> ExceptT String RandomM (List (List (Literal a)))
boom onSet offSet = do
  implicants <- concatMap (multipleSequentialSearch offSet) <$> cdSearch onSet offSet
  uncurry (liftA2 (++)) $ (pure *** greedySelectImplicants . uncurry generateCovers) $ getEssentials onSet implicants

