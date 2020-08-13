module Control.Monad.Random

import Control.Monad.MaybeT
import Data.List

%default total

export
data RandomM a = MkRandomM (IO a)

export
runRandomM : RandomM a -> IO a
runRandomM (MkRandomM x) = x

export
Functor RandomM where
  map f = MkRandomM . map f . runRandomM

export
Applicative RandomM where
  pure = MkRandomM . pure
  (MkRandomM f) <*> (MkRandomM x) = MkRandomM $ f <*> x

export
Monad RandomM where
  (MkRandomM x) >>= f = MkRandomM $ x >>= (runRandomM . f)

{-
export
randomM : Random a => RandomM a
randomM = MkRandomM randomIO
-}

export
rndSelect : (elems : List a) -> NonEmpty elems => RandomM a
--rndSelect elems = MkRandomM $ rndSelect elems
rndSelect (x :: _) = pure x

export
rndSelect' : List a -> MaybeT RandomM a
rndSelect' [] = nothing
--rndSelect' xs@(_ :: _) = lift $ rndSelect xs
rndSelect' (x :: _) = pure x

