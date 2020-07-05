module Language.Lefty.Call

import Language.Lefty.AST

%default total

data Lefty : Type -> Type where
  MkLefty : File -> a -> Lefty a

open : IO (Either FileError File)
open = popen "lefty" Read

main : IO ()
main = do
  open >>= either print (\_ => pure ())
  getLine
  pure ()

