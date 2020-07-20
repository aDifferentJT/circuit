module CommandLine

import Analytics
import Circuit
import Data.List
import Encodable
import GUI
import IndexType
import System
import TUI

parseArgs
  :  String
  -> {input : Encodable}
  -> {a : Encodable}
  -> Producing input a
  -> List String
  -> IO ()
parseArgs name x [] = putStrLn $ "No arguments (usually there's at least the executable)"
parseArgs name x [_] = putStrLn $ "Expected mode"
parseArgs name x [_, "analytics"] = do
  putStrLn $ name ++ ":"
  printLn $ analytics x
parseArgs name x [_, "gui"] = guiSimulate name x
parseArgs name x [_, "tui"] = tuiSimulate x (replicate 0) EmptyIndex
parseArgs name x (_ :: as) = putStrLn $ "Unexpected arguments: " ++ show as

export
commandLine
  :  String
  -> {input : Encodable}
  -> {a : Encodable}
  -> Producing input a
  -> IO ()
commandLine name x = getArgs >>= parseArgs name x

