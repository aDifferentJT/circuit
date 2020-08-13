module CommandLine

import Analytics
import Circuit
import Control.Monad.Random
import Control.Monad.State
import Data.List
import Encodable
import GUI
import IndexType
import System
import TUI
import Verilog

logo : String
logo = """╲
 ╲
  ╲
   ╲
    ╲╱▔▔▔▔▔╲
    ╱╲      ╲
   ╱  ▏      ╲
   ▏ ╲▏      ▕
   ▏  ╲      ▕
   ╲  ╱╲▁▁▁  ╱
    ╲╱  ╲  ╲╱
    ╱╲▁▁▁▁▁╱╲
   ╱         ╲
  ╱           ╲
 ╱             ╲
╱               ╲
"""

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
parseArgs name x [_, "verilog", fn] = do
  (v, verilogErrs) <- runRandomM $ runStateT (verilog name x) []
  traverse putStrLn $ reverse verilogErrs
  fileRes <- writeFile fn v
  case fileRes of
       Left e => printLn e
       Right () => pure ()
parseArgs name x (_ :: as) = putStrLn $ "Unexpected arguments: " ++ show as

export
commandLine
  :  String
  -> {input : Encodable}
  -> {a : Encodable}
  -> Producing input a
  -> IO ()
commandLine name x = putStr logo >>= \_ => getArgs >>= parseArgs name x

