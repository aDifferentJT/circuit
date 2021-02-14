module CommandLine

import Analytics
import Circuit
import Control.Monad.Random
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.Strings
import Encodable
import Graph
import GUI
import IndexType
import System
import System.File
import TUI
import Verilog

logo : String
logo = pack $
  [ '╲', '\n'
  , ' ', '╲', '\n'
  , ' ', ' ', '╲', '\n'
  , ' ', ' ', ' ', '╲', '\n'
  , ' ', ' ', ' ', ' ', '╲', '╱', '▔', '▔', '▔', '▔', '▔', '╲', '\n'
  , ' ', ' ', ' ', ' ', '╱', '╲', ' ', ' ', ' ', ' ', ' ', ' ', '╲', '\n'
  , ' ', ' ', ' ', '╱', ' ', ' ', '▏', ' ', ' ', ' ', ' ', ' ', ' ', '╲', '\n'
  , ' ', ' ', ' ', '▏', ' ', '╲', '▏', ' ', ' ', ' ', ' ', ' ', ' ', '▕', '\n'
  , ' ', ' ', ' ', '▏', ' ', ' ', '╲', ' ', ' ', ' ', ' ', ' ', ' ', '▕', '\n'
  , ' ', ' ', ' ', '╲', ' ', ' ', '╱', '╲', '▁', '▁', '▁', ' ', ' ', '╱', '\n'
  , ' ', ' ', ' ', ' ', '╲', '╱', ' ', ' ', '╲', ' ', ' ', '╲', '╱', '\n'
  , ' ', ' ', ' ', ' ', '╱', '╲', '▁', '▁', '▁', '▁', '▁', '╱', '╲', '\n'
  , ' ', ' ', ' ', '╱', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '╲', '\n'
  , ' ', ' ', '╱', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '╲', '\n'
  , ' ', '╱', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '╲', '\n'
  , '╱', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '╲', '\n'
  ]

parseArgs
  :  String
  -> {input : Encodable}
  -> {a : Encodable}
  -> Producing BinarySimPrim input a
  -> List String
  -> IO ()
parseArgs name x [] = putStrLn $ "No arguments (usually there's at least the executable)"
parseArgs name x [_] = putStrLn $ "Expected mode"
parseArgs name x [_, "analytics"] = do
  putStrLn $ name ++ ":"
  printLn $ analytics x
parseArgs name x [_, "graph", fn] = do
  fileRes <- runRandomM (graph x) >>= writeFile fn
  case fileRes of
       Left e => printLn e
       Right () => pure ()
parseArgs name x [_, "gui"] = guiSimulate name x (replicate $ MkBitType 0)
parseArgs name x [_, "tui"] = tuiSimulate x (replicate $ MkBitType 0) EmptyIndex
parseArgs name x [_, "verilog", fn] = do
  (verilogErrs, v) <- runRandomM $ runStateT [] $ verilog name x
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
  -> Producing BinarySimPrim input a
  -> IO ()
commandLine name x = putStr logo >>= \_ => getArgs >>= parseArgs name x

