module GUI

import Analytics
import Bit
import C_Encoding
import Circuit
import Data.IORef
import Encodable
import Encoding
import EncodingBuilder
import IndexType

%foreign "C:gui, gui"
gui' : String -> C_Encoding -> C_Encoding -> Int -> Int -> PrimIO ()

gui : String -> {a : Encodable} -> {b: Encodable} -> Encoding (BitType Bit) a -> (IndexType a -> IO ()) -> Encoding (BitType Bit) b -> Analytics -> IO ()
gui name x flip y analytics =
  primIO $
  gui'
    name
    (packEncoding x (Just flip))
    (packEncoding y Nothing)
    (cast analytics.size)
    (cast analytics.depth)

guiSimulate'
  :  String
  -> {input : Encodable}
  -> {a : Encodable}
  -> Producing input a
  -> IORef (Encoding (BitType Bit) input)
  -> IO ()
guiSimulate' name x inputs =
  gui
    name
    !(readIORef inputs)
    (\i => do
      modifyIORef inputs $ mapBitAt bitNot i
      guiSimulate' name x inputs
    )
    (simulate x !(readIORef inputs))
    (analytics x)

export
guiSimulate
  :  String
  -> {input : Encodable}
  -> {a : Encodable}
  -> Producing input a
  -> IO ()
guiSimulate name x = (newIORef $ replicate 0) >>= guiSimulate' name x

