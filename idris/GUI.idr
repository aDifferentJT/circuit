module GUI

import Analytics
import Bit
import C_Encoding
import Circuit
import Data.IORef
import Encodable
import Encoding
import IndexType

%include C "gui.h"
%link C "gui.so"

gui : String -> {a : Encodable} -> {b: Encodable} -> Encoding (BitType Bit) a -> (IndexType a -> IO ()) -> Encoding (BitType Bit) b -> Analytics -> IO ()
gui name x flip y analytics =
  foreign FFI_C "gui" (String -> C_Encoding -> C_Encoding -> Int -> Int -> IO ())
    name
    (packEncoding x (Just flip))
    (packEncoding y Nothing)
    (cast $ size $ analytics)
    (cast $ depth $ analytics)

guiSimulate'
  : String
  -> Producing input a
  -> IORef (Encoding (BitType Bit) input)
  -> IO ()
guiSimulate' name x inputs = do
  gui
    name
    !(readIORef inputs)
    (\i => do
      modifyIORef inputs $ mapBitAt bitNot i
      guiSimulate' name x inputs
    )
    (simulate x !(readIORef inputs))
    (analytics x)

covering export
guiSimulate : String -> Producing input a -> IO ()
guiSimulate name x = (newIORef $ replicate 0) >>= guiSimulate' name x

