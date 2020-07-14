module GUI

import Bit
import C_Encoding
import Circuit
import Data.IORef
import Encodable
import Encoding
import EncodingBuilder
import IndexType

%include C "gui.h"
%link C "gui.so"

gui : String -> {a : Encodable} -> {b: Encodable} -> Encoding (BitType Bit) a -> (IndexType a -> IO ()) -> Encoding (BitType Bit) b -> IO ()
gui name x flip y = foreign FFI_C "gui" (String -> C_Encoding -> C_Encoding -> IO ()) name (packEncoding x (Just flip)) (packEncoding y Nothing)

guiSimulate'
  : String
  -> {f : Encodable -> Type}
  -> {auto f' : (input' : Encodable) -> EncodingBuilder (ProducingBit input' Bit) (f input')}
  -> (input : Encodable)
  -> {auto isInputToT : builderInput @{f' input} (MkProxy (ProducingBit input Bit, f input)) = input}
  -> ((input' : Encodable) -> f input')
  -> IORef (Encoding (BitType Bit) (builderInput @{f' input} (MkProxy (ProducingBit input Bit, f input))))
  -> IO ()
guiSimulate' name {f'} input g x = do
  gui
    name
    !(readIORef x)
    (\i => do
      modifyIORef x $ mapBitAt bitNot i
      guiSimulate' name {f'} input g x
    )
    (simulate {f'} input g !(readIORef x))

covering export
guiSimulate
  : String
  -> {f : Encodable -> Type}
  -> {auto f' : (input' : Encodable) -> EncodingBuilder (ProducingBit input' Bit) (f input')}
  -> (input : Encodable)
  -> {auto isInputToT : builderInput @{f' input} (MkProxy (ProducingBit input Bit, f input)) = input}
  -> ((input' : Encodable) -> f input')
  -> IO ()
guiSimulate name {f'} input g = (newIORef $ replicate 0) >>= guiSimulate' name {f'} input g

