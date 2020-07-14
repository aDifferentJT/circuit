module GUI

import Bit
import C_Encoding
import Circuit
import Data.IORef
import Encodable
import Encoding
import EncodingBuilder
import IndexType

%foreign "C:gui, gui"
gui' : String -> C_Encoding -> C_Encoding -> PrimIO ()

gui : String -> {a : Encodable} -> {b: Encodable} -> Encoding (BitType Bit) a -> (IndexType a -> IO ()) -> Encoding (BitType Bit) b -> IO ()
gui name x flip y = primIO $ gui' name (packEncoding x (Just flip)) (packEncoding y Nothing)

guiSimulate'
  : String
  -> {0 f : Encodable -> Type}
  -> {auto f' : (input' : Encodable) -> EncodingBuilder (ProducingBit input' Bit) (f input')}
  -> (input : Encodable)
  -> {auto isInputToT : builderInput @{f' input} = input}
  -> ((input' : Encodable) -> f input')
  -> IORef (Encoding (BitType Bit) (builderInput @{f' input}))
  -> IO ()
guiSimulate' name input g x =
  gui
    name
    !(readIORef x)
    (\i => do
      modifyIORef x $ mapBitAt bitNot i
      guiSimulate' name input g x
    )
    (simulate input g !(readIORef x))

export
guiSimulate
  : String
  -> {0 f : Encodable -> Type}
  -> {auto f' : (input' : Encodable) -> EncodingBuilder (ProducingBit input' Bit) (f input')}
  -> (input : Encodable)
  -> {auto isInputToT : builderInput @{f' input} = input}
  -> ((input' : Encodable) -> f input')
  -> IO ()
guiSimulate name input g = (newIORef $ replicate 0) >>= guiSimulate' name input g

