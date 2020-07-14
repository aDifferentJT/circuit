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
gui' : C_Encoding -> C_Encoding -> PrimIO ()

gui : {a : Encodable} -> {b: Encodable} -> Encoding (BitType Bit) a -> (IndexType a -> IO ()) -> Encoding (BitType Bit) b -> IO ()
gui x flip y = primIO $ gui' (packEncoding x (Just flip)) (packEncoding y Nothing)

guiSimulate'
  :  {0 f : Encodable -> Type}
  -> {auto f' : (input' : Encodable) -> EncodingBuilder (ProducingBit input' Bit) (f input')}
  -> (input : Encodable)
  -> {auto isInputToT : builderInput @{f' input} = input}
  -> ((input' : Encodable) -> f input')
  -> IORef (Encoding (BitType Bit) (builderInput @{f' input}))
  -> IO ()
guiSimulate' input g x =
  gui
    !(readIORef x)
    (\i => do
      modifyIORef x $ mapBitAt bitNot i
      guiSimulate' input g x
    )
    (simulate input g !(readIORef x))

export
guiSimulate
  :  {0 f : Encodable -> Type}
  -> {auto f' : (input' : Encodable) -> EncodingBuilder (ProducingBit input' Bit) (f input')}
  -> (input : Encodable)
  -> {auto isInputToT : builderInput @{f' input} = input}
  -> ((input' : Encodable) -> f input')
  -> IO ()
guiSimulate input g = (newIORef $ replicate 0) >>= guiSimulate' input g

