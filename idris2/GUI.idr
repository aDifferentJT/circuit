module GUI

import Bit
import C_Encoding
import Circuit
import Data.IORef
import Encodable
import Encoding
import EncodingBuilder
import IndexType

%default total

%foreign "C:gui, gui"
gui' : C_Encoding -> C_Encoding -> PrimIO ()

gui : HasIO io => {a : Encodable} -> {b: Encodable} -> Encoding (BitType Bit) a -> (IndexType a -> IO ()) -> Encoding (BitType Bit) b -> io ()
gui x flip y = primIO $ gui' (packEncoding x (Just flip)) (packEncoding y Nothing)

%foreign "C:update, gui"
update : String -> String -> PrimIO ()

export
guiSimulate
  :  {0 f : Encodable -> Type}
  -> {auto f' : (input' : Encodable) -> EncodingBuilder (ProducingBit input' Bit) (f input')}
  -> (input : Encodable)
  -> {auto isInputToT : builderInput @{f' input} = input}
  -> ((input' : Encodable) -> f input')
  -> IO ()
guiSimulate input g = do
  x <- newIORef $ the (Encoding (BitType Bit) (builderInput @{f' input})) $ replicate 0
  gui
    !(readIORef x)
    (\i => do
      modifyIORef x $ mapBitAt bitNot i
      primIO $ update (packBits !(readIORef x)) (packBits $ simulate input g !(readIORef x))
    )
    (simulate input g !(readIORef x))

