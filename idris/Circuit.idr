module Circuit

import public Bit
import Control.Monad.State
import Data.Hash
import Data.SortedMap
import Data.Vect
import Decidable.Equality
import public Encodable
import public Encoding
import public EncodingBuilder
import IndexType
import Utils

%default total

public export
PrimType : Encodable -> Type
PrimType = Encoding $ BitType Bit

infixr 10 ~~>
public export
(~~>) : Encodable -> Encodable -> Type
a ~~> b = PrimType a -> PrimType b


mutual
  public export
  data Primitive : Encodable -> Encodable -> Encodable -> Type where
    MkPrimitive : String -> Bits64 -> (a ~~> b) -> Producing input a -> Primitive input a b

  public export
  data ProducingBit : Encodable -> Encodable -> Type where
    InputBit : PartialIndex input a -> ProducingBit input a
    BitProducedFrom : {a : Encodable} -> {b : Encodable} -> Primitive input a b -> PartialIndex b c -> ProducingBit input c

  public export
  Producing : Encodable -> Encodable -> Type
  Producing input = Encoding $ BitType $ ProducingBit input Bit


export
Show (Primitive input a b) where
  show (MkPrimitive name h _ _) = "Primitive " ++ name ++ " " ++ show h

export
Show (ProducingBit input a) where
  show (InputBit i) = "Input " -- ++ show i
  show (BitProducedFrom p i) = "Produced From " ++ show p -- ++ " at " ++ show i


export
Hashable (Primitive input a b) where
  saltedHash64 (MkPrimitive _ h _ _) = saltedHash64 h

export
Hashable (ProducingBit input a) where
  saltedHash64 (InputBit i) = saltedHash64 i
  saltedHash64 (BitProducedFrom p i) = saltedHash64 (p, i)


public export
Bit' : Encodable -> Type
Bit' input = ProducingBit input Bit

infixr 10 ~>
public export
(~>) : Encodable -> Encodable -> Type
a ~> b = (input : Encodable) -> Producing input a -> Producing input b


export
primitive
  :  String
  -> {auto t1' : EncodingBuilder Bit t1}
  -> t1
  -> (input : Encodable)
  -> {auto t2' : EncodingBuilder (ProducingBit input Bit) t2}
  -> {auto sameInput : (builderInput (MkProxy (Bit, t1))) = (builderInput (MkProxy (ProducingBit input Bit, t2)))}
  -> {auto sameOutput : (builderOutput (MkProxy (Bit, t1))) = (builderOutput (MkProxy (ProducingBit input Bit, t2)))}
  -> t2
primitive {t1} {t2} name g input {sameInput} {sameOutput} =
    deconstructEncodingFunction {t = ProducingBit input Bit} $
    \x => map (BitProducedFrom (primitive' x)) $
         rewrite sameOutput in IndexTypes
  where
    primitive' : Producing input (builderInput (MkProxy (ProducingBit input Bit, t2))) -> Primitive input (builderInput (MkProxy (Bit, t1))) (builderOutput (MkProxy (Bit, t1)))
    primitive' x = MkPrimitive name (hash (name, hash @{HashableEncoding {t = ProducingBit input Bit}} x)) (constructEncodingFunction {t = Bit} g) $ rewrite__impl (Producing input) sameInput x


export
inputProducing : {input : Encodable} -> Producing input input
inputProducing = map InputBit IndexTypes


mutual
  covering
  runPrimitive'
    :  {input : Encodable}
    -> {a : Encodable}
    -> {b : Encodable}
    -> PrimType input
    -> Primitive input a b
    -> State (SortedMap Bits64 (c : Encodable ** PrimType c)) (PrimType b)
  runPrimitive' {b} inputs prim@(MkPrimitive _ _ f' x) = do
    y <- f' <$> simulate' inputs x
    modify (insert (hash prim) (b ** y))
    pure y

  covering
  runPrimitive
    :  {input : Encodable}
    -> {a : Encodable}
    -> {b : Encodable}
    -> PrimType input
    -> Primitive input a b
    -> State (SortedMap Bits64 (c : Encodable ** PrimType c)) (PrimType b)
  runPrimitive {b} inputs prim =
    case Data.SortedMap.lookup (hash prim) !get of
         Just (b' ** xs) => case decEq b b' of
                                 Yes Refl => pure xs
                                 No _ => runPrimitive' inputs prim
         Nothing => runPrimitive' inputs prim

  covering
  simulate'
    :  {input : Encodable}
    -> {auto inputsEqual : input = input'}
    -> {a : Encodable}
    -> PrimType input
    -> Producing input' a
    -> State (SortedMap Bits64 (c : Encodable ** PrimType c)) (PrimType a)
  simulate' {inputsEqual = Refl} {a = Bit} inputs (BitEncoding x) =
    case x of
         InputBit i => pure $ index i inputs
         BitProducedFrom prim i => index i <$> runPrimitive inputs prim
  simulate' _      UnitEnc = pure UnitEnc
  simulate' {inputsEqual = Refl} inputs (x && y) = pure (!(simulate' inputs x) && !(simulate' inputs y))
  simulate' _      [] = pure []
  simulate' {inputsEqual = Refl} inputs (x :: xs) = pure (!(simulate' inputs x) :: !(simulate' inputs xs))
  simulate' {inputsEqual = Refl} inputs (NewEncoding x) = NewEncoding <$> simulate' inputs x

covering
export
simulate : Producing a b -> Encoding (BitType Bit) a -> Encoding (BitType Bit) b
simulate x inputs = fst $ flip runState empty $ simulate' inputs x

export
constructProducing
  :  {f : Encodable -> Type}
  -> {auto f' : (input' : Encodable) -> EncodingBuilder (ProducingBit input' Bit) (f input')}
  -> {input : Encodable}
  -> {auto isInputToT : builderInput @{f' input} (MkProxy (ProducingBit input Bit, f input)) = input}
  -> ((input' : Encodable) -> f input')
  -> Producing input (builderOutput @{f' input} (MkProxy (ProducingBit input Bit, f input)))
constructProducing {f} {f'} {input} {isInputToT} g = constructEncodingFunction @{f' input} (g input) $ rewrite isInputToT in inputProducing

