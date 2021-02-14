module Circuit

import public Bit
import Control.Monad.State
import Data.DPair
import Data.Hash
import Data.SortedMap
import Data.Vect
import Decidable.Equality
import public Encodable
import public Encoding
import public EncodingBuilder
import IndexType
import LinearUtils
import Utils

%default total

mutual
  public export
  data Primitive : (Encodable -> Encodable -> Type) -> Encodable -> Encodable -> Encodable -> Type where
    MkPrimitive : String -> Bits64 -> prim a b -> Producing prim input a -> Primitive prim input a b

  public export
  data ProducingBit : (Encodable -> Encodable -> Type) -> Encodable -> Encodable -> Type where
    InputBit : PartialIndex input a -> ProducingBit prim input a
    BitProducedFrom : {a : Encodable} -> {b : Encodable} -> (1 _ : Primitive prim input a b) -> PartialIndex b c -> ProducingBit prim input c

  public export
  Producing : (Encodable -> Encodable -> Type) -> Encodable -> Encodable -> Type
  Producing prim input = Encoding $ BitType $ ProducingBit prim input Bit


public export
BinarySimPrim : Encodable -> Encodable -> Type
BinarySimPrim a b = Encoding (BitType Bit) a -> Encoding (BitType Bit) b


export
Show (Primitive prim input a b) where
  show (MkPrimitive name h _ _) = "Primitive " ++ name ++ " " ++ show h

export
Show (ProducingBit prim input a) where
  show (InputBit i) = "Input " -- ++ show i
  show (BitProducedFrom p i) = "Produced From " ++ show p -- ++ " at " ++ show i


export
Hashable (Primitive prim input a b) where
  hash (MkPrimitive _ h _ _) = h

export
Hashable (ProducingBit prim input a) where
  hash (InputBit i) = hash i
  hash (BitProducedFrom p i) = addSalt (hash p) (hash i)


export
Dup (Primitive prim input a b) where
  dup (MkPrimitive name h f x) = MkPrimitive name h f x # MkPrimitive name h f x

  release (MkPrimitive name h f x) = MkUnrestricted (MkPrimitive name h f x)

export
Dup (ProducingBit prim input c) where
  dup (InputBit i) = InputBit i # InputBit i
  dup (BitProducedFrom {a} {b} p i) = dup' (dup p)
    where
      dup' : (1 _ : LPair (Primitive prim input a b) (Primitive prim input a b)) -> LPair (ProducingBit prim input c) (ProducingBit prim input c)
      dup' (p1 # p2) = BitProducedFrom p1 i # BitProducedFrom p2 i

  release (InputBit i) = MkUnrestricted $ InputBit i
  release (BitProducedFrom p i) = mixedFlip BitProducedFrom i <$> release p


public export
Bit' : Encodable -> Type
Bit' input = ProducingBit BinarySimPrim input Bit

infixr 10 ~>
public export
(~>) : Encodable -> Encodable -> Type
a ~> b = (input : Encodable) -> Producing BinarySimPrim input a -> Producing BinarySimPrim input b


export
primitive
  :  String
  -> {auto t1' : EncodingBuilder Bit t1}
  -> t1
  -> (0 input : Encodable)
  -> {auto t2' : EncodingBuilder (ProducingBit BinarySimPrim input Bit) t2}
  -> {auto sameInput : (builderInput @{t1'}) = (builderInput @{t2'})}
  -> {auto sameOutput : (builderOutput @{t1'}) = (builderOutput @{t2'})}
  -> t2
primitive name g input =
    deconstructEncodingFunction $
    \x => map (BitProducedFrom (primitive' x)) $
         rewrite sameOutput in IndexTypes
  where
    primitive' :  Producing BinarySimPrim input (builderInput @{t2'})
               -> Primitive BinarySimPrim input (builderInput @{t1'}) (builderOutput @{t1'})
    primitive' x = MkPrimitive
      name
      (addSalt (hash name) (hash @{HashableEncoding} x))
      (constructEncodingFunction g)
      (rewrite__impl (Producing BinarySimPrim input) sameInput x)


export
inputProducing : {input : Encodable} -> Producing prim input input
inputProducing = map InputBit IndexTypes


mutual
  covering
  runPrimitive'
    :  Encoding (BitType Bit) input
    -> Primitive BinarySimPrim input a b
    -> State (SortedMap Bits64 (Exists (Encoding (BitType Bit)))) (Encoding (BitType Bit) b)
  runPrimitive' inputs prim@(MkPrimitive _ _ f x) = do
    y <- f <$> simulate' inputs x
    modify (insert (hash prim) (Evidence b y))
    pure y

  covering
  runPrimitive
    :  Encoding (BitType Bit) input
    -> Primitive BinarySimPrim input a b
    -> State (SortedMap Bits64 (Exists (Encoding (BitType Bit)))) (Encoding (BitType Bit) b)
  runPrimitive inputs prim =
    case Data.SortedMap.lookup (hash prim) !get of
         Just (Evidence b' xs) => rewrite unsafeAssumeEq b b' in pure xs
         Nothing => runPrimitive' inputs prim

  covering
  simulate'
    :  Encoding (BitType Bit) input
    -> Producing BinarySimPrim input a
    -> State (SortedMap Bits64 (Exists (Encoding (BitType Bit)))) (Encoding (BitType Bit) a)
  simulate' {a = Bit} inputs (BitEncoding (MkBitType x)) =
    case x of
         InputBit i => pure $ index i inputs
         BitProducedFrom prim i => index i <$> runPrimitive inputs prim
  simulate' _      UnitEnc = pure UnitEnc
  simulate' inputs (x && y) = pure (!(simulate' inputs x) && !(simulate' inputs y))
  simulate' _      [] = pure []
  simulate' inputs (x :: xs) = pure (!(simulate' inputs x) :: !(simulate' inputs xs))
  simulate' inputs (NewEncoding x) = relax NewEncoding <$> simulate' inputs x

covering
export
simulate
  :  Producing BinarySimPrim input a
  -> Encoding (BitType Bit) input
  -> Encoding (BitType Bit) a
simulate x inputs = snd $ runState empty $ simulate' inputs x

export
constructProducing
  :  {0 f : Encodable -> Type}
  -> {auto f' : (0 input' : Encodable) -> EncodingBuilder (ProducingBit prim input' Bit) (f input')}
  -> {input : Encodable}
  -> {auto 0 isInputToT : builderInput @{f' input} = input}
  -> ((0 input' : Encodable) -> f input')
  -> Producing prim input (builderOutput @{f' input})
constructProducing g = constructEncodingFunction @{f' input} (g input) $ rewrite isInputToT in inputProducing

