module EncodingBuilder

import Data.LVect
import Encodable
import Encoding
import LinearUtils

%default total

public export
interface EncodingValue t a where
  builderEncodable : Encodable
  constructEncodingValue : (1 _ : a) -> Encoding (BitType t) builderEncodable
  deconstructEncodingValue : (1 _ : Encoding (BitType t) builderEncodable) -> a

export
EncodingValue t t where
  builderEncodable = Bit
  constructEncodingValue x = BitEncoding $ MkBitType x
  deconstructEncodingValue (BitEncoding (MkBitType x)) = x

export
EncodingValue t () where
  builderEncodable = UnitEnc
  constructEncodingValue () = UnitEnc
  deconstructEncodingValue UnitEnc = ()

export
(EncodingValue t a, EncodingValue t b) => EncodingValue t (LPair a b) where
  builderEncodable @{(a', b')} = builderEncodable @{a'} && builderEncodable @{b'}
  constructEncodingValue @{(_, _)} (x # y) = constructEncodingValue x && constructEncodingValue y
  deconstructEncodingValue @{(_, _)} (x && y) = deconstructEncodingValue x # deconstructEncodingValue y

export
{n : Nat} -> EncodingValue t a => EncodingValue t (LVect n a) where
  builderEncodable @{a'} = EncVect n $ builderEncodable @{a'}
  constructEncodingValue [] = []
  constructEncodingValue (x :: xs) = constructEncodingValue x :: constructEncodingValue xs
  deconstructEncodingValue [] = []
  deconstructEncodingValue (x :: xs) = deconstructEncodingValue x :: deconstructEncodingValue xs

public export
data NewEncBuilder : String -> Type -> Type where
  MkNewEncBuilder : (1 _ : a) -> NewEncBuilder ident a

export
{ident : String} -> EncodingValue t a => EncodingValue t (NewEncBuilder ident a) where
  builderEncodable @{a'} = NewEnc ident $ builderEncodable @{a'}
  constructEncodingValue (MkNewEncBuilder x) = NewEncoding $ constructEncodingValue x
  deconstructEncodingValue (NewEncoding x) = MkNewEncBuilder $ deconstructEncodingValue x

public export
interface EncodingBuilder t a where
  builderInput : Encodable
  builderOutput : Encodable
  constructEncodingFunction : a -> Encoding (BitType t) builderInput -> Encoding (BitType t) builderOutput
  deconstructEncodingFunction : (Encoding (BitType t) builderInput -> Encoding (BitType t) builderOutput) -> a

export
EncodingValue t a => EncodingBuilder t a where
  builderInput = UnitEnc
  builderOutput @{a'} = builderEncodable @{a'}
  constructEncodingFunction x UnitEnc = constructEncodingValue x
  deconstructEncodingFunction f = deconstructEncodingValue $ f UnitEnc

export
(EncodingValue t a, EncodingBuilder t b) => EncodingBuilder t (a -> b) where
  builderInput @{(a', b')} = builderEncodable @{a'} && builderInput @{b'}
  builderOutput @{(_, b')} = builderOutput @{b'}
  constructEncodingFunction @{(_, _)} f (x && y) = constructEncodingFunction (f $ deconstructEncodingValue x) y
  deconstructEncodingFunction @{(a', b')} f x = deconstructEncodingFunction @{b'} $ \y => f (constructEncodingValue @{a'} x && y)

public export
interface LinearEncodingBuilder t a where
  linearBuilderInput : Encodable
  linearBuilderOutput : Encodable
  constructLinearEncodingFunction : (1 _ : a) -> (1 _ : Encoding (BitType t) linearBuilderInput) -> Encoding (BitType t) linearBuilderOutput
  deconstructLinearEncodingFunction : (1 _ : (1 _ : Encoding (BitType t) linearBuilderInput) -> Encoding (BitType t) linearBuilderOutput) -> a

export
EncodingValue t a => LinearEncodingBuilder t a where
  linearBuilderInput = UnitEnc
  linearBuilderOutput @{a'} = builderEncodable @{a'}
  constructLinearEncodingFunction x UnitEnc = constructEncodingValue x
  deconstructLinearEncodingFunction f = deconstructEncodingValue $ f UnitEnc

export
(EncodingValue t a, LinearEncodingBuilder t b) => LinearEncodingBuilder t ((1 _ : a) -> b) where
  linearBuilderInput @{(a', b')} = builderEncodable @{a'} && linearBuilderInput @{b'}
  linearBuilderOutput @{(_, b')} = linearBuilderOutput @{b'}
  constructLinearEncodingFunction @{(_, _)} f (x && y) = constructLinearEncodingFunction (f $ deconstructEncodingValue x) y
  deconstructLinearEncodingFunction @{(a', b')} f x =
    let
      g :  (1 _ : (1 _ : Encoding (BitType t) (builderEncodable @{a'} && linearBuilderInput @{b'})) -> Encoding (BitType t) (linearBuilderOutput @{b'}))
        -> (1 _ : a)
        -> (1 _ : Encoding (BitType t) (linearBuilderInput @{b'}))
        -> Encoding (BitType t) (linearBuilderOutput @{b'})
      g f' x' y = f' (constructEncodingValue @{a'} x' && y)
    in
      deconstructLinearEncodingFunction @{b'} (g f x)

