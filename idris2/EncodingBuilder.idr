module EncodingBuilder

import Data.Vect
import Encodable
import Encoding

%default total

public export
interface EncodingValue t a where
  builderEncodable : Encodable
  constructEncodingValue : a -> Encoding (BitType t) builderEncodable
  deconstructEncodingValue : Encoding (BitType t) builderEncodable -> a

export
EncodingValue t t where
  builderEncodable = Bit
  constructEncodingValue x = BitEncoding x
  deconstructEncodingValue (BitEncoding x) = x

export
(EncodingValue t a, EncodingValue t b) => EncodingValue t (a, b) where
  builderEncodable @{(a', b')} = builderEncodable @{a'} && builderEncodable @{b'}
  constructEncodingValue @{(_, _)} (x, y) = constructEncodingValue x && constructEncodingValue y
  deconstructEncodingValue @{(_, _)} (x && y) = (deconstructEncodingValue x, deconstructEncodingValue y)

export
{n : Nat} -> EncodingValue t a => EncodingValue t (Vect n a) where
  builderEncodable @{a'} = EncVect n $ builderEncodable @{a'}
  constructEncodingValue [] = []
  constructEncodingValue (x :: xs) = constructEncodingValue x :: constructEncodingValue xs
  deconstructEncodingValue [] = []
  deconstructEncodingValue (x :: y) = deconstructEncodingValue x :: deconstructEncodingValue y

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

