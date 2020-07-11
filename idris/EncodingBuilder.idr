module EncodingBuilder

import Data.Vect
import Encodable
import Encoding

%default total

public export
data Proxy : a -> Type where
  MkProxy : (x : a) -> Proxy x

public export
interface EncodingBuilder t a where
  builderInput : Proxy (t, a) -> Encodable
  builderOutput : Proxy (t, a) -> Encodable
  constructEncodingFunction : a -> Encoding (BitType t) (builderInput (MkProxy (t, a))) -> Encoding (BitType t) (builderOutput (MkProxy (t, a)))
  deconstructEncodingFunction : (Encoding (BitType t) (builderInput (MkProxy (t, a))) -> Encoding (BitType t) (builderOutput (MkProxy (t, a)))) -> a

public export
interface EncodingValue t a where
  builderEncodable : Encodable
  constructEncodingValue : a -> Encoding (BitType t) builderEncodable
  deconstructEncodingValue : Encoding (BitType t) builderEncodable -> a
  

public export
EncodingValue t t where
  builderEncodable = Bit
  constructEncodingValue x = BitEncoding x
  deconstructEncodingValue (BitEncoding x) = x

public export
EncodingBuilder t t where
  builderInput _ = UnitEnc
  builderOutput {t} _ = builderEncodable {t} {a = t}
  constructEncodingFunction {t} x UnitEnc = constructEncodingValue {t} x
  deconstructEncodingFunction {t} f = deconstructEncodingValue {t} $ f UnitEnc

public export
(EncodingValue t a, EncodingValue t b) => EncodingValue t (a, b) where
  builderEncodable @{a'} @{b'} = builderEncodable @{a'} && builderEncodable @{b'}
  constructEncodingValue @{a'} @{b'} (x, y) = constructEncodingValue @{a'} x && constructEncodingValue @{b'} y
  deconstructEncodingValue @{a'} @{b'} (x && y) = (deconstructEncodingValue @{a'} x, deconstructEncodingValue @{b'} y)

public export
(EncodingValue t a, EncodingValue t b) => EncodingBuilder t (a, b) where
  builderInput _ = UnitEnc
  builderOutput {t} {a} {b} _ = builderEncodable {t} {a = (a, b)}
  constructEncodingFunction {t} x UnitEnc = constructEncodingValue {t} x
  deconstructEncodingFunction {t} f = deconstructEncodingValue {t} $ f UnitEnc

public export
EncodingValue t a => EncodingValue t (Vect n a) where
  builderEncodable @{a'} {n} = EncVect n $ builderEncodable @{a'}
  constructEncodingValue [] = []
  constructEncodingValue {t} {n = S n} (x :: xs) = constructEncodingValue {t} x :: constructEncodingValue {t} xs
  deconstructEncodingValue [] = []
  deconstructEncodingValue {t} (x :: y) = deconstructEncodingValue {t} x :: deconstructEncodingValue {t} y

public export
EncodingValue t a => EncodingBuilder t (Vect n a) where
  builderInput _ = UnitEnc
  builderOutput {t} {n} {a} _ = builderEncodable {t} {a = Vect n a}
  constructEncodingFunction {t} x UnitEnc = constructEncodingValue {t} x
  deconstructEncodingFunction {t} f = deconstructEncodingValue {t} $ f UnitEnc

public export
(EncodingValue t a, EncodingBuilder t b) => EncodingBuilder t (a -> b) where
  builderInput @{a'} @{b'} {t} {b} _ = builderEncodable @{a'} && builderInput (MkProxy (t, b))
  builderOutput {t} {b} _ = builderOutput (MkProxy (t, b))
  constructEncodingFunction @{a'} @{b'} f (x && y) = constructEncodingFunction @{b'} (f $ deconstructEncodingValue @{a'} x) y
  deconstructEncodingFunction @{a'} @{b'} f x = deconstructEncodingFunction @{b'} $ \y => f (constructEncodingValue @{a'} x && y)

