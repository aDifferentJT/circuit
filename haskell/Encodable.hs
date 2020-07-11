{-# LANGUAGE DataKinds, KindSignatures, GADTs, ScopedTypeVariables, StandaloneDeriving #-}

module Encodable
  ( EncodableKind(..)
  , EncodableType(..)
  ) where

import Data.Nat
import GHC.Exts
import GHC.TypeLits

data EncodableKind :: * where
    BitT     :: EncodableKind
    UnitEncT :: EncodableKind
    PairEncT :: EncodableKind -> EncodableKind -> EncodableKind
    EncVectT :: NatKind -> EncodableKind -> EncodableKind
    NewEncT  :: Symbol -> EncodableKind -> EncodableKind

data EncodableType :: EncodableKind -> * where
    BitV     :: EncodableType BitT
    UnitEncV :: EncodableType UnitEncT
    PairEncV :: EncodableType a -> EncodableType b -> EncodableType (PairEncT a b)
    EncVectV :: NatType n -> EncodableType a -> EncodableType (EncVectT n a)
    NewEncV  :: KnownSymbol ident => EncodableType a -> EncodableType (NewEncT ident a)

deriving instance Eq (EncodableType a)
deriving instance Ord (EncodableType a)

