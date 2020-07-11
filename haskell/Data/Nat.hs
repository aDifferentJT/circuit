{-# LANGUAGE DataKinds, GADTs, KindSignatures, StandaloneDeriving #-}

module Data.Nat
  ( NatKind(..)
  , NatType(..)
  ) where

data NatKind :: * where
  ZT :: NatKind
  ST :: NatKind -> NatKind

data NatType :: NatKind -> * where
  ZV :: NatType ZT
  SV :: NatType n -> NatType (ST n)

deriving instance Eq (NatType n)
deriving instance Ord (NatType n)

natToInteger :: NatType n -> Integer
natToInteger ZV = 0
natToInteger (SV n) = 1 + natToInteger n

instance Show (NatType n) where
  show = show . natToInteger

