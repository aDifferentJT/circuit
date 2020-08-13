module Control.Monad.MaybeT

import public Control.Monad.Trans

%default total

public export
record MaybeT (m : Type -> Type) a where
  constructor MkMaybeT
  runMaybeT : m (Maybe a)

public export
Functor f => Functor (MaybeT f) where
  map g = MkMaybeT . map (map g) . runMaybeT

public export
Applicative f => Applicative (MaybeT f) where
  pure = MkMaybeT . pure . pure
  (MkMaybeT g) <*> (MkMaybeT x) = MkMaybeT $ ((<*>) <$> g) <*> x

public export
Monad m => Monad (MaybeT m) where
  (MkMaybeT x) >>= f = MkMaybeT $ x >>= maybe (pure Nothing) (runMaybeT . f)

public export
MonadTrans MaybeT where
  lift = MkMaybeT . map pure

public export
nothing : Applicative f => MaybeT f a
nothing = MkMaybeT $ pure $ Nothing

