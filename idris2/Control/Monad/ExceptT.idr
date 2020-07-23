module Control.Monad.ExceptT

import Control.Monad.MaybeT
import public Control.Monad.Trans

%default total

public export
record ExceptT e m a where
  constructor MkExceptT
  runExceptT : m (Either e a)

public export
Functor f => Functor (ExceptT e f) where
  map g = MkExceptT . map (map g) . runExceptT

public export
Applicative f => Applicative (ExceptT e f) where
  pure = MkExceptT . pure . pure
  (MkExceptT g) <*> (MkExceptT x) = MkExceptT $ ((<*>) <$> g) <*> x

public export
Monad m => Monad (ExceptT e m) where
  (MkExceptT x) >>= f = MkExceptT $ x >>= either (pure . Left) (runExceptT . f)

public export
MonadTrans (ExceptT e) where
  lift = MkExceptT . map pure

public export
fail : Applicative f => e -> ExceptT e f a
fail = MkExceptT . pure . Left

public export
exceptFromMaybe : Monad m => Lazy e -> MaybeT m a -> ExceptT e m a
exceptFromMaybe x y = lift (runMaybeT y) >>= maybe (fail x) pure

