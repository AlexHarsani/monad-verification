module Control.MonadReader.ReaderT where

import Control.MonadReader.MonadTrans

data ReaderT r m a = MkReaderT{readerTComputation :: r -> m a}

askT :: Monad m => ReaderT r m r
askT = MkReaderT return

asksT :: Monad m => (r -> a) -> ReaderT r m a
asksT f = MkReaderT (return . f)

localT :: Monad m => (r -> r) -> ReaderT r m a -> ReaderT r m a
localT f (MkReaderT g) = MkReaderT (g . f)

runReaderT :: Monad m => ReaderT r m a -> r -> m a
runReaderT (MkReaderT f) = f

instance (Monad m) => Functor (ReaderT r m) where
    fmap f (MkReaderT g) = MkReaderT $ fmap f . g

instance (Monad m) => Applicative (ReaderT r m) where
    pure x = MkReaderT (\ _ -> pure x)
    MkReaderT f <*> MkReaderT g = MkReaderT (\ x -> f x <*> g x)

instance (Monad m) => Monad (ReaderT r m) where
    m >>= k
      = MkReaderT (\ r -> runReaderT m r >>= \ a -> runReaderT (k a) r)

instance MonadTrans (ReaderT r) where
    lift m = MkReaderT (\ _ -> m)

