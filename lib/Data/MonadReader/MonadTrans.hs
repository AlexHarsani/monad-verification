module Data.MonadReader.MonadTrans where

class MonadTrans t where
    liftM :: Monad m => m a -> t m a

