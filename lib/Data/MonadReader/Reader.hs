module Data.MonadReader.Reader where

data Reader r a = MkReader{readerComputation :: r -> a}

ask :: Reader r r
ask = MkReader id

asks :: (r -> a) -> Reader r a
asks f = MkReader f

local :: (r -> r) -> Reader r a -> Reader r a
local f (MkReader g) = MkReader (g . f)

runReader :: Reader r a -> r -> a
runReader (MkReader f) = f

instance Functor (Reader r) where
    fmap f (MkReader g) = MkReader (f . g)

instance Applicative (Reader r) where
    pure x = MkReader (const x)
    MkReader f <*> MkReader g = MkReader (\ x -> f x (g x))

instance Monad (Reader r) where
    MkReader f >>= g = MkReader (\ y -> runReader (g (f y)) y)

